%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:46 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  170 (2336 expanded)
%              Number of clauses        :  106 ( 800 expanded)
%              Number of leaves         :   15 ( 437 expanded)
%              Depth                    :   27
%              Number of atoms          :  522 (12050 expanded)
%              Number of equality atoms :  262 (2534 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & k2_relset_1(sK1,sK2,sK3) = sK2
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f45])).

fof(f80,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f46])).

fof(f60,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f43,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f18])).

fof(f62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1883,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_788,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_789,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_791,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_789,c_35])).

cnf(c_1875,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1879,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4235,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1875,c_1879])).

cnf(c_4303,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_791,c_4235])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1880,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2911,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_1880])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_362,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_363,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_365,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_37])).

cnf(c_1872,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_2925,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2911,c_1872])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1877,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5129,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2925,c_1877])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1878,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3370,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1875,c_1878])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3382,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3370,c_33])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_348,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_349,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_351,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_349,c_37])).

cnf(c_1873,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_2924,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2911,c_1873])).

cnf(c_3455,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3382,c_2924])).

cnf(c_5142,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5129,c_3455])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2193,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2194,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2193])).

cnf(c_2196,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2327,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2196])).

cnf(c_2328,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2327])).

cnf(c_5760,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5142,c_38,c_40,c_2194,c_2328])).

cnf(c_5766,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4303,c_5760])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_799,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k1_relat_1(X0) != sK2
    | k2_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_800,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_812,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_800,c_17])).

cnf(c_1861,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_817,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_2431,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1861,c_38,c_40,c_817,c_2194,c_2328])).

cnf(c_2432,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2431])).

cnf(c_2972,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2924,c_2432])).

cnf(c_3044,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2972,c_2925])).

cnf(c_3454,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3382,c_3044])).

cnf(c_3458,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3454])).

cnf(c_4344,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4303,c_3458])).

cnf(c_5944,plain,
    ( sK2 = k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5766,c_4344])).

cnf(c_5950,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1883,c_5944])).

cnf(c_5953,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5950,c_38,c_40,c_2328])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_818,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_819,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_818])).

cnf(c_831,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_819,c_17])).

cnf(c_1860,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_2973,plain,
    ( k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2924,c_1860])).

cnf(c_3112,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(sK3) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2973,c_38,c_40,c_2194,c_2328])).

cnf(c_3113,plain,
    ( k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3112])).

cnf(c_3116,plain,
    ( k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3113,c_2925])).

cnf(c_3452,plain,
    ( sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3382,c_3116])).

cnf(c_3469,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3452])).

cnf(c_5965,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5953,c_3469])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1886,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3479,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3382,c_1886])).

cnf(c_3495,plain,
    ( ~ v1_relat_1(sK3)
    | sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3479])).

cnf(c_3624,plain,
    ( sK3 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3479,c_35,c_2327,c_3495])).

cnf(c_3625,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3624])).

cnf(c_5973,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5953,c_3625])).

cnf(c_6032,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5973])).

cnf(c_6088,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5965,c_6032])).

cnf(c_8,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6091,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6088,c_8])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6092,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6091,c_5])).

cnf(c_16,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_84,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_85,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_92,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_94,plain,
    ( v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_5957,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5953,c_5760])).

cnf(c_6102,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) = iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5957,c_6032])).

cnf(c_6105,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6102,c_8])).

cnf(c_6106,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6105,c_5])).

cnf(c_6728,plain,
    ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6092,c_84,c_85,c_94,c_6106])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1887,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6733,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6728,c_1887])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:33:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.85/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/0.98  
% 2.85/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.85/0.98  
% 2.85/0.98  ------  iProver source info
% 2.85/0.98  
% 2.85/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.85/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.85/0.98  git: non_committed_changes: false
% 2.85/0.98  git: last_make_outside_of_git: false
% 2.85/0.98  
% 2.85/0.98  ------ 
% 2.85/0.98  
% 2.85/0.98  ------ Input Options
% 2.85/0.98  
% 2.85/0.98  --out_options                           all
% 2.85/0.98  --tptp_safe_out                         true
% 2.85/0.98  --problem_path                          ""
% 2.85/0.98  --include_path                          ""
% 2.85/0.98  --clausifier                            res/vclausify_rel
% 2.85/0.98  --clausifier_options                    --mode clausify
% 2.85/0.98  --stdin                                 false
% 2.85/0.98  --stats_out                             all
% 2.85/0.98  
% 2.85/0.98  ------ General Options
% 2.85/0.98  
% 2.85/0.98  --fof                                   false
% 2.85/0.98  --time_out_real                         305.
% 2.85/0.98  --time_out_virtual                      -1.
% 2.85/0.98  --symbol_type_check                     false
% 2.85/0.98  --clausify_out                          false
% 2.85/0.98  --sig_cnt_out                           false
% 2.85/0.98  --trig_cnt_out                          false
% 2.85/0.98  --trig_cnt_out_tolerance                1.
% 2.85/0.98  --trig_cnt_out_sk_spl                   false
% 2.85/0.98  --abstr_cl_out                          false
% 2.85/0.98  
% 2.85/0.98  ------ Global Options
% 2.85/0.98  
% 2.85/0.98  --schedule                              default
% 2.85/0.98  --add_important_lit                     false
% 2.85/0.98  --prop_solver_per_cl                    1000
% 2.85/0.98  --min_unsat_core                        false
% 2.85/0.98  --soft_assumptions                      false
% 2.85/0.98  --soft_lemma_size                       3
% 2.85/0.98  --prop_impl_unit_size                   0
% 2.85/0.98  --prop_impl_unit                        []
% 2.85/0.98  --share_sel_clauses                     true
% 2.85/0.98  --reset_solvers                         false
% 2.85/0.98  --bc_imp_inh                            [conj_cone]
% 2.85/0.98  --conj_cone_tolerance                   3.
% 2.85/0.98  --extra_neg_conj                        none
% 2.85/0.98  --large_theory_mode                     true
% 2.85/0.98  --prolific_symb_bound                   200
% 2.85/0.98  --lt_threshold                          2000
% 2.85/0.98  --clause_weak_htbl                      true
% 2.85/0.98  --gc_record_bc_elim                     false
% 2.85/0.98  
% 2.85/0.98  ------ Preprocessing Options
% 2.85/0.98  
% 2.85/0.98  --preprocessing_flag                    true
% 2.85/0.98  --time_out_prep_mult                    0.1
% 2.85/0.98  --splitting_mode                        input
% 2.85/0.98  --splitting_grd                         true
% 2.85/0.98  --splitting_cvd                         false
% 2.85/0.98  --splitting_cvd_svl                     false
% 2.85/0.98  --splitting_nvd                         32
% 2.85/0.98  --sub_typing                            true
% 2.85/0.98  --prep_gs_sim                           true
% 2.85/0.98  --prep_unflatten                        true
% 2.85/0.98  --prep_res_sim                          true
% 2.85/0.98  --prep_upred                            true
% 2.85/0.98  --prep_sem_filter                       exhaustive
% 2.85/0.98  --prep_sem_filter_out                   false
% 2.85/0.98  --pred_elim                             true
% 2.85/0.98  --res_sim_input                         true
% 2.85/0.98  --eq_ax_congr_red                       true
% 2.85/0.98  --pure_diseq_elim                       true
% 2.85/0.98  --brand_transform                       false
% 2.85/0.98  --non_eq_to_eq                          false
% 2.85/0.98  --prep_def_merge                        true
% 2.85/0.98  --prep_def_merge_prop_impl              false
% 2.85/0.98  --prep_def_merge_mbd                    true
% 2.85/0.98  --prep_def_merge_tr_red                 false
% 2.85/0.98  --prep_def_merge_tr_cl                  false
% 2.85/0.98  --smt_preprocessing                     true
% 2.85/0.98  --smt_ac_axioms                         fast
% 2.85/0.98  --preprocessed_out                      false
% 2.85/0.98  --preprocessed_stats                    false
% 2.85/0.98  
% 2.85/0.98  ------ Abstraction refinement Options
% 2.85/0.98  
% 2.85/0.98  --abstr_ref                             []
% 2.85/0.98  --abstr_ref_prep                        false
% 2.85/0.98  --abstr_ref_until_sat                   false
% 2.85/0.98  --abstr_ref_sig_restrict                funpre
% 2.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.98  --abstr_ref_under                       []
% 2.85/0.98  
% 2.85/0.98  ------ SAT Options
% 2.85/0.98  
% 2.85/0.98  --sat_mode                              false
% 2.85/0.98  --sat_fm_restart_options                ""
% 2.85/0.98  --sat_gr_def                            false
% 2.85/0.98  --sat_epr_types                         true
% 2.85/0.98  --sat_non_cyclic_types                  false
% 2.85/0.98  --sat_finite_models                     false
% 2.85/0.98  --sat_fm_lemmas                         false
% 2.85/0.98  --sat_fm_prep                           false
% 2.85/0.98  --sat_fm_uc_incr                        true
% 2.85/0.98  --sat_out_model                         small
% 2.85/0.98  --sat_out_clauses                       false
% 2.85/0.98  
% 2.85/0.98  ------ QBF Options
% 2.85/0.98  
% 2.85/0.98  --qbf_mode                              false
% 2.85/0.98  --qbf_elim_univ                         false
% 2.85/0.98  --qbf_dom_inst                          none
% 2.85/0.98  --qbf_dom_pre_inst                      false
% 2.85/0.98  --qbf_sk_in                             false
% 2.85/0.98  --qbf_pred_elim                         true
% 2.85/0.98  --qbf_split                             512
% 2.85/0.98  
% 2.85/0.98  ------ BMC1 Options
% 2.85/0.98  
% 2.85/0.98  --bmc1_incremental                      false
% 2.85/0.98  --bmc1_axioms                           reachable_all
% 2.85/0.98  --bmc1_min_bound                        0
% 2.85/0.98  --bmc1_max_bound                        -1
% 2.85/0.98  --bmc1_max_bound_default                -1
% 2.85/0.98  --bmc1_symbol_reachability              true
% 2.85/0.98  --bmc1_property_lemmas                  false
% 2.85/0.98  --bmc1_k_induction                      false
% 2.85/0.98  --bmc1_non_equiv_states                 false
% 2.85/0.98  --bmc1_deadlock                         false
% 2.85/0.98  --bmc1_ucm                              false
% 2.85/0.98  --bmc1_add_unsat_core                   none
% 2.85/0.98  --bmc1_unsat_core_children              false
% 2.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.98  --bmc1_out_stat                         full
% 2.85/0.98  --bmc1_ground_init                      false
% 2.85/0.98  --bmc1_pre_inst_next_state              false
% 2.85/0.98  --bmc1_pre_inst_state                   false
% 2.85/0.98  --bmc1_pre_inst_reach_state             false
% 2.85/0.98  --bmc1_out_unsat_core                   false
% 2.85/0.98  --bmc1_aig_witness_out                  false
% 2.85/0.98  --bmc1_verbose                          false
% 2.85/0.98  --bmc1_dump_clauses_tptp                false
% 2.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.98  --bmc1_dump_file                        -
% 2.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.98  --bmc1_ucm_extend_mode                  1
% 2.85/0.98  --bmc1_ucm_init_mode                    2
% 2.85/0.98  --bmc1_ucm_cone_mode                    none
% 2.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.98  --bmc1_ucm_relax_model                  4
% 2.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.98  --bmc1_ucm_layered_model                none
% 2.85/0.98  --bmc1_ucm_max_lemma_size               10
% 2.85/0.98  
% 2.85/0.98  ------ AIG Options
% 2.85/0.98  
% 2.85/0.98  --aig_mode                              false
% 2.85/0.98  
% 2.85/0.98  ------ Instantiation Options
% 2.85/0.98  
% 2.85/0.98  --instantiation_flag                    true
% 2.85/0.98  --inst_sos_flag                         false
% 2.85/0.98  --inst_sos_phase                        true
% 2.85/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.98  --inst_lit_sel_side                     num_symb
% 2.85/0.98  --inst_solver_per_active                1400
% 2.85/0.98  --inst_solver_calls_frac                1.
% 2.85/0.98  --inst_passive_queue_type               priority_queues
% 2.85/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.98  --inst_passive_queues_freq              [25;2]
% 2.85/0.98  --inst_dismatching                      true
% 2.85/0.98  --inst_eager_unprocessed_to_passive     true
% 2.85/0.98  --inst_prop_sim_given                   true
% 2.85/0.98  --inst_prop_sim_new                     false
% 2.85/0.98  --inst_subs_new                         false
% 2.85/0.98  --inst_eq_res_simp                      false
% 2.85/0.98  --inst_subs_given                       false
% 2.85/0.98  --inst_orphan_elimination               true
% 2.85/0.98  --inst_learning_loop_flag               true
% 2.85/0.98  --inst_learning_start                   3000
% 2.85/0.98  --inst_learning_factor                  2
% 2.85/0.98  --inst_start_prop_sim_after_learn       3
% 2.85/0.98  --inst_sel_renew                        solver
% 2.85/0.98  --inst_lit_activity_flag                true
% 2.85/0.98  --inst_restr_to_given                   false
% 2.85/0.98  --inst_activity_threshold               500
% 2.85/0.98  --inst_out_proof                        true
% 2.85/0.98  
% 2.85/0.98  ------ Resolution Options
% 2.85/0.98  
% 2.85/0.98  --resolution_flag                       true
% 2.85/0.98  --res_lit_sel                           adaptive
% 2.85/0.98  --res_lit_sel_side                      none
% 2.85/0.98  --res_ordering                          kbo
% 2.85/0.98  --res_to_prop_solver                    active
% 2.85/0.98  --res_prop_simpl_new                    false
% 2.85/0.98  --res_prop_simpl_given                  true
% 2.85/0.98  --res_passive_queue_type                priority_queues
% 2.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.98  --res_passive_queues_freq               [15;5]
% 2.85/0.98  --res_forward_subs                      full
% 2.85/0.98  --res_backward_subs                     full
% 2.85/0.98  --res_forward_subs_resolution           true
% 2.85/0.98  --res_backward_subs_resolution          true
% 2.85/0.98  --res_orphan_elimination                true
% 2.85/0.98  --res_time_limit                        2.
% 2.85/0.98  --res_out_proof                         true
% 2.85/0.98  
% 2.85/0.98  ------ Superposition Options
% 2.85/0.98  
% 2.85/0.98  --superposition_flag                    true
% 2.85/0.98  --sup_passive_queue_type                priority_queues
% 2.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.98  --demod_completeness_check              fast
% 2.85/0.98  --demod_use_ground                      true
% 2.85/0.98  --sup_to_prop_solver                    passive
% 2.85/0.98  --sup_prop_simpl_new                    true
% 2.85/0.98  --sup_prop_simpl_given                  true
% 2.85/0.98  --sup_fun_splitting                     false
% 2.85/0.98  --sup_smt_interval                      50000
% 2.85/0.98  
% 2.85/0.98  ------ Superposition Simplification Setup
% 2.85/0.98  
% 2.85/0.98  --sup_indices_passive                   []
% 2.85/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.98  --sup_full_bw                           [BwDemod]
% 2.85/0.98  --sup_immed_triv                        [TrivRules]
% 2.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.98  --sup_immed_bw_main                     []
% 2.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.98  
% 2.85/0.98  ------ Combination Options
% 2.85/0.98  
% 2.85/0.98  --comb_res_mult                         3
% 2.85/0.98  --comb_sup_mult                         2
% 2.85/0.98  --comb_inst_mult                        10
% 2.85/0.98  
% 2.85/0.98  ------ Debug Options
% 2.85/0.98  
% 2.85/0.98  --dbg_backtrace                         false
% 2.85/0.98  --dbg_dump_prop_clauses                 false
% 2.85/0.98  --dbg_dump_prop_clauses_file            -
% 2.85/0.98  --dbg_out_stat                          false
% 2.85/0.98  ------ Parsing...
% 2.85/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.85/0.98  
% 2.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.85/0.98  
% 2.85/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.85/0.98  
% 2.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.85/0.98  ------ Proving...
% 2.85/0.98  ------ Problem Properties 
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  clauses                                 39
% 2.85/0.98  conjectures                             3
% 2.85/0.98  EPR                                     5
% 2.85/0.98  Horn                                    32
% 2.85/0.98  unary                                   10
% 2.85/0.98  binary                                  8
% 2.85/0.98  lits                                    108
% 2.85/0.98  lits eq                                 45
% 2.85/0.98  fd_pure                                 0
% 2.85/0.98  fd_pseudo                               0
% 2.85/0.98  fd_cond                                 5
% 2.85/0.98  fd_pseudo_cond                          0
% 2.85/0.98  AC symbols                              0
% 2.85/0.98  
% 2.85/0.98  ------ Schedule dynamic 5 is on 
% 2.85/0.98  
% 2.85/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  ------ 
% 2.85/0.98  Current options:
% 2.85/0.98  ------ 
% 2.85/0.98  
% 2.85/0.98  ------ Input Options
% 2.85/0.98  
% 2.85/0.98  --out_options                           all
% 2.85/0.98  --tptp_safe_out                         true
% 2.85/0.98  --problem_path                          ""
% 2.85/0.98  --include_path                          ""
% 2.85/0.98  --clausifier                            res/vclausify_rel
% 2.85/0.98  --clausifier_options                    --mode clausify
% 2.85/0.98  --stdin                                 false
% 2.85/0.98  --stats_out                             all
% 2.85/0.98  
% 2.85/0.98  ------ General Options
% 2.85/0.98  
% 2.85/0.98  --fof                                   false
% 2.85/0.98  --time_out_real                         305.
% 2.85/0.98  --time_out_virtual                      -1.
% 2.85/0.98  --symbol_type_check                     false
% 2.85/0.98  --clausify_out                          false
% 2.85/0.98  --sig_cnt_out                           false
% 2.85/0.98  --trig_cnt_out                          false
% 2.85/0.98  --trig_cnt_out_tolerance                1.
% 2.85/0.98  --trig_cnt_out_sk_spl                   false
% 2.85/0.98  --abstr_cl_out                          false
% 2.85/0.98  
% 2.85/0.98  ------ Global Options
% 2.85/0.98  
% 2.85/0.98  --schedule                              default
% 2.85/0.98  --add_important_lit                     false
% 2.85/0.98  --prop_solver_per_cl                    1000
% 2.85/0.98  --min_unsat_core                        false
% 2.85/0.98  --soft_assumptions                      false
% 2.85/0.98  --soft_lemma_size                       3
% 2.85/0.98  --prop_impl_unit_size                   0
% 2.85/0.98  --prop_impl_unit                        []
% 2.85/0.98  --share_sel_clauses                     true
% 2.85/0.98  --reset_solvers                         false
% 2.85/0.98  --bc_imp_inh                            [conj_cone]
% 2.85/0.98  --conj_cone_tolerance                   3.
% 2.85/0.98  --extra_neg_conj                        none
% 2.85/0.98  --large_theory_mode                     true
% 2.85/0.98  --prolific_symb_bound                   200
% 2.85/0.98  --lt_threshold                          2000
% 2.85/0.98  --clause_weak_htbl                      true
% 2.85/0.98  --gc_record_bc_elim                     false
% 2.85/0.98  
% 2.85/0.98  ------ Preprocessing Options
% 2.85/0.98  
% 2.85/0.98  --preprocessing_flag                    true
% 2.85/0.98  --time_out_prep_mult                    0.1
% 2.85/0.98  --splitting_mode                        input
% 2.85/0.98  --splitting_grd                         true
% 2.85/0.98  --splitting_cvd                         false
% 2.85/0.98  --splitting_cvd_svl                     false
% 2.85/0.98  --splitting_nvd                         32
% 2.85/0.98  --sub_typing                            true
% 2.85/0.98  --prep_gs_sim                           true
% 2.85/0.98  --prep_unflatten                        true
% 2.85/0.98  --prep_res_sim                          true
% 2.85/0.98  --prep_upred                            true
% 2.85/0.98  --prep_sem_filter                       exhaustive
% 2.85/0.98  --prep_sem_filter_out                   false
% 2.85/0.98  --pred_elim                             true
% 2.85/0.98  --res_sim_input                         true
% 2.85/0.98  --eq_ax_congr_red                       true
% 2.85/0.98  --pure_diseq_elim                       true
% 2.85/0.98  --brand_transform                       false
% 2.85/0.98  --non_eq_to_eq                          false
% 2.85/0.98  --prep_def_merge                        true
% 2.85/0.98  --prep_def_merge_prop_impl              false
% 2.85/0.98  --prep_def_merge_mbd                    true
% 2.85/0.98  --prep_def_merge_tr_red                 false
% 2.85/0.98  --prep_def_merge_tr_cl                  false
% 2.85/0.98  --smt_preprocessing                     true
% 2.85/0.98  --smt_ac_axioms                         fast
% 2.85/0.98  --preprocessed_out                      false
% 2.85/0.98  --preprocessed_stats                    false
% 2.85/0.98  
% 2.85/0.98  ------ Abstraction refinement Options
% 2.85/0.98  
% 2.85/0.98  --abstr_ref                             []
% 2.85/0.98  --abstr_ref_prep                        false
% 2.85/0.98  --abstr_ref_until_sat                   false
% 2.85/0.98  --abstr_ref_sig_restrict                funpre
% 2.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.98  --abstr_ref_under                       []
% 2.85/0.98  
% 2.85/0.98  ------ SAT Options
% 2.85/0.98  
% 2.85/0.98  --sat_mode                              false
% 2.85/0.98  --sat_fm_restart_options                ""
% 2.85/0.98  --sat_gr_def                            false
% 2.85/0.98  --sat_epr_types                         true
% 2.85/0.98  --sat_non_cyclic_types                  false
% 2.85/0.98  --sat_finite_models                     false
% 2.85/0.98  --sat_fm_lemmas                         false
% 2.85/0.98  --sat_fm_prep                           false
% 2.85/0.98  --sat_fm_uc_incr                        true
% 2.85/0.98  --sat_out_model                         small
% 2.85/0.98  --sat_out_clauses                       false
% 2.85/0.98  
% 2.85/0.98  ------ QBF Options
% 2.85/0.98  
% 2.85/0.98  --qbf_mode                              false
% 2.85/0.98  --qbf_elim_univ                         false
% 2.85/0.98  --qbf_dom_inst                          none
% 2.85/0.98  --qbf_dom_pre_inst                      false
% 2.85/0.98  --qbf_sk_in                             false
% 2.85/0.98  --qbf_pred_elim                         true
% 2.85/0.98  --qbf_split                             512
% 2.85/0.98  
% 2.85/0.98  ------ BMC1 Options
% 2.85/0.98  
% 2.85/0.98  --bmc1_incremental                      false
% 2.85/0.98  --bmc1_axioms                           reachable_all
% 2.85/0.98  --bmc1_min_bound                        0
% 2.85/0.98  --bmc1_max_bound                        -1
% 2.85/0.98  --bmc1_max_bound_default                -1
% 2.85/0.98  --bmc1_symbol_reachability              true
% 2.85/0.98  --bmc1_property_lemmas                  false
% 2.85/0.98  --bmc1_k_induction                      false
% 2.85/0.98  --bmc1_non_equiv_states                 false
% 2.85/0.98  --bmc1_deadlock                         false
% 2.85/0.98  --bmc1_ucm                              false
% 2.85/0.98  --bmc1_add_unsat_core                   none
% 2.85/0.98  --bmc1_unsat_core_children              false
% 2.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.98  --bmc1_out_stat                         full
% 2.85/0.98  --bmc1_ground_init                      false
% 2.85/0.98  --bmc1_pre_inst_next_state              false
% 2.85/0.98  --bmc1_pre_inst_state                   false
% 2.85/0.98  --bmc1_pre_inst_reach_state             false
% 2.85/0.98  --bmc1_out_unsat_core                   false
% 2.85/0.98  --bmc1_aig_witness_out                  false
% 2.85/0.98  --bmc1_verbose                          false
% 2.85/0.98  --bmc1_dump_clauses_tptp                false
% 2.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.98  --bmc1_dump_file                        -
% 2.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.98  --bmc1_ucm_extend_mode                  1
% 2.85/0.98  --bmc1_ucm_init_mode                    2
% 2.85/0.98  --bmc1_ucm_cone_mode                    none
% 2.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.98  --bmc1_ucm_relax_model                  4
% 2.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.98  --bmc1_ucm_layered_model                none
% 2.85/0.98  --bmc1_ucm_max_lemma_size               10
% 2.85/0.98  
% 2.85/0.98  ------ AIG Options
% 2.85/0.98  
% 2.85/0.98  --aig_mode                              false
% 2.85/0.98  
% 2.85/0.98  ------ Instantiation Options
% 2.85/0.98  
% 2.85/0.98  --instantiation_flag                    true
% 2.85/0.98  --inst_sos_flag                         false
% 2.85/0.98  --inst_sos_phase                        true
% 2.85/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.98  --inst_lit_sel_side                     none
% 2.85/0.98  --inst_solver_per_active                1400
% 2.85/0.98  --inst_solver_calls_frac                1.
% 2.85/0.98  --inst_passive_queue_type               priority_queues
% 2.85/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.98  --inst_passive_queues_freq              [25;2]
% 2.85/0.98  --inst_dismatching                      true
% 2.85/0.98  --inst_eager_unprocessed_to_passive     true
% 2.85/0.98  --inst_prop_sim_given                   true
% 2.85/0.98  --inst_prop_sim_new                     false
% 2.85/0.98  --inst_subs_new                         false
% 2.85/0.98  --inst_eq_res_simp                      false
% 2.85/0.98  --inst_subs_given                       false
% 2.85/0.98  --inst_orphan_elimination               true
% 2.85/0.98  --inst_learning_loop_flag               true
% 2.85/0.98  --inst_learning_start                   3000
% 2.85/0.98  --inst_learning_factor                  2
% 2.85/0.98  --inst_start_prop_sim_after_learn       3
% 2.85/0.98  --inst_sel_renew                        solver
% 2.85/0.98  --inst_lit_activity_flag                true
% 2.85/0.98  --inst_restr_to_given                   false
% 2.85/0.98  --inst_activity_threshold               500
% 2.85/0.98  --inst_out_proof                        true
% 2.85/0.98  
% 2.85/0.98  ------ Resolution Options
% 2.85/0.98  
% 2.85/0.98  --resolution_flag                       false
% 2.85/0.98  --res_lit_sel                           adaptive
% 2.85/0.98  --res_lit_sel_side                      none
% 2.85/0.98  --res_ordering                          kbo
% 2.85/0.98  --res_to_prop_solver                    active
% 2.85/0.98  --res_prop_simpl_new                    false
% 2.85/0.98  --res_prop_simpl_given                  true
% 2.85/0.98  --res_passive_queue_type                priority_queues
% 2.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.98  --res_passive_queues_freq               [15;5]
% 2.85/0.98  --res_forward_subs                      full
% 2.85/0.98  --res_backward_subs                     full
% 2.85/0.98  --res_forward_subs_resolution           true
% 2.85/0.98  --res_backward_subs_resolution          true
% 2.85/0.98  --res_orphan_elimination                true
% 2.85/0.98  --res_time_limit                        2.
% 2.85/0.98  --res_out_proof                         true
% 2.85/0.98  
% 2.85/0.98  ------ Superposition Options
% 2.85/0.98  
% 2.85/0.98  --superposition_flag                    true
% 2.85/0.98  --sup_passive_queue_type                priority_queues
% 2.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.98  --demod_completeness_check              fast
% 2.85/0.98  --demod_use_ground                      true
% 2.85/0.98  --sup_to_prop_solver                    passive
% 2.85/0.98  --sup_prop_simpl_new                    true
% 2.85/0.98  --sup_prop_simpl_given                  true
% 2.85/0.98  --sup_fun_splitting                     false
% 2.85/0.98  --sup_smt_interval                      50000
% 2.85/0.98  
% 2.85/0.98  ------ Superposition Simplification Setup
% 2.85/0.98  
% 2.85/0.98  --sup_indices_passive                   []
% 2.85/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.98  --sup_full_bw                           [BwDemod]
% 2.85/0.98  --sup_immed_triv                        [TrivRules]
% 2.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.98  --sup_immed_bw_main                     []
% 2.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.98  
% 2.85/0.98  ------ Combination Options
% 2.85/0.98  
% 2.85/0.98  --comb_res_mult                         3
% 2.85/0.98  --comb_sup_mult                         2
% 2.85/0.98  --comb_inst_mult                        10
% 2.85/0.98  
% 2.85/0.98  ------ Debug Options
% 2.85/0.98  
% 2.85/0.98  --dbg_backtrace                         false
% 2.85/0.98  --dbg_dump_prop_clauses                 false
% 2.85/0.98  --dbg_dump_prop_clauses_file            -
% 2.85/0.98  --dbg_out_stat                          false
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  ------ Proving...
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  % SZS status Theorem for theBenchmark.p
% 2.85/0.98  
% 2.85/0.98   Resolution empty clause
% 2.85/0.98  
% 2.85/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.85/0.98  
% 2.85/0.98  fof(f6,axiom,(
% 2.85/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f22,plain,(
% 2.85/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/0.98    inference(ennf_transformation,[],[f6])).
% 2.85/0.98  
% 2.85/0.98  fof(f23,plain,(
% 2.85/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/0.98    inference(flattening,[],[f22])).
% 2.85/0.98  
% 2.85/0.98  fof(f58,plain,(
% 2.85/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f23])).
% 2.85/0.98  
% 2.85/0.98  fof(f12,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f29,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f12])).
% 2.85/0.98  
% 2.85/0.98  fof(f30,plain,(
% 2.85/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(flattening,[],[f29])).
% 2.85/0.98  
% 2.85/0.98  fof(f44,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(nnf_transformation,[],[f30])).
% 2.85/0.98  
% 2.85/0.98  fof(f67,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f44])).
% 2.85/0.98  
% 2.85/0.98  fof(f15,conjecture,(
% 2.85/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f16,negated_conjecture,(
% 2.85/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.85/0.98    inference(negated_conjecture,[],[f15])).
% 2.85/0.98  
% 2.85/0.98  fof(f35,plain,(
% 2.85/0.98    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.85/0.98    inference(ennf_transformation,[],[f16])).
% 2.85/0.98  
% 2.85/0.98  fof(f36,plain,(
% 2.85/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.85/0.98    inference(flattening,[],[f35])).
% 2.85/0.98  
% 2.85/0.98  fof(f45,plain,(
% 2.85/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.85/0.98    introduced(choice_axiom,[])).
% 2.85/0.98  
% 2.85/0.98  fof(f46,plain,(
% 2.85/0.98    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f45])).
% 2.85/0.98  
% 2.85/0.98  fof(f80,plain,(
% 2.85/0.98    v1_funct_2(sK3,sK1,sK2)),
% 2.85/0.98    inference(cnf_transformation,[],[f46])).
% 2.85/0.98  
% 2.85/0.98  fof(f81,plain,(
% 2.85/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.85/0.98    inference(cnf_transformation,[],[f46])).
% 2.85/0.98  
% 2.85/0.98  fof(f10,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f27,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f10])).
% 2.85/0.98  
% 2.85/0.98  fof(f65,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f27])).
% 2.85/0.98  
% 2.85/0.98  fof(f9,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f26,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f9])).
% 2.85/0.98  
% 2.85/0.98  fof(f64,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f26])).
% 2.85/0.98  
% 2.85/0.98  fof(f7,axiom,(
% 2.85/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f24,plain,(
% 2.85/0.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/0.98    inference(ennf_transformation,[],[f7])).
% 2.85/0.98  
% 2.85/0.98  fof(f25,plain,(
% 2.85/0.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/0.98    inference(flattening,[],[f24])).
% 2.85/0.98  
% 2.85/0.98  fof(f61,plain,(
% 2.85/0.98    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f25])).
% 2.85/0.98  
% 2.85/0.98  fof(f82,plain,(
% 2.85/0.98    v2_funct_1(sK3)),
% 2.85/0.98    inference(cnf_transformation,[],[f46])).
% 2.85/0.98  
% 2.85/0.98  fof(f79,plain,(
% 2.85/0.98    v1_funct_1(sK3)),
% 2.85/0.98    inference(cnf_transformation,[],[f46])).
% 2.85/0.98  
% 2.85/0.98  fof(f13,axiom,(
% 2.85/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f31,plain,(
% 2.85/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.85/0.98    inference(ennf_transformation,[],[f13])).
% 2.85/0.98  
% 2.85/0.98  fof(f32,plain,(
% 2.85/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.85/0.98    inference(flattening,[],[f31])).
% 2.85/0.98  
% 2.85/0.98  fof(f75,plain,(
% 2.85/0.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f32])).
% 2.85/0.98  
% 2.85/0.98  fof(f11,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f28,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f11])).
% 2.85/0.98  
% 2.85/0.98  fof(f66,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f28])).
% 2.85/0.98  
% 2.85/0.98  fof(f83,plain,(
% 2.85/0.98    k2_relset_1(sK1,sK2,sK3) = sK2),
% 2.85/0.98    inference(cnf_transformation,[],[f46])).
% 2.85/0.98  
% 2.85/0.98  fof(f60,plain,(
% 2.85/0.98    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f25])).
% 2.85/0.98  
% 2.85/0.98  fof(f59,plain,(
% 2.85/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f23])).
% 2.85/0.98  
% 2.85/0.98  fof(f74,plain,(
% 2.85/0.98    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f32])).
% 2.85/0.98  
% 2.85/0.98  fof(f84,plain,(
% 2.85/0.98    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 2.85/0.98    inference(cnf_transformation,[],[f46])).
% 2.85/0.98  
% 2.85/0.98  fof(f14,axiom,(
% 2.85/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f33,plain,(
% 2.85/0.98    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.85/0.98    inference(ennf_transformation,[],[f14])).
% 2.85/0.98  
% 2.85/0.98  fof(f34,plain,(
% 2.85/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.85/0.98    inference(flattening,[],[f33])).
% 2.85/0.98  
% 2.85/0.98  fof(f77,plain,(
% 2.85/0.98    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f34])).
% 2.85/0.98  
% 2.85/0.98  fof(f5,axiom,(
% 2.85/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f20,plain,(
% 2.85/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.85/0.98    inference(ennf_transformation,[],[f5])).
% 2.85/0.98  
% 2.85/0.98  fof(f21,plain,(
% 2.85/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.85/0.98    inference(flattening,[],[f20])).
% 2.85/0.98  
% 2.85/0.98  fof(f57,plain,(
% 2.85/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f21])).
% 2.85/0.98  
% 2.85/0.98  fof(f4,axiom,(
% 2.85/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f54,plain,(
% 2.85/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.85/0.98    inference(cnf_transformation,[],[f4])).
% 2.85/0.98  
% 2.85/0.98  fof(f3,axiom,(
% 2.85/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f41,plain,(
% 2.85/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.85/0.98    inference(nnf_transformation,[],[f3])).
% 2.85/0.98  
% 2.85/0.98  fof(f42,plain,(
% 2.85/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.85/0.98    inference(flattening,[],[f41])).
% 2.85/0.98  
% 2.85/0.98  fof(f52,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.85/0.98    inference(cnf_transformation,[],[f42])).
% 2.85/0.98  
% 2.85/0.98  fof(f86,plain,(
% 2.85/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.85/0.98    inference(equality_resolution,[],[f52])).
% 2.85/0.98  
% 2.85/0.98  fof(f8,axiom,(
% 2.85/0.98    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f17,plain,(
% 2.85/0.98    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 2.85/0.98    inference(pure_predicate_removal,[],[f8])).
% 2.85/0.98  
% 2.85/0.98  fof(f18,plain,(
% 2.85/0.98    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 2.85/0.98    inference(pure_predicate_removal,[],[f17])).
% 2.85/0.98  
% 2.85/0.98  fof(f43,plain,(
% 2.85/0.98    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 2.85/0.98    inference(rectify,[],[f18])).
% 2.85/0.98  
% 2.85/0.98  fof(f62,plain,(
% 2.85/0.98    v1_relat_1(k1_xboole_0)),
% 2.85/0.98    inference(cnf_transformation,[],[f43])).
% 2.85/0.98  
% 2.85/0.98  fof(f63,plain,(
% 2.85/0.98    v1_funct_1(k1_xboole_0)),
% 2.85/0.98    inference(cnf_transformation,[],[f43])).
% 2.85/0.98  
% 2.85/0.98  fof(f2,axiom,(
% 2.85/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f50,plain,(
% 2.85/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f2])).
% 2.85/0.98  
% 2.85/0.98  cnf(c_12,plain,
% 2.85/0.98      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.85/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1883,plain,
% 2.85/0.98      ( v1_funct_1(X0) != iProver_top
% 2.85/0.98      | v1_relat_1(X0) != iProver_top
% 2.85/0.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_25,plain,
% 2.85/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.85/0.98      | k1_xboole_0 = X2 ),
% 2.85/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_36,negated_conjecture,
% 2.85/0.98      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.85/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_788,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.85/0.98      | sK1 != X1
% 2.85/0.98      | sK2 != X2
% 2.85/0.98      | sK3 != X0
% 2.85/0.98      | k1_xboole_0 = X2 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_789,plain,
% 2.85/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.85/0.98      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.85/0.98      | k1_xboole_0 = sK2 ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_788]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_35,negated_conjecture,
% 2.85/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.85/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_791,plain,
% 2.85/0.98      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.85/0.98      inference(global_propositional_subsumption,[status(thm)],[c_789,c_35]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1875,plain,
% 2.85/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_18,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1879,plain,
% 2.85/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.85/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_4235,plain,
% 2.85/0.98      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_1875,c_1879]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_4303,plain,
% 2.85/0.98      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_791,c_4235]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_17,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1880,plain,
% 2.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.85/0.98      | v1_relat_1(X0) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2911,plain,
% 2.85/0.98      ( v1_relat_1(sK3) = iProver_top ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_1875,c_1880]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_13,plain,
% 2.85/0.98      ( ~ v2_funct_1(X0)
% 2.85/0.98      | ~ v1_funct_1(X0)
% 2.85/0.98      | ~ v1_relat_1(X0)
% 2.85/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_34,negated_conjecture,
% 2.85/0.98      ( v2_funct_1(sK3) ),
% 2.85/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_362,plain,
% 2.85/0.98      ( ~ v1_funct_1(X0)
% 2.85/0.98      | ~ v1_relat_1(X0)
% 2.85/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.85/0.98      | sK3 != X0 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_34]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_363,plain,
% 2.85/0.98      ( ~ v1_funct_1(sK3)
% 2.85/0.98      | ~ v1_relat_1(sK3)
% 2.85/0.98      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_362]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_37,negated_conjecture,
% 2.85/0.98      ( v1_funct_1(sK3) ),
% 2.85/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_365,plain,
% 2.85/0.98      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.85/0.98      inference(global_propositional_subsumption,[status(thm)],[c_363,c_37]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1872,plain,
% 2.85/0.98      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 2.85/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2925,plain,
% 2.85/0.98      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_2911,c_1872]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_26,plain,
% 2.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.85/0.98      | ~ v1_funct_1(X0)
% 2.85/0.98      | ~ v1_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1877,plain,
% 2.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.85/0.98      | v1_funct_1(X0) != iProver_top
% 2.85/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5129,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 2.85/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.85/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_2925,c_1877]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_19,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1878,plain,
% 2.85/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.85/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3370,plain,
% 2.85/0.98      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_1875,c_1878]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_33,negated_conjecture,
% 2.85/0.98      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 2.85/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3382,plain,
% 2.85/0.98      ( k2_relat_1(sK3) = sK2 ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_3370,c_33]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_14,plain,
% 2.85/0.98      ( ~ v2_funct_1(X0)
% 2.85/0.98      | ~ v1_funct_1(X0)
% 2.85/0.98      | ~ v1_relat_1(X0)
% 2.85/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_348,plain,
% 2.85/0.98      ( ~ v1_funct_1(X0)
% 2.85/0.98      | ~ v1_relat_1(X0)
% 2.85/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.85/0.98      | sK3 != X0 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_34]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_349,plain,
% 2.85/0.98      ( ~ v1_funct_1(sK3)
% 2.85/0.98      | ~ v1_relat_1(sK3)
% 2.85/0.98      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_348]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_351,plain,
% 2.85/0.98      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.85/0.98      inference(global_propositional_subsumption,[status(thm)],[c_349,c_37]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1873,plain,
% 2.85/0.98      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 2.85/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2924,plain,
% 2.85/0.98      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_2911,c_1873]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3455,plain,
% 2.85/0.98      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_3382,c_2924]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5142,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 2.85/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.85/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_5129,c_3455]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_38,plain,
% 2.85/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_40,plain,
% 2.85/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_11,plain,
% 2.85/0.98      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2193,plain,
% 2.85/0.98      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2194,plain,
% 2.85/0.98      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 2.85/0.98      | v1_funct_1(sK3) != iProver_top
% 2.85/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_2193]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2196,plain,
% 2.85/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK3) ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2327,plain,
% 2.85/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.85/0.98      | v1_relat_1(sK3) ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_2196]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2328,plain,
% 2.85/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.85/0.98      | v1_relat_1(sK3) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_2327]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5760,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 2.85/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.85/0.98      inference(global_propositional_subsumption,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_5142,c_38,c_40,c_2194,c_2328]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5766,plain,
% 2.85/0.98      ( sK2 = k1_xboole_0
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
% 2.85/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_4303,c_5760]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_27,plain,
% 2.85/0.98      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.85/0.98      | ~ v1_funct_1(X0)
% 2.85/0.98      | ~ v1_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_32,negated_conjecture,
% 2.85/0.98      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 2.85/0.98      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.85/0.98      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 2.85/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_799,plain,
% 2.85/0.98      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.85/0.98      | ~ v1_funct_1(X0)
% 2.85/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.85/0.98      | ~ v1_relat_1(X0)
% 2.85/0.98      | k2_funct_1(sK3) != X0
% 2.85/0.98      | k1_relat_1(X0) != sK2
% 2.85/0.98      | k2_relat_1(X0) != sK1 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_800,plain,
% 2.85/0.98      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.85/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.85/0.98      | ~ v1_relat_1(k2_funct_1(sK3))
% 2.85/0.98      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.85/0.98      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_799]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_812,plain,
% 2.85/0.98      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.85/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.85/0.98      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.85/0.98      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 2.85/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_800,c_17]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1861,plain,
% 2.85/0.98      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.85/0.98      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.85/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_817,plain,
% 2.85/0.98      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.85/0.98      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.85/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2431,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.85/0.98      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.85/0.98      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 2.85/0.98      inference(global_propositional_subsumption,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_1861,c_38,c_40,c_817,c_2194,c_2328]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2432,plain,
% 2.85/0.98      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.85/0.98      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.85/0.98      inference(renaming,[status(thm)],[c_2431]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2972,plain,
% 2.85/0.98      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 2.85/0.98      | k2_relat_1(sK3) != sK2
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_2924,c_2432]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3044,plain,
% 2.85/0.98      ( k1_relat_1(sK3) != sK1
% 2.85/0.98      | k2_relat_1(sK3) != sK2
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_2972,c_2925]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3454,plain,
% 2.85/0.98      ( k1_relat_1(sK3) != sK1
% 2.85/0.98      | sK2 != sK2
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_3382,c_3044]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3458,plain,
% 2.85/0.98      ( k1_relat_1(sK3) != sK1
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.85/0.98      inference(equality_resolution_simp,[status(thm)],[c_3454]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_4344,plain,
% 2.85/0.98      ( sK2 = k1_xboole_0
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_4303,c_3458]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5944,plain,
% 2.85/0.98      ( sK2 = k1_xboole_0 | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.85/0.98      inference(global_propositional_subsumption,[status(thm)],[c_5766,c_4344]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5950,plain,
% 2.85/0.98      ( sK2 = k1_xboole_0
% 2.85/0.98      | v1_funct_1(sK3) != iProver_top
% 2.85/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_1883,c_5944]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5953,plain,
% 2.85/0.98      ( sK2 = k1_xboole_0 ),
% 2.85/0.98      inference(global_propositional_subsumption,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_5950,c_38,c_40,c_2328]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_30,plain,
% 2.85/0.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.85/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.85/0.98      | ~ v1_funct_1(X0)
% 2.85/0.98      | ~ v1_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_818,plain,
% 2.85/0.98      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.85/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.85/0.98      | ~ v1_funct_1(X0)
% 2.85/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.85/0.98      | ~ v1_relat_1(X0)
% 2.85/0.98      | k2_funct_1(sK3) != X0
% 2.85/0.98      | k1_relat_1(X0) != sK2
% 2.85/0.98      | sK1 != X1 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_819,plain,
% 2.85/0.98      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.85/0.98      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 2.85/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.85/0.98      | ~ v1_relat_1(k2_funct_1(sK3))
% 2.85/0.98      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_818]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_831,plain,
% 2.85/0.98      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.85/0.98      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 2.85/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 2.85/0.98      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 2.85/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_819,c_17]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1860,plain,
% 2.85/0.98      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.85/0.98      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 2.85/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2973,plain,
% 2.85/0.98      ( k2_relat_1(sK3) != sK2
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.85/0.98      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 2.85/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_2924,c_1860]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3112,plain,
% 2.85/0.98      ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.85/0.98      | k2_relat_1(sK3) != sK2 ),
% 2.85/0.98      inference(global_propositional_subsumption,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_2973,c_38,c_40,c_2194,c_2328]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3113,plain,
% 2.85/0.98      ( k2_relat_1(sK3) != sK2
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.85/0.98      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top ),
% 2.85/0.98      inference(renaming,[status(thm)],[c_3112]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3116,plain,
% 2.85/0.98      ( k2_relat_1(sK3) != sK2
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.85/0.98      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_3113,c_2925]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3452,plain,
% 2.85/0.98      ( sK2 != sK2
% 2.85/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.85/0.98      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_3382,c_3116]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3469,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.85/0.98      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 2.85/0.98      inference(equality_resolution_simp,[status(thm)],[c_3452]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5965,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 2.85/0.98      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_5953,c_3469]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_9,plain,
% 2.85/0.98      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1886,plain,
% 2.85/0.98      ( k2_relat_1(X0) != k1_xboole_0
% 2.85/0.98      | k1_xboole_0 = X0
% 2.85/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3479,plain,
% 2.85/0.98      ( sK2 != k1_xboole_0
% 2.85/0.98      | sK3 = k1_xboole_0
% 2.85/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_3382,c_1886]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3495,plain,
% 2.85/0.98      ( ~ v1_relat_1(sK3) | sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.85/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3479]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3624,plain,
% 2.85/0.98      ( sK3 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.85/0.98      inference(global_propositional_subsumption,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_3479,c_35,c_2327,c_3495]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3625,plain,
% 2.85/0.98      ( sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.85/0.98      inference(renaming,[status(thm)],[c_3624]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5973,plain,
% 2.85/0.98      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_5953,c_3625]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_6032,plain,
% 2.85/0.98      ( sK3 = k1_xboole_0 ),
% 2.85/0.98      inference(equality_resolution_simp,[status(thm)],[c_5973]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_6088,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 2.85/0.98      | r1_tarski(k1_relat_1(k1_xboole_0),sK1) != iProver_top ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_5965,c_6032]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_8,plain,
% 2.85/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_6091,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 2.85/0.98      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_6088,c_8]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5,plain,
% 2.85/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_6092,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.85/0.98      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_6091,c_5]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_16,plain,
% 2.85/0.98      ( v1_relat_1(k1_xboole_0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_84,plain,
% 2.85/0.98      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_15,plain,
% 2.85/0.98      ( v1_funct_1(k1_xboole_0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_85,plain,
% 2.85/0.98      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_92,plain,
% 2.85/0.98      ( v1_funct_1(X0) != iProver_top
% 2.85/0.98      | v1_relat_1(X0) != iProver_top
% 2.85/0.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_94,plain,
% 2.85/0.98      ( v1_funct_1(k1_xboole_0) != iProver_top
% 2.85/0.98      | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 2.85/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_92]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5957,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top
% 2.85/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_5953,c_5760]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_6102,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) = iProver_top
% 2.85/0.98      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_5957,c_6032]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_6105,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 2.85/0.98      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 2.85/0.98      inference(light_normalisation,[status(thm)],[c_6102,c_8]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_6106,plain,
% 2.85/0.98      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.85/0.98      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_6105,c_5]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_6728,plain,
% 2.85/0.98      ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 2.85/0.98      inference(global_propositional_subsumption,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_6092,c_84,c_85,c_94,c_6106]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3,plain,
% 2.85/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1887,plain,
% 2.85/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_6733,plain,
% 2.85/0.98      ( $false ),
% 2.85/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_6728,c_1887]) ).
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.85/0.98  
% 2.85/0.98  ------                               Statistics
% 2.85/0.98  
% 2.85/0.98  ------ General
% 2.85/0.98  
% 2.85/0.98  abstr_ref_over_cycles:                  0
% 2.85/0.98  abstr_ref_under_cycles:                 0
% 2.85/0.98  gc_basic_clause_elim:                   0
% 2.85/0.98  forced_gc_time:                         0
% 2.85/0.98  parsing_time:                           0.009
% 2.85/0.98  unif_index_cands_time:                  0.
% 2.85/0.98  unif_index_add_time:                    0.
% 2.85/0.98  orderings_time:                         0.
% 2.85/0.98  out_proof_time:                         0.01
% 2.85/0.98  total_time:                             0.208
% 2.85/0.98  num_of_symbols:                         50
% 2.85/0.98  num_of_terms:                           5973
% 2.85/0.98  
% 2.85/0.98  ------ Preprocessing
% 2.85/0.98  
% 2.85/0.98  num_of_splits:                          0
% 2.85/0.98  num_of_split_atoms:                     0
% 2.85/0.98  num_of_reused_defs:                     0
% 2.85/0.98  num_eq_ax_congr_red:                    9
% 2.85/0.98  num_of_sem_filtered_clauses:            1
% 2.85/0.98  num_of_subtypes:                        0
% 2.85/0.98  monotx_restored_types:                  0
% 2.85/0.98  sat_num_of_epr_types:                   0
% 2.85/0.98  sat_num_of_non_cyclic_types:            0
% 2.85/0.98  sat_guarded_non_collapsed_types:        0
% 2.85/0.98  num_pure_diseq_elim:                    0
% 2.85/0.98  simp_replaced_by:                       0
% 2.85/0.98  res_preprocessed:                       143
% 2.85/0.98  prep_upred:                             0
% 2.85/0.98  prep_unflattend:                        100
% 2.85/0.98  smt_new_axioms:                         0
% 2.85/0.98  pred_elim_cands:                        7
% 2.85/0.98  pred_elim:                              2
% 2.85/0.98  pred_elim_cl:                           -3
% 2.85/0.98  pred_elim_cycles:                       4
% 2.85/0.98  merged_defs:                            0
% 2.85/0.98  merged_defs_ncl:                        0
% 2.85/0.98  bin_hyper_res:                          0
% 2.85/0.98  prep_cycles:                            3
% 2.85/0.98  pred_elim_time:                         0.019
% 2.85/0.98  splitting_time:                         0.
% 2.85/0.98  sem_filter_time:                        0.
% 2.85/0.98  monotx_time:                            0.
% 2.85/0.98  subtype_inf_time:                       0.
% 2.85/0.98  
% 2.85/0.98  ------ Problem properties
% 2.85/0.98  
% 2.85/0.98  clauses:                                39
% 2.85/0.98  conjectures:                            3
% 2.85/0.98  epr:                                    5
% 2.85/0.98  horn:                                   32
% 2.85/0.98  ground:                                 18
% 2.85/0.98  unary:                                  10
% 2.85/0.98  binary:                                 8
% 2.85/0.98  lits:                                   108
% 2.85/0.98  lits_eq:                                45
% 2.85/0.98  fd_pure:                                0
% 2.85/0.98  fd_pseudo:                              0
% 2.85/0.98  fd_cond:                                5
% 2.85/0.98  fd_pseudo_cond:                         0
% 2.85/0.98  ac_symbols:                             0
% 2.85/0.98  
% 2.85/0.98  ------ Propositional Solver
% 2.85/0.98  
% 2.85/0.98  prop_solver_calls:                      23
% 2.85/0.98  prop_fast_solver_calls:                 1308
% 2.85/0.98  smt_solver_calls:                       0
% 2.85/0.98  smt_fast_solver_calls:                  0
% 2.85/0.98  prop_num_of_clauses:                    2294
% 2.85/0.98  prop_preprocess_simplified:             6476
% 2.85/0.98  prop_fo_subsumed:                       54
% 2.85/0.98  prop_solver_time:                       0.
% 2.85/0.98  smt_solver_time:                        0.
% 2.85/0.98  smt_fast_solver_time:                   0.
% 2.85/0.98  prop_fast_solver_time:                  0.
% 2.85/0.98  prop_unsat_core_time:                   0.
% 2.85/0.98  
% 2.85/0.98  ------ QBF
% 2.85/0.98  
% 2.85/0.98  qbf_q_res:                              0
% 2.85/0.98  qbf_num_tautologies:                    0
% 2.85/0.98  qbf_prep_cycles:                        0
% 2.85/0.98  
% 2.85/0.98  ------ BMC1
% 2.85/0.98  
% 2.85/0.98  bmc1_current_bound:                     -1
% 2.85/0.98  bmc1_last_solved_bound:                 -1
% 2.85/0.98  bmc1_unsat_core_size:                   -1
% 2.85/0.98  bmc1_unsat_core_parents_size:           -1
% 2.85/0.98  bmc1_merge_next_fun:                    0
% 2.85/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.85/0.98  
% 2.85/0.98  ------ Instantiation
% 2.85/0.98  
% 2.85/0.98  inst_num_of_clauses:                    861
% 2.85/0.98  inst_num_in_passive:                    57
% 2.85/0.98  inst_num_in_active:                     388
% 2.85/0.98  inst_num_in_unprocessed:                416
% 2.85/0.98  inst_num_of_loops:                      470
% 2.85/0.98  inst_num_of_learning_restarts:          0
% 2.85/0.98  inst_num_moves_active_passive:          80
% 2.85/0.98  inst_lit_activity:                      0
% 2.85/0.98  inst_lit_activity_moves:                0
% 2.85/0.98  inst_num_tautologies:                   0
% 2.85/0.98  inst_num_prop_implied:                  0
% 2.85/0.98  inst_num_existing_simplified:           0
% 2.85/0.98  inst_num_eq_res_simplified:             0
% 2.85/0.98  inst_num_child_elim:                    0
% 2.85/0.98  inst_num_of_dismatching_blockings:      319
% 2.85/0.98  inst_num_of_non_proper_insts:           564
% 2.85/0.98  inst_num_of_duplicates:                 0
% 2.85/0.98  inst_inst_num_from_inst_to_res:         0
% 2.85/0.98  inst_dismatching_checking_time:         0.
% 2.85/0.98  
% 2.85/0.98  ------ Resolution
% 2.85/0.98  
% 2.85/0.98  res_num_of_clauses:                     0
% 2.85/0.98  res_num_in_passive:                     0
% 2.85/0.98  res_num_in_active:                      0
% 2.85/0.98  res_num_of_loops:                       146
% 2.85/0.98  res_forward_subset_subsumed:            27
% 2.85/0.98  res_backward_subset_subsumed:           2
% 2.85/0.98  res_forward_subsumed:                   1
% 2.85/0.98  res_backward_subsumed:                  0
% 2.85/0.98  res_forward_subsumption_resolution:     5
% 2.85/0.98  res_backward_subsumption_resolution:    0
% 2.85/0.98  res_clause_to_clause_subsumption:       297
% 2.85/0.98  res_orphan_elimination:                 0
% 2.85/0.98  res_tautology_del:                      64
% 2.85/0.98  res_num_eq_res_simplified:              0
% 2.85/0.98  res_num_sel_changes:                    0
% 2.85/0.98  res_moves_from_active_to_pass:          0
% 2.85/0.98  
% 2.85/0.98  ------ Superposition
% 2.85/0.98  
% 2.85/0.98  sup_time_total:                         0.
% 2.85/0.98  sup_time_generating:                    0.
% 2.85/0.98  sup_time_sim_full:                      0.
% 2.85/0.98  sup_time_sim_immed:                     0.
% 2.85/0.98  
% 2.85/0.98  sup_num_of_clauses:                     55
% 2.85/0.98  sup_num_in_active:                      40
% 2.85/0.98  sup_num_in_passive:                     15
% 2.85/0.98  sup_num_of_loops:                       92
% 2.85/0.98  sup_fw_superposition:                   44
% 2.85/0.98  sup_bw_superposition:                   51
% 2.85/0.98  sup_immediate_simplified:               85
% 2.85/0.98  sup_given_eliminated:                   0
% 2.85/0.98  comparisons_done:                       0
% 2.85/0.98  comparisons_avoided:                    8
% 2.85/0.98  
% 2.85/0.98  ------ Simplifications
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  sim_fw_subset_subsumed:                 11
% 2.85/0.98  sim_bw_subset_subsumed:                 13
% 2.85/0.98  sim_fw_subsumed:                        6
% 2.85/0.98  sim_bw_subsumed:                        4
% 2.85/0.98  sim_fw_subsumption_res:                 3
% 2.85/0.98  sim_bw_subsumption_res:                 0
% 2.85/0.98  sim_tautology_del:                      5
% 2.85/0.98  sim_eq_tautology_del:                   17
% 2.85/0.98  sim_eq_res_simp:                        6
% 2.85/0.98  sim_fw_demodulated:                     18
% 2.85/0.98  sim_bw_demodulated:                     53
% 2.85/0.98  sim_light_normalised:                   63
% 2.85/0.98  sim_joinable_taut:                      0
% 2.85/0.98  sim_joinable_simp:                      0
% 2.85/0.98  sim_ac_normalised:                      0
% 2.85/0.98  sim_smt_subsumption:                    0
% 2.85/0.98  
%------------------------------------------------------------------------------

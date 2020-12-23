%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:46 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  172 (3456 expanded)
%              Number of clauses        :  108 (1168 expanded)
%              Number of leaves         :   15 ( 649 expanded)
%              Depth                    :   27
%              Number of atoms          :  529 (18074 expanded)
%              Number of equality atoms :  269 (3910 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f30])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f46,plain,
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

fof(f47,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f46])).

fof(f83,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f47])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f44,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f19])).

fof(f65,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_992,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_993,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_992])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_995,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_993,c_37])).

cnf(c_2361,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2365,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4909,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2361,c_2365])).

cnf(c_5142,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_995,c_4909])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2366,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3531,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2361,c_2366])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_36,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_458,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_36])).

cnf(c_459,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_461,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_39])).

cnf(c_2358,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_3582,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3531,c_2358])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6063,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3582,c_2363])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2364,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4429,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2361,c_2364])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4446,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4429,c_35])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_444,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_445,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_447,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_39])).

cnf(c_2359,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_3581,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3531,c_2359])).

cnf(c_4461,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4446,c_3581])).

cnf(c_6076,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6063,c_4461])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2695,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2696,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2695])).

cnf(c_2709,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2851,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2709])).

cnf(c_2852,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2851])).

cnf(c_6566,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6076,c_40,c_42,c_2696,c_2852])).

cnf(c_6572,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5142,c_6566])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2369,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2372,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3975,plain,
    ( k2_funct_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3582,c_2372])).

cnf(c_5387,plain,
    ( k2_funct_1(sK3) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5142,c_3975])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_34,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1003,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k1_relat_1(X0) != sK2
    | k2_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_34])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(unflattening,[status(thm)],[c_1003])).

cnf(c_1016,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1004,c_19])).

cnf(c_2347,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_1021,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_2974,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2347,c_40,c_42,c_1021,c_2696,c_2852])).

cnf(c_2975,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2974])).

cnf(c_3588,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3581,c_2975])).

cnf(c_3670,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3588,c_3582])).

cnf(c_4460,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4446,c_3670])).

cnf(c_4464,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4460])).

cnf(c_5839,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5142,c_4464])).

cnf(c_6785,plain,
    ( sK2 = k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5387,c_5839,c_6572])).

cnf(c_6791,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2369,c_6785])).

cnf(c_7379,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6572,c_40,c_42,c_2852,c_6791])).

cnf(c_32,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1022,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_34])).

cnf(c_1023,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1022])).

cnf(c_1035,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1023,c_19])).

cnf(c_2346,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1035])).

cnf(c_3589,plain,
    ( k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3581,c_2346])).

cnf(c_4221,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(sK3) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3589,c_40,c_42,c_2696,c_2852])).

cnf(c_4222,plain,
    ( k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4221])).

cnf(c_4225,plain,
    ( k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4222,c_3582])).

cnf(c_4456,plain,
    ( sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4446,c_4225])).

cnf(c_4483,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4456])).

cnf(c_7394,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7379,c_4483])).

cnf(c_4494,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4446,c_2372])).

cnf(c_4510,plain,
    ( ~ v1_relat_1(sK3)
    | sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4494])).

cnf(c_5244,plain,
    ( sK3 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4494,c_37,c_2851,c_4510])).

cnf(c_5245,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5244])).

cnf(c_7401,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7379,c_5245])).

cnf(c_7466,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7401])).

cnf(c_7522,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7394,c_7466])).

cnf(c_10,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7525,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7522,c_10])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_7526,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7525,c_6])).

cnf(c_18,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_86,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_87,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_94,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_96,plain,
    ( v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_7389,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7379,c_6566])).

cnf(c_7536,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) = iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7389,c_7466])).

cnf(c_7539,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7536,c_10])).

cnf(c_7540,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7539,c_6])).

cnf(c_8948,plain,
    ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7526,c_86,c_87,c_96,c_7540])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2378,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8953,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8948,c_2378])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:34:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.44/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/1.00  
% 3.44/1.00  ------  iProver source info
% 3.44/1.00  
% 3.44/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.44/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/1.00  git: non_committed_changes: false
% 3.44/1.00  git: last_make_outside_of_git: false
% 3.44/1.00  
% 3.44/1.00  ------ 
% 3.44/1.00  
% 3.44/1.00  ------ Input Options
% 3.44/1.00  
% 3.44/1.00  --out_options                           all
% 3.44/1.00  --tptp_safe_out                         true
% 3.44/1.00  --problem_path                          ""
% 3.44/1.00  --include_path                          ""
% 3.44/1.00  --clausifier                            res/vclausify_rel
% 3.44/1.00  --clausifier_options                    --mode clausify
% 3.44/1.00  --stdin                                 false
% 3.44/1.00  --stats_out                             all
% 3.44/1.00  
% 3.44/1.00  ------ General Options
% 3.44/1.00  
% 3.44/1.00  --fof                                   false
% 3.44/1.00  --time_out_real                         305.
% 3.44/1.00  --time_out_virtual                      -1.
% 3.44/1.00  --symbol_type_check                     false
% 3.44/1.00  --clausify_out                          false
% 3.44/1.00  --sig_cnt_out                           false
% 3.44/1.00  --trig_cnt_out                          false
% 3.44/1.00  --trig_cnt_out_tolerance                1.
% 3.44/1.00  --trig_cnt_out_sk_spl                   false
% 3.44/1.00  --abstr_cl_out                          false
% 3.44/1.00  
% 3.44/1.00  ------ Global Options
% 3.44/1.00  
% 3.44/1.00  --schedule                              default
% 3.44/1.00  --add_important_lit                     false
% 3.44/1.00  --prop_solver_per_cl                    1000
% 3.44/1.00  --min_unsat_core                        false
% 3.44/1.00  --soft_assumptions                      false
% 3.44/1.00  --soft_lemma_size                       3
% 3.44/1.00  --prop_impl_unit_size                   0
% 3.44/1.00  --prop_impl_unit                        []
% 3.44/1.00  --share_sel_clauses                     true
% 3.44/1.00  --reset_solvers                         false
% 3.44/1.00  --bc_imp_inh                            [conj_cone]
% 3.44/1.00  --conj_cone_tolerance                   3.
% 3.44/1.00  --extra_neg_conj                        none
% 3.44/1.00  --large_theory_mode                     true
% 3.44/1.00  --prolific_symb_bound                   200
% 3.44/1.00  --lt_threshold                          2000
% 3.44/1.00  --clause_weak_htbl                      true
% 3.44/1.00  --gc_record_bc_elim                     false
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing Options
% 3.44/1.00  
% 3.44/1.00  --preprocessing_flag                    true
% 3.44/1.00  --time_out_prep_mult                    0.1
% 3.44/1.00  --splitting_mode                        input
% 3.44/1.00  --splitting_grd                         true
% 3.44/1.00  --splitting_cvd                         false
% 3.44/1.00  --splitting_cvd_svl                     false
% 3.44/1.00  --splitting_nvd                         32
% 3.44/1.00  --sub_typing                            true
% 3.44/1.00  --prep_gs_sim                           true
% 3.44/1.00  --prep_unflatten                        true
% 3.44/1.00  --prep_res_sim                          true
% 3.44/1.00  --prep_upred                            true
% 3.44/1.00  --prep_sem_filter                       exhaustive
% 3.44/1.00  --prep_sem_filter_out                   false
% 3.44/1.00  --pred_elim                             true
% 3.44/1.00  --res_sim_input                         true
% 3.44/1.00  --eq_ax_congr_red                       true
% 3.44/1.00  --pure_diseq_elim                       true
% 3.44/1.00  --brand_transform                       false
% 3.44/1.00  --non_eq_to_eq                          false
% 3.44/1.00  --prep_def_merge                        true
% 3.44/1.00  --prep_def_merge_prop_impl              false
% 3.44/1.00  --prep_def_merge_mbd                    true
% 3.44/1.00  --prep_def_merge_tr_red                 false
% 3.44/1.00  --prep_def_merge_tr_cl                  false
% 3.44/1.00  --smt_preprocessing                     true
% 3.44/1.00  --smt_ac_axioms                         fast
% 3.44/1.00  --preprocessed_out                      false
% 3.44/1.00  --preprocessed_stats                    false
% 3.44/1.00  
% 3.44/1.00  ------ Abstraction refinement Options
% 3.44/1.00  
% 3.44/1.00  --abstr_ref                             []
% 3.44/1.00  --abstr_ref_prep                        false
% 3.44/1.00  --abstr_ref_until_sat                   false
% 3.44/1.00  --abstr_ref_sig_restrict                funpre
% 3.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/1.00  --abstr_ref_under                       []
% 3.44/1.00  
% 3.44/1.00  ------ SAT Options
% 3.44/1.00  
% 3.44/1.00  --sat_mode                              false
% 3.44/1.00  --sat_fm_restart_options                ""
% 3.44/1.00  --sat_gr_def                            false
% 3.44/1.00  --sat_epr_types                         true
% 3.44/1.00  --sat_non_cyclic_types                  false
% 3.44/1.00  --sat_finite_models                     false
% 3.44/1.00  --sat_fm_lemmas                         false
% 3.44/1.00  --sat_fm_prep                           false
% 3.44/1.00  --sat_fm_uc_incr                        true
% 3.44/1.00  --sat_out_model                         small
% 3.44/1.00  --sat_out_clauses                       false
% 3.44/1.00  
% 3.44/1.00  ------ QBF Options
% 3.44/1.00  
% 3.44/1.00  --qbf_mode                              false
% 3.44/1.00  --qbf_elim_univ                         false
% 3.44/1.00  --qbf_dom_inst                          none
% 3.44/1.00  --qbf_dom_pre_inst                      false
% 3.44/1.00  --qbf_sk_in                             false
% 3.44/1.00  --qbf_pred_elim                         true
% 3.44/1.00  --qbf_split                             512
% 3.44/1.00  
% 3.44/1.00  ------ BMC1 Options
% 3.44/1.00  
% 3.44/1.00  --bmc1_incremental                      false
% 3.44/1.00  --bmc1_axioms                           reachable_all
% 3.44/1.00  --bmc1_min_bound                        0
% 3.44/1.00  --bmc1_max_bound                        -1
% 3.44/1.00  --bmc1_max_bound_default                -1
% 3.44/1.00  --bmc1_symbol_reachability              true
% 3.44/1.00  --bmc1_property_lemmas                  false
% 3.44/1.00  --bmc1_k_induction                      false
% 3.44/1.00  --bmc1_non_equiv_states                 false
% 3.44/1.00  --bmc1_deadlock                         false
% 3.44/1.00  --bmc1_ucm                              false
% 3.44/1.00  --bmc1_add_unsat_core                   none
% 3.44/1.00  --bmc1_unsat_core_children              false
% 3.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/1.00  --bmc1_out_stat                         full
% 3.44/1.00  --bmc1_ground_init                      false
% 3.44/1.00  --bmc1_pre_inst_next_state              false
% 3.44/1.00  --bmc1_pre_inst_state                   false
% 3.44/1.00  --bmc1_pre_inst_reach_state             false
% 3.44/1.00  --bmc1_out_unsat_core                   false
% 3.44/1.00  --bmc1_aig_witness_out                  false
% 3.44/1.00  --bmc1_verbose                          false
% 3.44/1.00  --bmc1_dump_clauses_tptp                false
% 3.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.44/1.00  --bmc1_dump_file                        -
% 3.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.44/1.00  --bmc1_ucm_extend_mode                  1
% 3.44/1.00  --bmc1_ucm_init_mode                    2
% 3.44/1.00  --bmc1_ucm_cone_mode                    none
% 3.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.44/1.00  --bmc1_ucm_relax_model                  4
% 3.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/1.00  --bmc1_ucm_layered_model                none
% 3.44/1.00  --bmc1_ucm_max_lemma_size               10
% 3.44/1.00  
% 3.44/1.00  ------ AIG Options
% 3.44/1.00  
% 3.44/1.00  --aig_mode                              false
% 3.44/1.00  
% 3.44/1.00  ------ Instantiation Options
% 3.44/1.00  
% 3.44/1.00  --instantiation_flag                    true
% 3.44/1.00  --inst_sos_flag                         false
% 3.44/1.00  --inst_sos_phase                        true
% 3.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/1.00  --inst_lit_sel_side                     num_symb
% 3.44/1.00  --inst_solver_per_active                1400
% 3.44/1.00  --inst_solver_calls_frac                1.
% 3.44/1.00  --inst_passive_queue_type               priority_queues
% 3.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/1.00  --inst_passive_queues_freq              [25;2]
% 3.44/1.00  --inst_dismatching                      true
% 3.44/1.00  --inst_eager_unprocessed_to_passive     true
% 3.44/1.00  --inst_prop_sim_given                   true
% 3.44/1.00  --inst_prop_sim_new                     false
% 3.44/1.00  --inst_subs_new                         false
% 3.44/1.00  --inst_eq_res_simp                      false
% 3.44/1.00  --inst_subs_given                       false
% 3.44/1.00  --inst_orphan_elimination               true
% 3.44/1.00  --inst_learning_loop_flag               true
% 3.44/1.00  --inst_learning_start                   3000
% 3.44/1.00  --inst_learning_factor                  2
% 3.44/1.00  --inst_start_prop_sim_after_learn       3
% 3.44/1.00  --inst_sel_renew                        solver
% 3.44/1.00  --inst_lit_activity_flag                true
% 3.44/1.00  --inst_restr_to_given                   false
% 3.44/1.00  --inst_activity_threshold               500
% 3.44/1.00  --inst_out_proof                        true
% 3.44/1.00  
% 3.44/1.00  ------ Resolution Options
% 3.44/1.00  
% 3.44/1.00  --resolution_flag                       true
% 3.44/1.00  --res_lit_sel                           adaptive
% 3.44/1.00  --res_lit_sel_side                      none
% 3.44/1.00  --res_ordering                          kbo
% 3.44/1.00  --res_to_prop_solver                    active
% 3.44/1.00  --res_prop_simpl_new                    false
% 3.44/1.00  --res_prop_simpl_given                  true
% 3.44/1.00  --res_passive_queue_type                priority_queues
% 3.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/1.00  --res_passive_queues_freq               [15;5]
% 3.44/1.00  --res_forward_subs                      full
% 3.44/1.00  --res_backward_subs                     full
% 3.44/1.00  --res_forward_subs_resolution           true
% 3.44/1.00  --res_backward_subs_resolution          true
% 3.44/1.00  --res_orphan_elimination                true
% 3.44/1.00  --res_time_limit                        2.
% 3.44/1.00  --res_out_proof                         true
% 3.44/1.00  
% 3.44/1.00  ------ Superposition Options
% 3.44/1.00  
% 3.44/1.00  --superposition_flag                    true
% 3.44/1.00  --sup_passive_queue_type                priority_queues
% 3.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.44/1.00  --demod_completeness_check              fast
% 3.44/1.00  --demod_use_ground                      true
% 3.44/1.00  --sup_to_prop_solver                    passive
% 3.44/1.00  --sup_prop_simpl_new                    true
% 3.44/1.00  --sup_prop_simpl_given                  true
% 3.44/1.00  --sup_fun_splitting                     false
% 3.44/1.00  --sup_smt_interval                      50000
% 3.44/1.00  
% 3.44/1.00  ------ Superposition Simplification Setup
% 3.44/1.00  
% 3.44/1.00  --sup_indices_passive                   []
% 3.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.00  --sup_full_bw                           [BwDemod]
% 3.44/1.00  --sup_immed_triv                        [TrivRules]
% 3.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.00  --sup_immed_bw_main                     []
% 3.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/1.00  
% 3.44/1.00  ------ Combination Options
% 3.44/1.00  
% 3.44/1.00  --comb_res_mult                         3
% 3.44/1.00  --comb_sup_mult                         2
% 3.44/1.00  --comb_inst_mult                        10
% 3.44/1.00  
% 3.44/1.00  ------ Debug Options
% 3.44/1.00  
% 3.44/1.00  --dbg_backtrace                         false
% 3.44/1.00  --dbg_dump_prop_clauses                 false
% 3.44/1.00  --dbg_dump_prop_clauses_file            -
% 3.44/1.00  --dbg_out_stat                          false
% 3.44/1.00  ------ Parsing...
% 3.44/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/1.00  ------ Proving...
% 3.44/1.00  ------ Problem Properties 
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  clauses                                 41
% 3.44/1.00  conjectures                             3
% 3.44/1.00  EPR                                     5
% 3.44/1.00  Horn                                    34
% 3.44/1.00  unary                                   10
% 3.44/1.00  binary                                  9
% 3.44/1.00  lits                                    113
% 3.44/1.00  lits eq                                 47
% 3.44/1.00  fd_pure                                 0
% 3.44/1.00  fd_pseudo                               0
% 3.44/1.00  fd_cond                                 5
% 3.44/1.00  fd_pseudo_cond                          2
% 3.44/1.00  AC symbols                              0
% 3.44/1.00  
% 3.44/1.00  ------ Schedule dynamic 5 is on 
% 3.44/1.00  
% 3.44/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  ------ 
% 3.44/1.00  Current options:
% 3.44/1.00  ------ 
% 3.44/1.00  
% 3.44/1.00  ------ Input Options
% 3.44/1.00  
% 3.44/1.00  --out_options                           all
% 3.44/1.00  --tptp_safe_out                         true
% 3.44/1.00  --problem_path                          ""
% 3.44/1.00  --include_path                          ""
% 3.44/1.00  --clausifier                            res/vclausify_rel
% 3.44/1.00  --clausifier_options                    --mode clausify
% 3.44/1.00  --stdin                                 false
% 3.44/1.00  --stats_out                             all
% 3.44/1.00  
% 3.44/1.00  ------ General Options
% 3.44/1.00  
% 3.44/1.00  --fof                                   false
% 3.44/1.00  --time_out_real                         305.
% 3.44/1.00  --time_out_virtual                      -1.
% 3.44/1.00  --symbol_type_check                     false
% 3.44/1.00  --clausify_out                          false
% 3.44/1.00  --sig_cnt_out                           false
% 3.44/1.00  --trig_cnt_out                          false
% 3.44/1.00  --trig_cnt_out_tolerance                1.
% 3.44/1.00  --trig_cnt_out_sk_spl                   false
% 3.44/1.00  --abstr_cl_out                          false
% 3.44/1.00  
% 3.44/1.00  ------ Global Options
% 3.44/1.00  
% 3.44/1.00  --schedule                              default
% 3.44/1.00  --add_important_lit                     false
% 3.44/1.00  --prop_solver_per_cl                    1000
% 3.44/1.00  --min_unsat_core                        false
% 3.44/1.00  --soft_assumptions                      false
% 3.44/1.00  --soft_lemma_size                       3
% 3.44/1.00  --prop_impl_unit_size                   0
% 3.44/1.00  --prop_impl_unit                        []
% 3.44/1.00  --share_sel_clauses                     true
% 3.44/1.00  --reset_solvers                         false
% 3.44/1.00  --bc_imp_inh                            [conj_cone]
% 3.44/1.00  --conj_cone_tolerance                   3.
% 3.44/1.00  --extra_neg_conj                        none
% 3.44/1.00  --large_theory_mode                     true
% 3.44/1.00  --prolific_symb_bound                   200
% 3.44/1.00  --lt_threshold                          2000
% 3.44/1.00  --clause_weak_htbl                      true
% 3.44/1.00  --gc_record_bc_elim                     false
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing Options
% 3.44/1.00  
% 3.44/1.00  --preprocessing_flag                    true
% 3.44/1.00  --time_out_prep_mult                    0.1
% 3.44/1.00  --splitting_mode                        input
% 3.44/1.00  --splitting_grd                         true
% 3.44/1.00  --splitting_cvd                         false
% 3.44/1.00  --splitting_cvd_svl                     false
% 3.44/1.00  --splitting_nvd                         32
% 3.44/1.00  --sub_typing                            true
% 3.44/1.00  --prep_gs_sim                           true
% 3.44/1.00  --prep_unflatten                        true
% 3.44/1.00  --prep_res_sim                          true
% 3.44/1.00  --prep_upred                            true
% 3.44/1.00  --prep_sem_filter                       exhaustive
% 3.44/1.00  --prep_sem_filter_out                   false
% 3.44/1.00  --pred_elim                             true
% 3.44/1.00  --res_sim_input                         true
% 3.44/1.00  --eq_ax_congr_red                       true
% 3.44/1.00  --pure_diseq_elim                       true
% 3.44/1.00  --brand_transform                       false
% 3.44/1.00  --non_eq_to_eq                          false
% 3.44/1.00  --prep_def_merge                        true
% 3.44/1.00  --prep_def_merge_prop_impl              false
% 3.44/1.00  --prep_def_merge_mbd                    true
% 3.44/1.00  --prep_def_merge_tr_red                 false
% 3.44/1.00  --prep_def_merge_tr_cl                  false
% 3.44/1.00  --smt_preprocessing                     true
% 3.44/1.00  --smt_ac_axioms                         fast
% 3.44/1.00  --preprocessed_out                      false
% 3.44/1.00  --preprocessed_stats                    false
% 3.44/1.00  
% 3.44/1.00  ------ Abstraction refinement Options
% 3.44/1.00  
% 3.44/1.00  --abstr_ref                             []
% 3.44/1.00  --abstr_ref_prep                        false
% 3.44/1.00  --abstr_ref_until_sat                   false
% 3.44/1.00  --abstr_ref_sig_restrict                funpre
% 3.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/1.00  --abstr_ref_under                       []
% 3.44/1.00  
% 3.44/1.00  ------ SAT Options
% 3.44/1.00  
% 3.44/1.00  --sat_mode                              false
% 3.44/1.00  --sat_fm_restart_options                ""
% 3.44/1.00  --sat_gr_def                            false
% 3.44/1.00  --sat_epr_types                         true
% 3.44/1.00  --sat_non_cyclic_types                  false
% 3.44/1.00  --sat_finite_models                     false
% 3.44/1.00  --sat_fm_lemmas                         false
% 3.44/1.00  --sat_fm_prep                           false
% 3.44/1.00  --sat_fm_uc_incr                        true
% 3.44/1.00  --sat_out_model                         small
% 3.44/1.00  --sat_out_clauses                       false
% 3.44/1.00  
% 3.44/1.00  ------ QBF Options
% 3.44/1.00  
% 3.44/1.00  --qbf_mode                              false
% 3.44/1.00  --qbf_elim_univ                         false
% 3.44/1.00  --qbf_dom_inst                          none
% 3.44/1.00  --qbf_dom_pre_inst                      false
% 3.44/1.00  --qbf_sk_in                             false
% 3.44/1.00  --qbf_pred_elim                         true
% 3.44/1.00  --qbf_split                             512
% 3.44/1.00  
% 3.44/1.00  ------ BMC1 Options
% 3.44/1.00  
% 3.44/1.00  --bmc1_incremental                      false
% 3.44/1.00  --bmc1_axioms                           reachable_all
% 3.44/1.00  --bmc1_min_bound                        0
% 3.44/1.00  --bmc1_max_bound                        -1
% 3.44/1.00  --bmc1_max_bound_default                -1
% 3.44/1.00  --bmc1_symbol_reachability              true
% 3.44/1.00  --bmc1_property_lemmas                  false
% 3.44/1.00  --bmc1_k_induction                      false
% 3.44/1.00  --bmc1_non_equiv_states                 false
% 3.44/1.00  --bmc1_deadlock                         false
% 3.44/1.00  --bmc1_ucm                              false
% 3.44/1.00  --bmc1_add_unsat_core                   none
% 3.44/1.00  --bmc1_unsat_core_children              false
% 3.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/1.00  --bmc1_out_stat                         full
% 3.44/1.00  --bmc1_ground_init                      false
% 3.44/1.00  --bmc1_pre_inst_next_state              false
% 3.44/1.00  --bmc1_pre_inst_state                   false
% 3.44/1.00  --bmc1_pre_inst_reach_state             false
% 3.44/1.00  --bmc1_out_unsat_core                   false
% 3.44/1.00  --bmc1_aig_witness_out                  false
% 3.44/1.00  --bmc1_verbose                          false
% 3.44/1.00  --bmc1_dump_clauses_tptp                false
% 3.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.44/1.00  --bmc1_dump_file                        -
% 3.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.44/1.00  --bmc1_ucm_extend_mode                  1
% 3.44/1.00  --bmc1_ucm_init_mode                    2
% 3.44/1.00  --bmc1_ucm_cone_mode                    none
% 3.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.44/1.00  --bmc1_ucm_relax_model                  4
% 3.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/1.00  --bmc1_ucm_layered_model                none
% 3.44/1.00  --bmc1_ucm_max_lemma_size               10
% 3.44/1.00  
% 3.44/1.00  ------ AIG Options
% 3.44/1.00  
% 3.44/1.00  --aig_mode                              false
% 3.44/1.00  
% 3.44/1.00  ------ Instantiation Options
% 3.44/1.00  
% 3.44/1.00  --instantiation_flag                    true
% 3.44/1.00  --inst_sos_flag                         false
% 3.44/1.00  --inst_sos_phase                        true
% 3.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/1.00  --inst_lit_sel_side                     none
% 3.44/1.00  --inst_solver_per_active                1400
% 3.44/1.00  --inst_solver_calls_frac                1.
% 3.44/1.00  --inst_passive_queue_type               priority_queues
% 3.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/1.00  --inst_passive_queues_freq              [25;2]
% 3.44/1.00  --inst_dismatching                      true
% 3.44/1.00  --inst_eager_unprocessed_to_passive     true
% 3.44/1.00  --inst_prop_sim_given                   true
% 3.44/1.00  --inst_prop_sim_new                     false
% 3.44/1.00  --inst_subs_new                         false
% 3.44/1.00  --inst_eq_res_simp                      false
% 3.44/1.00  --inst_subs_given                       false
% 3.44/1.00  --inst_orphan_elimination               true
% 3.44/1.00  --inst_learning_loop_flag               true
% 3.44/1.00  --inst_learning_start                   3000
% 3.44/1.00  --inst_learning_factor                  2
% 3.44/1.00  --inst_start_prop_sim_after_learn       3
% 3.44/1.00  --inst_sel_renew                        solver
% 3.44/1.00  --inst_lit_activity_flag                true
% 3.44/1.00  --inst_restr_to_given                   false
% 3.44/1.00  --inst_activity_threshold               500
% 3.44/1.00  --inst_out_proof                        true
% 3.44/1.00  
% 3.44/1.00  ------ Resolution Options
% 3.44/1.00  
% 3.44/1.00  --resolution_flag                       false
% 3.44/1.00  --res_lit_sel                           adaptive
% 3.44/1.00  --res_lit_sel_side                      none
% 3.44/1.00  --res_ordering                          kbo
% 3.44/1.00  --res_to_prop_solver                    active
% 3.44/1.00  --res_prop_simpl_new                    false
% 3.44/1.00  --res_prop_simpl_given                  true
% 3.44/1.00  --res_passive_queue_type                priority_queues
% 3.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/1.00  --res_passive_queues_freq               [15;5]
% 3.44/1.00  --res_forward_subs                      full
% 3.44/1.00  --res_backward_subs                     full
% 3.44/1.00  --res_forward_subs_resolution           true
% 3.44/1.00  --res_backward_subs_resolution          true
% 3.44/1.00  --res_orphan_elimination                true
% 3.44/1.00  --res_time_limit                        2.
% 3.44/1.00  --res_out_proof                         true
% 3.44/1.00  
% 3.44/1.00  ------ Superposition Options
% 3.44/1.00  
% 3.44/1.00  --superposition_flag                    true
% 3.44/1.00  --sup_passive_queue_type                priority_queues
% 3.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.44/1.00  --demod_completeness_check              fast
% 3.44/1.00  --demod_use_ground                      true
% 3.44/1.00  --sup_to_prop_solver                    passive
% 3.44/1.00  --sup_prop_simpl_new                    true
% 3.44/1.00  --sup_prop_simpl_given                  true
% 3.44/1.00  --sup_fun_splitting                     false
% 3.44/1.00  --sup_smt_interval                      50000
% 3.44/1.00  
% 3.44/1.00  ------ Superposition Simplification Setup
% 3.44/1.00  
% 3.44/1.00  --sup_indices_passive                   []
% 3.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.00  --sup_full_bw                           [BwDemod]
% 3.44/1.00  --sup_immed_triv                        [TrivRules]
% 3.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.00  --sup_immed_bw_main                     []
% 3.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/1.00  
% 3.44/1.00  ------ Combination Options
% 3.44/1.00  
% 3.44/1.00  --comb_res_mult                         3
% 3.44/1.00  --comb_sup_mult                         2
% 3.44/1.00  --comb_inst_mult                        10
% 3.44/1.00  
% 3.44/1.00  ------ Debug Options
% 3.44/1.00  
% 3.44/1.00  --dbg_backtrace                         false
% 3.44/1.00  --dbg_dump_prop_clauses                 false
% 3.44/1.00  --dbg_dump_prop_clauses_file            -
% 3.44/1.00  --dbg_out_stat                          false
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  ------ Proving...
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  % SZS status Theorem for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00   Resolution empty clause
% 3.44/1.00  
% 3.44/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  fof(f13,axiom,(
% 3.44/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f30,plain,(
% 3.44/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.00    inference(ennf_transformation,[],[f13])).
% 3.44/1.00  
% 3.44/1.00  fof(f31,plain,(
% 3.44/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.00    inference(flattening,[],[f30])).
% 3.44/1.00  
% 3.44/1.00  fof(f45,plain,(
% 3.44/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.00    inference(nnf_transformation,[],[f31])).
% 3.44/1.00  
% 3.44/1.00  fof(f70,plain,(
% 3.44/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/1.00    inference(cnf_transformation,[],[f45])).
% 3.44/1.00  
% 3.44/1.00  fof(f16,conjecture,(
% 3.44/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f17,negated_conjecture,(
% 3.44/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.44/1.00    inference(negated_conjecture,[],[f16])).
% 3.44/1.00  
% 3.44/1.00  fof(f36,plain,(
% 3.44/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.44/1.00    inference(ennf_transformation,[],[f17])).
% 3.44/1.00  
% 3.44/1.00  fof(f37,plain,(
% 3.44/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.44/1.00    inference(flattening,[],[f36])).
% 3.44/1.00  
% 3.44/1.00  fof(f46,plain,(
% 3.44/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.44/1.00    introduced(choice_axiom,[])).
% 3.44/1.00  
% 3.44/1.00  fof(f47,plain,(
% 3.44/1.00    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f46])).
% 3.44/1.00  
% 3.44/1.00  fof(f83,plain,(
% 3.44/1.00    v1_funct_2(sK3,sK1,sK2)),
% 3.44/1.00    inference(cnf_transformation,[],[f47])).
% 3.44/1.00  
% 3.44/1.00  fof(f84,plain,(
% 3.44/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.44/1.00    inference(cnf_transformation,[],[f47])).
% 3.44/1.00  
% 3.44/1.00  fof(f11,axiom,(
% 3.44/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f28,plain,(
% 3.44/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.00    inference(ennf_transformation,[],[f11])).
% 3.44/1.00  
% 3.44/1.00  fof(f68,plain,(
% 3.44/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/1.00    inference(cnf_transformation,[],[f28])).
% 3.44/1.00  
% 3.44/1.00  fof(f10,axiom,(
% 3.44/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f27,plain,(
% 3.44/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.00    inference(ennf_transformation,[],[f10])).
% 3.44/1.00  
% 3.44/1.00  fof(f67,plain,(
% 3.44/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/1.00    inference(cnf_transformation,[],[f27])).
% 3.44/1.00  
% 3.44/1.00  fof(f8,axiom,(
% 3.44/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f25,plain,(
% 3.44/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.44/1.00    inference(ennf_transformation,[],[f8])).
% 3.44/1.00  
% 3.44/1.00  fof(f26,plain,(
% 3.44/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.44/1.00    inference(flattening,[],[f25])).
% 3.44/1.00  
% 3.44/1.00  fof(f64,plain,(
% 3.44/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f26])).
% 3.44/1.00  
% 3.44/1.00  fof(f85,plain,(
% 3.44/1.00    v2_funct_1(sK3)),
% 3.44/1.00    inference(cnf_transformation,[],[f47])).
% 3.44/1.00  
% 3.44/1.00  fof(f82,plain,(
% 3.44/1.00    v1_funct_1(sK3)),
% 3.44/1.00    inference(cnf_transformation,[],[f47])).
% 3.44/1.00  
% 3.44/1.00  fof(f14,axiom,(
% 3.44/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f32,plain,(
% 3.44/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.44/1.00    inference(ennf_transformation,[],[f14])).
% 3.44/1.00  
% 3.44/1.00  fof(f33,plain,(
% 3.44/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.44/1.00    inference(flattening,[],[f32])).
% 3.44/1.00  
% 3.44/1.00  fof(f78,plain,(
% 3.44/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f33])).
% 3.44/1.00  
% 3.44/1.00  fof(f12,axiom,(
% 3.44/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f29,plain,(
% 3.44/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.00    inference(ennf_transformation,[],[f12])).
% 3.44/1.00  
% 3.44/1.00  fof(f69,plain,(
% 3.44/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/1.00    inference(cnf_transformation,[],[f29])).
% 3.44/1.00  
% 3.44/1.00  fof(f86,plain,(
% 3.44/1.00    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.44/1.00    inference(cnf_transformation,[],[f47])).
% 3.44/1.00  
% 3.44/1.00  fof(f63,plain,(
% 3.44/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f26])).
% 3.44/1.00  
% 3.44/1.00  fof(f7,axiom,(
% 3.44/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f23,plain,(
% 3.44/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.44/1.00    inference(ennf_transformation,[],[f7])).
% 3.44/1.00  
% 3.44/1.00  fof(f24,plain,(
% 3.44/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.44/1.00    inference(flattening,[],[f23])).
% 3.44/1.00  
% 3.44/1.00  fof(f62,plain,(
% 3.44/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f24])).
% 3.44/1.00  
% 3.44/1.00  fof(f61,plain,(
% 3.44/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f24])).
% 3.44/1.00  
% 3.44/1.00  fof(f6,axiom,(
% 3.44/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f21,plain,(
% 3.44/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.44/1.00    inference(ennf_transformation,[],[f6])).
% 3.44/1.00  
% 3.44/1.00  fof(f22,plain,(
% 3.44/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.44/1.00    inference(flattening,[],[f21])).
% 3.44/1.00  
% 3.44/1.00  fof(f60,plain,(
% 3.44/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f22])).
% 3.44/1.00  
% 3.44/1.00  fof(f77,plain,(
% 3.44/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f33])).
% 3.44/1.00  
% 3.44/1.00  fof(f87,plain,(
% 3.44/1.00    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.44/1.00    inference(cnf_transformation,[],[f47])).
% 3.44/1.00  
% 3.44/1.00  fof(f15,axiom,(
% 3.44/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f34,plain,(
% 3.44/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.44/1.00    inference(ennf_transformation,[],[f15])).
% 3.44/1.00  
% 3.44/1.00  fof(f35,plain,(
% 3.44/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.44/1.00    inference(flattening,[],[f34])).
% 3.44/1.00  
% 3.44/1.00  fof(f80,plain,(
% 3.44/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f35])).
% 3.44/1.00  
% 3.44/1.00  fof(f5,axiom,(
% 3.44/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f57,plain,(
% 3.44/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.44/1.00    inference(cnf_transformation,[],[f5])).
% 3.44/1.00  
% 3.44/1.00  fof(f3,axiom,(
% 3.44/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f42,plain,(
% 3.44/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.44/1.00    inference(nnf_transformation,[],[f3])).
% 3.44/1.00  
% 3.44/1.00  fof(f43,plain,(
% 3.44/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.44/1.00    inference(flattening,[],[f42])).
% 3.44/1.00  
% 3.44/1.00  fof(f54,plain,(
% 3.44/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.44/1.00    inference(cnf_transformation,[],[f43])).
% 3.44/1.00  
% 3.44/1.00  fof(f91,plain,(
% 3.44/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.44/1.00    inference(equality_resolution,[],[f54])).
% 3.44/1.00  
% 3.44/1.00  fof(f9,axiom,(
% 3.44/1.00    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f18,plain,(
% 3.44/1.00    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 3.44/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.44/1.00  
% 3.44/1.00  fof(f19,plain,(
% 3.44/1.00    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 3.44/1.00    inference(pure_predicate_removal,[],[f18])).
% 3.44/1.00  
% 3.44/1.00  fof(f44,plain,(
% 3.44/1.00    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 3.44/1.00    inference(rectify,[],[f19])).
% 3.44/1.00  
% 3.44/1.00  fof(f65,plain,(
% 3.44/1.00    v1_relat_1(k1_xboole_0)),
% 3.44/1.00    inference(cnf_transformation,[],[f44])).
% 3.44/1.00  
% 3.44/1.00  fof(f66,plain,(
% 3.44/1.00    v1_funct_1(k1_xboole_0)),
% 3.44/1.00    inference(cnf_transformation,[],[f44])).
% 3.44/1.00  
% 3.44/1.00  fof(f1,axiom,(
% 3.44/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f48,plain,(
% 3.44/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f1])).
% 3.44/1.00  
% 3.44/1.00  cnf(c_27,plain,
% 3.44/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.44/1.00      | k1_xboole_0 = X2 ),
% 3.44/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_38,negated_conjecture,
% 3.44/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.44/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_992,plain,
% 3.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.44/1.00      | sK1 != X1
% 3.44/1.00      | sK2 != X2
% 3.44/1.00      | sK3 != X0
% 3.44/1.00      | k1_xboole_0 = X2 ),
% 3.44/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_993,plain,
% 3.44/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.44/1.00      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.44/1.00      | k1_xboole_0 = sK2 ),
% 3.44/1.00      inference(unflattening,[status(thm)],[c_992]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_37,negated_conjecture,
% 3.44/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.44/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_995,plain,
% 3.44/1.00      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.44/1.00      inference(global_propositional_subsumption,[status(thm)],[c_993,c_37]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2361,plain,
% 3.44/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_20,plain,
% 3.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2365,plain,
% 3.44/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.44/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4909,plain,
% 3.44/1.00      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_2361,c_2365]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5142,plain,
% 3.44/1.00      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_995,c_4909]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_19,plain,
% 3.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2366,plain,
% 3.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.44/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3531,plain,
% 3.44/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_2361,c_2366]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_15,plain,
% 3.44/1.00      ( ~ v2_funct_1(X0)
% 3.44/1.00      | ~ v1_funct_1(X0)
% 3.44/1.00      | ~ v1_relat_1(X0)
% 3.44/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_36,negated_conjecture,
% 3.44/1.00      ( v2_funct_1(sK3) ),
% 3.44/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_458,plain,
% 3.44/1.00      ( ~ v1_funct_1(X0)
% 3.44/1.00      | ~ v1_relat_1(X0)
% 3.44/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.44/1.00      | sK3 != X0 ),
% 3.44/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_36]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_459,plain,
% 3.44/1.00      ( ~ v1_funct_1(sK3)
% 3.44/1.00      | ~ v1_relat_1(sK3)
% 3.44/1.00      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.44/1.00      inference(unflattening,[status(thm)],[c_458]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_39,negated_conjecture,
% 3.44/1.00      ( v1_funct_1(sK3) ),
% 3.44/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_461,plain,
% 3.44/1.00      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.44/1.00      inference(global_propositional_subsumption,[status(thm)],[c_459,c_39]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2358,plain,
% 3.44/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.44/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3582,plain,
% 3.44/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_3531,c_2358]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_28,plain,
% 3.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.44/1.00      | ~ v1_funct_1(X0)
% 3.44/1.00      | ~ v1_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2363,plain,
% 3.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.44/1.00      | v1_funct_1(X0) != iProver_top
% 3.44/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_6063,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.44/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.44/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_3582,c_2363]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_21,plain,
% 3.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2364,plain,
% 3.44/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.44/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4429,plain,
% 3.44/1.00      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_2361,c_2364]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_35,negated_conjecture,
% 3.44/1.00      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.44/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4446,plain,
% 3.44/1.00      ( k2_relat_1(sK3) = sK2 ),
% 3.44/1.00      inference(light_normalisation,[status(thm)],[c_4429,c_35]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_16,plain,
% 3.44/1.00      ( ~ v2_funct_1(X0)
% 3.44/1.00      | ~ v1_funct_1(X0)
% 3.44/1.00      | ~ v1_relat_1(X0)
% 3.44/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_444,plain,
% 3.44/1.00      ( ~ v1_funct_1(X0)
% 3.44/1.00      | ~ v1_relat_1(X0)
% 3.44/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.44/1.00      | sK3 != X0 ),
% 3.44/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_36]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_445,plain,
% 3.44/1.00      ( ~ v1_funct_1(sK3)
% 3.44/1.00      | ~ v1_relat_1(sK3)
% 3.44/1.00      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.44/1.00      inference(unflattening,[status(thm)],[c_444]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_447,plain,
% 3.44/1.00      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.44/1.00      inference(global_propositional_subsumption,[status(thm)],[c_445,c_39]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2359,plain,
% 3.44/1.00      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.44/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3581,plain,
% 3.44/1.00      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_3531,c_2359]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4461,plain,
% 3.44/1.00      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_4446,c_3581]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_6076,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.44/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.44/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.44/1.00      inference(light_normalisation,[status(thm)],[c_6063,c_4461]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_40,plain,
% 3.44/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_42,plain,
% 3.44/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_13,plain,
% 3.44/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2695,plain,
% 3.44/1.00      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2696,plain,
% 3.44/1.00      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.44/1.00      | v1_funct_1(sK3) != iProver_top
% 3.44/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_2695]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2709,plain,
% 3.44/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK3) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2851,plain,
% 3.44/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.44/1.00      | v1_relat_1(sK3) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_2709]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2852,plain,
% 3.44/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.44/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_2851]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_6566,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.44/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_6076,c_40,c_42,c_2696,c_2852]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_6572,plain,
% 3.44/1.00      ( sK2 = k1_xboole_0
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
% 3.44/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_5142,c_6566]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_14,plain,
% 3.44/1.00      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.44/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2369,plain,
% 3.44/1.00      ( v1_funct_1(X0) != iProver_top
% 3.44/1.00      | v1_relat_1(X0) != iProver_top
% 3.44/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_11,plain,
% 3.44/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.44/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2372,plain,
% 3.44/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 3.44/1.00      | k1_xboole_0 = X0
% 3.44/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3975,plain,
% 3.44/1.00      ( k2_funct_1(sK3) = k1_xboole_0
% 3.44/1.00      | k1_relat_1(sK3) != k1_xboole_0
% 3.44/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_3582,c_2372]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5387,plain,
% 3.44/1.00      ( k2_funct_1(sK3) = k1_xboole_0
% 3.44/1.00      | sK1 != k1_xboole_0
% 3.44/1.00      | sK2 = k1_xboole_0
% 3.44/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_5142,c_3975]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_29,plain,
% 3.44/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.44/1.00      | ~ v1_funct_1(X0)
% 3.44/1.00      | ~ v1_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_34,negated_conjecture,
% 3.44/1.00      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.44/1.00      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.44/1.00      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.44/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1003,plain,
% 3.44/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.44/1.00      | ~ v1_funct_1(X0)
% 3.44/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.44/1.00      | ~ v1_relat_1(X0)
% 3.44/1.00      | k2_funct_1(sK3) != X0
% 3.44/1.00      | k1_relat_1(X0) != sK2
% 3.44/1.00      | k2_relat_1(X0) != sK1 ),
% 3.44/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_34]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1004,plain,
% 3.44/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.44/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.44/1.00      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.44/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.44/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.44/1.00      inference(unflattening,[status(thm)],[c_1003]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1016,plain,
% 3.44/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.44/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.44/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.44/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.44/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1004,c_19]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2347,plain,
% 3.44/1.00      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.44/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.44/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1021,plain,
% 3.44/1.00      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.44/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.44/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2974,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.44/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.44/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_2347,c_40,c_42,c_1021,c_2696,c_2852]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2975,plain,
% 3.44/1.00      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.44/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.44/1.00      inference(renaming,[status(thm)],[c_2974]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3588,plain,
% 3.44/1.00      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.44/1.00      | k2_relat_1(sK3) != sK2
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_3581,c_2975]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3670,plain,
% 3.44/1.00      ( k1_relat_1(sK3) != sK1
% 3.44/1.00      | k2_relat_1(sK3) != sK2
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.44/1.00      inference(light_normalisation,[status(thm)],[c_3588,c_3582]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4460,plain,
% 3.44/1.00      ( k1_relat_1(sK3) != sK1
% 3.44/1.00      | sK2 != sK2
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_4446,c_3670]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4464,plain,
% 3.44/1.00      ( k1_relat_1(sK3) != sK1
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.44/1.00      inference(equality_resolution_simp,[status(thm)],[c_4460]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5839,plain,
% 3.44/1.00      ( sK2 = k1_xboole_0
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_5142,c_4464]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_6785,plain,
% 3.44/1.00      ( sK2 = k1_xboole_0 | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_5387,c_5839,c_6572]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_6791,plain,
% 3.44/1.00      ( sK2 = k1_xboole_0
% 3.44/1.00      | v1_funct_1(sK3) != iProver_top
% 3.44/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_2369,c_6785]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7379,plain,
% 3.44/1.00      ( sK2 = k1_xboole_0 ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_6572,c_40,c_42,c_2852,c_6791]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_32,plain,
% 3.44/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.44/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.44/1.00      | ~ v1_funct_1(X0)
% 3.44/1.00      | ~ v1_relat_1(X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1022,plain,
% 3.44/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.44/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.44/1.00      | ~ v1_funct_1(X0)
% 3.44/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.44/1.00      | ~ v1_relat_1(X0)
% 3.44/1.00      | k2_funct_1(sK3) != X0
% 3.44/1.00      | k1_relat_1(X0) != sK2
% 3.44/1.00      | sK1 != X1 ),
% 3.44/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_34]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1023,plain,
% 3.44/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.44/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 3.44/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.44/1.00      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.44/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.44/1.00      inference(unflattening,[status(thm)],[c_1022]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1035,plain,
% 3.44/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.44/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 3.44/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.44/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.44/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1023,c_19]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2346,plain,
% 3.44/1.00      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.44/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 3.44/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1035]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3589,plain,
% 3.44/1.00      ( k2_relat_1(sK3) != sK2
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.44/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 3.44/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_3581,c_2346]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4221,plain,
% 3.44/1.00      ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.44/1.00      | k2_relat_1(sK3) != sK2 ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_3589,c_40,c_42,c_2696,c_2852]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4222,plain,
% 3.44/1.00      ( k2_relat_1(sK3) != sK2
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.44/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top ),
% 3.44/1.00      inference(renaming,[status(thm)],[c_4221]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4225,plain,
% 3.44/1.00      ( k2_relat_1(sK3) != sK2
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.44/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.44/1.00      inference(light_normalisation,[status(thm)],[c_4222,c_3582]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4456,plain,
% 3.44/1.00      ( sK2 != sK2
% 3.44/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.44/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_4446,c_4225]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4483,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.44/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.44/1.00      inference(equality_resolution_simp,[status(thm)],[c_4456]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7394,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.44/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_7379,c_4483]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4494,plain,
% 3.44/1.00      ( sK2 != k1_xboole_0
% 3.44/1.00      | sK3 = k1_xboole_0
% 3.44/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_4446,c_2372]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4510,plain,
% 3.44/1.00      ( ~ v1_relat_1(sK3) | sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.44/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4494]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5244,plain,
% 3.44/1.00      ( sK3 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_4494,c_37,c_2851,c_4510]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_5245,plain,
% 3.44/1.00      ( sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.44/1.00      inference(renaming,[status(thm)],[c_5244]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7401,plain,
% 3.44/1.00      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_7379,c_5245]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7466,plain,
% 3.44/1.00      ( sK3 = k1_xboole_0 ),
% 3.44/1.00      inference(equality_resolution_simp,[status(thm)],[c_7401]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7522,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.44/1.00      | r1_tarski(k1_relat_1(k1_xboole_0),sK1) != iProver_top ),
% 3.44/1.00      inference(light_normalisation,[status(thm)],[c_7394,c_7466]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_10,plain,
% 3.44/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.44/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7525,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.44/1.00      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.44/1.00      inference(light_normalisation,[status(thm)],[c_7522,c_10]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_6,plain,
% 3.44/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.44/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7526,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.44/1.00      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_7525,c_6]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_18,plain,
% 3.44/1.00      ( v1_relat_1(k1_xboole_0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_86,plain,
% 3.44/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_17,plain,
% 3.44/1.00      ( v1_funct_1(k1_xboole_0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_87,plain,
% 3.44/1.00      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_94,plain,
% 3.44/1.00      ( v1_funct_1(X0) != iProver_top
% 3.44/1.00      | v1_relat_1(X0) != iProver_top
% 3.44/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_96,plain,
% 3.44/1.00      ( v1_funct_1(k1_xboole_0) != iProver_top
% 3.44/1.00      | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 3.44/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_94]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7389,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top
% 3.44/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_7379,c_6566]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7536,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) = iProver_top
% 3.44/1.00      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.44/1.00      inference(light_normalisation,[status(thm)],[c_7389,c_7466]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7539,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.44/1.00      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.44/1.00      inference(light_normalisation,[status(thm)],[c_7536,c_10]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_7540,plain,
% 3.44/1.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.44/1.00      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_7539,c_6]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_8948,plain,
% 3.44/1.00      ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_7526,c_86,c_87,c_96,c_7540]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_0,plain,
% 3.44/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.44/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2378,plain,
% 3.44/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.44/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_8953,plain,
% 3.44/1.00      ( $false ),
% 3.44/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_8948,c_2378]) ).
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  ------                               Statistics
% 3.44/1.00  
% 3.44/1.00  ------ General
% 3.44/1.00  
% 3.44/1.00  abstr_ref_over_cycles:                  0
% 3.44/1.00  abstr_ref_under_cycles:                 0
% 3.44/1.00  gc_basic_clause_elim:                   0
% 3.44/1.00  forced_gc_time:                         0
% 3.44/1.00  parsing_time:                           0.012
% 3.44/1.00  unif_index_cands_time:                  0.
% 3.44/1.00  unif_index_add_time:                    0.
% 3.44/1.00  orderings_time:                         0.
% 3.44/1.00  out_proof_time:                         0.017
% 3.44/1.00  total_time:                             0.364
% 3.44/1.00  num_of_symbols:                         50
% 3.44/1.00  num_of_terms:                           7378
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing
% 3.44/1.00  
% 3.44/1.00  num_of_splits:                          0
% 3.44/1.00  num_of_split_atoms:                     0
% 3.44/1.00  num_of_reused_defs:                     0
% 3.44/1.00  num_eq_ax_congr_red:                    7
% 3.44/1.00  num_of_sem_filtered_clauses:            1
% 3.44/1.00  num_of_subtypes:                        0
% 3.44/1.00  monotx_restored_types:                  0
% 3.44/1.00  sat_num_of_epr_types:                   0
% 3.44/1.00  sat_num_of_non_cyclic_types:            0
% 3.44/1.00  sat_guarded_non_collapsed_types:        0
% 3.44/1.00  num_pure_diseq_elim:                    0
% 3.44/1.00  simp_replaced_by:                       0
% 3.44/1.00  res_preprocessed:                       149
% 3.44/1.00  prep_upred:                             0
% 3.44/1.00  prep_unflattend:                        103
% 3.44/1.00  smt_new_axioms:                         0
% 3.44/1.00  pred_elim_cands:                        7
% 3.44/1.00  pred_elim:                              2
% 3.44/1.00  pred_elim_cl:                           -3
% 3.44/1.00  pred_elim_cycles:                       5
% 3.44/1.00  merged_defs:                            6
% 3.44/1.00  merged_defs_ncl:                        0
% 3.44/1.00  bin_hyper_res:                          6
% 3.44/1.00  prep_cycles:                            3
% 3.44/1.00  pred_elim_time:                         0.023
% 3.44/1.00  splitting_time:                         0.
% 3.44/1.00  sem_filter_time:                        0.
% 3.44/1.00  monotx_time:                            0.001
% 3.44/1.00  subtype_inf_time:                       0.
% 3.44/1.00  
% 3.44/1.00  ------ Problem properties
% 3.44/1.00  
% 3.44/1.00  clauses:                                41
% 3.44/1.00  conjectures:                            3
% 3.44/1.00  epr:                                    5
% 3.44/1.00  horn:                                   34
% 3.44/1.00  ground:                                 18
% 3.44/1.00  unary:                                  10
% 3.44/1.00  binary:                                 9
% 3.44/1.00  lits:                                   113
% 3.44/1.00  lits_eq:                                47
% 3.44/1.00  fd_pure:                                0
% 3.44/1.00  fd_pseudo:                              0
% 3.44/1.00  fd_cond:                                5
% 3.44/1.00  fd_pseudo_cond:                         2
% 3.44/1.00  ac_symbols:                             0
% 3.44/1.00  
% 3.44/1.00  ------ Propositional Solver
% 3.44/1.00  
% 3.44/1.00  prop_solver_calls:                      24
% 3.44/1.00  prop_fast_solver_calls:                 1376
% 3.44/1.00  smt_solver_calls:                       0
% 3.44/1.00  smt_fast_solver_calls:                  0
% 3.44/1.00  prop_num_of_clauses:                    2830
% 3.44/1.00  prop_preprocess_simplified:             6992
% 3.44/1.00  prop_fo_subsumed:                       52
% 3.44/1.00  prop_solver_time:                       0.
% 3.44/1.00  smt_solver_time:                        0.
% 3.44/1.00  smt_fast_solver_time:                   0.
% 3.44/1.00  prop_fast_solver_time:                  0.
% 3.44/1.00  prop_unsat_core_time:                   0.
% 3.44/1.00  
% 3.44/1.00  ------ QBF
% 3.44/1.00  
% 3.44/1.00  qbf_q_res:                              0
% 3.44/1.00  qbf_num_tautologies:                    0
% 3.44/1.00  qbf_prep_cycles:                        0
% 3.44/1.00  
% 3.44/1.00  ------ BMC1
% 3.44/1.00  
% 3.44/1.00  bmc1_current_bound:                     -1
% 3.44/1.00  bmc1_last_solved_bound:                 -1
% 3.44/1.00  bmc1_unsat_core_size:                   -1
% 3.44/1.00  bmc1_unsat_core_parents_size:           -1
% 3.44/1.00  bmc1_merge_next_fun:                    0
% 3.44/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.44/1.00  
% 3.44/1.00  ------ Instantiation
% 3.44/1.00  
% 3.44/1.00  inst_num_of_clauses:                    931
% 3.44/1.00  inst_num_in_passive:                    6
% 3.44/1.00  inst_num_in_active:                     472
% 3.44/1.00  inst_num_in_unprocessed:                453
% 3.44/1.00  inst_num_of_loops:                      530
% 3.44/1.00  inst_num_of_learning_restarts:          0
% 3.44/1.00  inst_num_moves_active_passive:          55
% 3.44/1.00  inst_lit_activity:                      0
% 3.44/1.00  inst_lit_activity_moves:                0
% 3.44/1.00  inst_num_tautologies:                   0
% 3.44/1.00  inst_num_prop_implied:                  0
% 3.44/1.00  inst_num_existing_simplified:           0
% 3.44/1.00  inst_num_eq_res_simplified:             0
% 3.44/1.00  inst_num_child_elim:                    0
% 3.44/1.00  inst_num_of_dismatching_blockings:      706
% 3.44/1.00  inst_num_of_non_proper_insts:           1016
% 3.44/1.00  inst_num_of_duplicates:                 0
% 3.44/1.00  inst_inst_num_from_inst_to_res:         0
% 3.44/1.00  inst_dismatching_checking_time:         0.
% 3.44/1.00  
% 3.44/1.00  ------ Resolution
% 3.44/1.00  
% 3.44/1.00  res_num_of_clauses:                     0
% 3.44/1.00  res_num_in_passive:                     0
% 3.44/1.00  res_num_in_active:                      0
% 3.44/1.00  res_num_of_loops:                       152
% 3.44/1.00  res_forward_subset_subsumed:            43
% 3.44/1.00  res_backward_subset_subsumed:           2
% 3.44/1.00  res_forward_subsumed:                   1
% 3.44/1.00  res_backward_subsumed:                  0
% 3.44/1.00  res_forward_subsumption_resolution:     6
% 3.44/1.00  res_backward_subsumption_resolution:    0
% 3.44/1.00  res_clause_to_clause_subsumption:       384
% 3.44/1.00  res_orphan_elimination:                 0
% 3.44/1.00  res_tautology_del:                      117
% 3.44/1.00  res_num_eq_res_simplified:              0
% 3.44/1.00  res_num_sel_changes:                    0
% 3.44/1.00  res_moves_from_active_to_pass:          0
% 3.44/1.00  
% 3.44/1.00  ------ Superposition
% 3.44/1.00  
% 3.44/1.00  sup_time_total:                         0.
% 3.44/1.00  sup_time_generating:                    0.
% 3.44/1.00  sup_time_sim_full:                      0.
% 3.44/1.00  sup_time_sim_immed:                     0.
% 3.44/1.00  
% 3.44/1.00  sup_num_of_clauses:                     79
% 3.44/1.00  sup_num_in_active:                      51
% 3.44/1.00  sup_num_in_passive:                     28
% 3.44/1.00  sup_num_of_loops:                       104
% 3.44/1.00  sup_fw_superposition:                   61
% 3.44/1.00  sup_bw_superposition:                   62
% 3.44/1.00  sup_immediate_simplified:               95
% 3.44/1.00  sup_given_eliminated:                   0
% 3.44/1.00  comparisons_done:                       0
% 3.44/1.00  comparisons_avoided:                    8
% 3.44/1.00  
% 3.44/1.00  ------ Simplifications
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  sim_fw_subset_subsumed:                 12
% 3.44/1.00  sim_bw_subset_subsumed:                 11
% 3.44/1.00  sim_fw_subsumed:                        8
% 3.44/1.00  sim_bw_subsumed:                        3
% 3.44/1.00  sim_fw_subsumption_res:                 4
% 3.44/1.00  sim_bw_subsumption_res:                 0
% 3.44/1.00  sim_tautology_del:                      5
% 3.44/1.00  sim_eq_tautology_del:                   20
% 3.44/1.00  sim_eq_res_simp:                        7
% 3.44/1.00  sim_fw_demodulated:                     20
% 3.44/1.00  sim_bw_demodulated:                     56
% 3.44/1.00  sim_light_normalised:                   67
% 3.44/1.00  sim_joinable_taut:                      0
% 3.44/1.00  sim_joinable_simp:                      0
% 3.44/1.00  sim_ac_normalised:                      0
% 3.44/1.00  sim_smt_subsumption:                    0
% 3.44/1.00  
%------------------------------------------------------------------------------

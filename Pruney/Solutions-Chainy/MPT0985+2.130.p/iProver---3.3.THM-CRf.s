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
% DateTime   : Thu Dec  3 12:02:46 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  165 (3640 expanded)
%              Number of clauses        :  104 (1221 expanded)
%              Number of leaves         :   15 ( 695 expanded)
%              Depth                    :   23
%              Number of atoms          :  477 (18516 expanded)
%              Number of equality atoms :  280 (4561 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

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
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f46])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f18,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(nnf_transformation,[],[f40])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1093,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1096,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4180,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1093,c_1096])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_456,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_458,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_31])).

cnf(c_4371,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4180,c_458])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1102,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4383,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4371,c_1102])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1324,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1325,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_25,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_28,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_28])).

cnf(c_440,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_1085,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_441,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1310,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1311,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1310])).

cnf(c_1374,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_xboole_0 = sK0
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1085,c_34,c_36,c_441,c_1311,c_1325])).

cnf(c_1375,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1374])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_336,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_337,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_339,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_337,c_33])).

cnf(c_1090,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_1328,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1090,c_33,c_31,c_337,c_1324])).

cnf(c_1378,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != sK1
    | sK0 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1375,c_1328])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1094,plain,
    ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3167,plain,
    ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1093,c_1094])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1097,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3200,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3167,c_1097])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1095,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3518,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1093,c_1095])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3530,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3518,c_29])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1103,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3651,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3530,c_1103])).

cnf(c_3652,plain,
    ( ~ v1_relat_1(sK2)
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3651])).

cnf(c_3705,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3651,c_31,c_1324,c_3652])).

cnf(c_3706,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3705])).

cnf(c_3856,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3200,c_36])).

cnf(c_4181,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3856,c_1096])).

cnf(c_1099,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2006,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1093,c_1099])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1104,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2030,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2006,c_1104])).

cnf(c_3641,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3530,c_2030])).

cnf(c_4193,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4181,c_3641])).

cnf(c_4631,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4383,c_36,c_1325,c_1378,c_3200,c_3706,c_4193])).

cnf(c_4636,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(k1_xboole_0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4631,c_4193])).

cnf(c_4663,plain,
    ( k2_relset_1(sK0,sK1,k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_4631,c_29])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1106,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3515,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1106,c_1095])).

cnf(c_9,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3541,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3515,c_9])).

cnf(c_4665,plain,
    ( sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4663,c_3541])).

cnf(c_2599,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | k4_relat_1(sK2) = k1_xboole_0
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2030,c_1102])).

cnf(c_3640,plain,
    ( k4_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3530,c_2599])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1100,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3291,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1328,c_1100])).

cnf(c_3710,plain,
    ( sK1 != k1_xboole_0
    | k4_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3640,c_34,c_36,c_1325,c_3291])).

cnf(c_3711,plain,
    ( k4_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3710])).

cnf(c_4644,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4631,c_3711])).

cnf(c_4707,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4644,c_4665])).

cnf(c_4708,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4707])).

cnf(c_4742,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4636,c_4665,c_4708])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_408,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_1087,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1243,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1087,c_3])).

cnf(c_1551,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1243,c_34,c_36,c_1311,c_1325])).

cnf(c_1552,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1551])).

cnf(c_1555,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1552,c_1328])).

cnf(c_4655,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4631,c_1555])).

cnf(c_4689,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4655,c_4665])).

cnf(c_4690,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4689])).

cnf(c_4694,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4690,c_3])).

cnf(c_4711,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4708,c_4694])).

cnf(c_4744,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4742,c_4711])).

cnf(c_4746,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4744])).

cnf(c_99,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_101,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4746,c_101])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.06/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.04  
% 2.06/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.06/1.04  
% 2.06/1.04  ------  iProver source info
% 2.06/1.04  
% 2.06/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.06/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.06/1.04  git: non_committed_changes: false
% 2.06/1.04  git: last_make_outside_of_git: false
% 2.06/1.04  
% 2.06/1.04  ------ 
% 2.06/1.04  
% 2.06/1.04  ------ Input Options
% 2.06/1.04  
% 2.06/1.04  --out_options                           all
% 2.06/1.04  --tptp_safe_out                         true
% 2.06/1.04  --problem_path                          ""
% 2.06/1.04  --include_path                          ""
% 2.06/1.04  --clausifier                            res/vclausify_rel
% 2.06/1.04  --clausifier_options                    --mode clausify
% 2.06/1.04  --stdin                                 false
% 2.06/1.04  --stats_out                             all
% 2.06/1.04  
% 2.06/1.04  ------ General Options
% 2.06/1.04  
% 2.06/1.04  --fof                                   false
% 2.06/1.04  --time_out_real                         305.
% 2.06/1.04  --time_out_virtual                      -1.
% 2.06/1.04  --symbol_type_check                     false
% 2.06/1.04  --clausify_out                          false
% 2.06/1.04  --sig_cnt_out                           false
% 2.06/1.04  --trig_cnt_out                          false
% 2.06/1.04  --trig_cnt_out_tolerance                1.
% 2.06/1.04  --trig_cnt_out_sk_spl                   false
% 2.06/1.04  --abstr_cl_out                          false
% 2.06/1.04  
% 2.06/1.04  ------ Global Options
% 2.06/1.04  
% 2.06/1.04  --schedule                              default
% 2.06/1.04  --add_important_lit                     false
% 2.06/1.04  --prop_solver_per_cl                    1000
% 2.06/1.04  --min_unsat_core                        false
% 2.06/1.04  --soft_assumptions                      false
% 2.06/1.04  --soft_lemma_size                       3
% 2.06/1.04  --prop_impl_unit_size                   0
% 2.06/1.04  --prop_impl_unit                        []
% 2.06/1.04  --share_sel_clauses                     true
% 2.06/1.04  --reset_solvers                         false
% 2.06/1.04  --bc_imp_inh                            [conj_cone]
% 2.06/1.04  --conj_cone_tolerance                   3.
% 2.06/1.04  --extra_neg_conj                        none
% 2.06/1.04  --large_theory_mode                     true
% 2.06/1.04  --prolific_symb_bound                   200
% 2.06/1.04  --lt_threshold                          2000
% 2.06/1.04  --clause_weak_htbl                      true
% 2.06/1.04  --gc_record_bc_elim                     false
% 2.06/1.04  
% 2.06/1.04  ------ Preprocessing Options
% 2.06/1.04  
% 2.06/1.04  --preprocessing_flag                    true
% 2.06/1.04  --time_out_prep_mult                    0.1
% 2.06/1.04  --splitting_mode                        input
% 2.06/1.04  --splitting_grd                         true
% 2.06/1.04  --splitting_cvd                         false
% 2.06/1.04  --splitting_cvd_svl                     false
% 2.06/1.04  --splitting_nvd                         32
% 2.06/1.04  --sub_typing                            true
% 2.06/1.04  --prep_gs_sim                           true
% 2.06/1.04  --prep_unflatten                        true
% 2.06/1.04  --prep_res_sim                          true
% 2.06/1.04  --prep_upred                            true
% 2.06/1.04  --prep_sem_filter                       exhaustive
% 2.06/1.04  --prep_sem_filter_out                   false
% 2.06/1.04  --pred_elim                             true
% 2.06/1.04  --res_sim_input                         true
% 2.06/1.04  --eq_ax_congr_red                       true
% 2.06/1.04  --pure_diseq_elim                       true
% 2.06/1.04  --brand_transform                       false
% 2.06/1.04  --non_eq_to_eq                          false
% 2.06/1.04  --prep_def_merge                        true
% 2.06/1.04  --prep_def_merge_prop_impl              false
% 2.06/1.04  --prep_def_merge_mbd                    true
% 2.06/1.04  --prep_def_merge_tr_red                 false
% 2.06/1.04  --prep_def_merge_tr_cl                  false
% 2.06/1.04  --smt_preprocessing                     true
% 2.06/1.04  --smt_ac_axioms                         fast
% 2.06/1.04  --preprocessed_out                      false
% 2.06/1.04  --preprocessed_stats                    false
% 2.06/1.04  
% 2.06/1.04  ------ Abstraction refinement Options
% 2.06/1.04  
% 2.06/1.04  --abstr_ref                             []
% 2.06/1.04  --abstr_ref_prep                        false
% 2.06/1.04  --abstr_ref_until_sat                   false
% 2.06/1.04  --abstr_ref_sig_restrict                funpre
% 2.06/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/1.04  --abstr_ref_under                       []
% 2.06/1.04  
% 2.06/1.04  ------ SAT Options
% 2.06/1.04  
% 2.06/1.04  --sat_mode                              false
% 2.06/1.04  --sat_fm_restart_options                ""
% 2.06/1.04  --sat_gr_def                            false
% 2.06/1.04  --sat_epr_types                         true
% 2.06/1.04  --sat_non_cyclic_types                  false
% 2.06/1.04  --sat_finite_models                     false
% 2.06/1.04  --sat_fm_lemmas                         false
% 2.06/1.04  --sat_fm_prep                           false
% 2.06/1.04  --sat_fm_uc_incr                        true
% 2.06/1.04  --sat_out_model                         small
% 2.06/1.04  --sat_out_clauses                       false
% 2.06/1.04  
% 2.06/1.04  ------ QBF Options
% 2.06/1.04  
% 2.06/1.04  --qbf_mode                              false
% 2.06/1.04  --qbf_elim_univ                         false
% 2.06/1.04  --qbf_dom_inst                          none
% 2.06/1.04  --qbf_dom_pre_inst                      false
% 2.06/1.04  --qbf_sk_in                             false
% 2.06/1.04  --qbf_pred_elim                         true
% 2.06/1.04  --qbf_split                             512
% 2.06/1.04  
% 2.06/1.04  ------ BMC1 Options
% 2.06/1.04  
% 2.06/1.04  --bmc1_incremental                      false
% 2.06/1.04  --bmc1_axioms                           reachable_all
% 2.06/1.04  --bmc1_min_bound                        0
% 2.06/1.04  --bmc1_max_bound                        -1
% 2.06/1.04  --bmc1_max_bound_default                -1
% 2.06/1.04  --bmc1_symbol_reachability              true
% 2.06/1.04  --bmc1_property_lemmas                  false
% 2.06/1.04  --bmc1_k_induction                      false
% 2.06/1.04  --bmc1_non_equiv_states                 false
% 2.06/1.04  --bmc1_deadlock                         false
% 2.06/1.04  --bmc1_ucm                              false
% 2.06/1.04  --bmc1_add_unsat_core                   none
% 2.06/1.04  --bmc1_unsat_core_children              false
% 2.06/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/1.04  --bmc1_out_stat                         full
% 2.06/1.04  --bmc1_ground_init                      false
% 2.06/1.04  --bmc1_pre_inst_next_state              false
% 2.06/1.04  --bmc1_pre_inst_state                   false
% 2.06/1.04  --bmc1_pre_inst_reach_state             false
% 2.06/1.04  --bmc1_out_unsat_core                   false
% 2.06/1.04  --bmc1_aig_witness_out                  false
% 2.06/1.04  --bmc1_verbose                          false
% 2.06/1.04  --bmc1_dump_clauses_tptp                false
% 2.06/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.06/1.04  --bmc1_dump_file                        -
% 2.06/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.06/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.06/1.04  --bmc1_ucm_extend_mode                  1
% 2.06/1.04  --bmc1_ucm_init_mode                    2
% 2.06/1.04  --bmc1_ucm_cone_mode                    none
% 2.06/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.06/1.04  --bmc1_ucm_relax_model                  4
% 2.06/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.06/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/1.04  --bmc1_ucm_layered_model                none
% 2.06/1.04  --bmc1_ucm_max_lemma_size               10
% 2.06/1.04  
% 2.06/1.04  ------ AIG Options
% 2.06/1.04  
% 2.06/1.04  --aig_mode                              false
% 2.06/1.04  
% 2.06/1.04  ------ Instantiation Options
% 2.06/1.04  
% 2.06/1.04  --instantiation_flag                    true
% 2.06/1.04  --inst_sos_flag                         false
% 2.06/1.04  --inst_sos_phase                        true
% 2.06/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/1.04  --inst_lit_sel_side                     num_symb
% 2.06/1.04  --inst_solver_per_active                1400
% 2.06/1.04  --inst_solver_calls_frac                1.
% 2.06/1.04  --inst_passive_queue_type               priority_queues
% 2.06/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/1.04  --inst_passive_queues_freq              [25;2]
% 2.06/1.04  --inst_dismatching                      true
% 2.06/1.04  --inst_eager_unprocessed_to_passive     true
% 2.06/1.04  --inst_prop_sim_given                   true
% 2.06/1.04  --inst_prop_sim_new                     false
% 2.06/1.04  --inst_subs_new                         false
% 2.06/1.04  --inst_eq_res_simp                      false
% 2.06/1.04  --inst_subs_given                       false
% 2.06/1.04  --inst_orphan_elimination               true
% 2.06/1.04  --inst_learning_loop_flag               true
% 2.06/1.04  --inst_learning_start                   3000
% 2.06/1.04  --inst_learning_factor                  2
% 2.06/1.04  --inst_start_prop_sim_after_learn       3
% 2.06/1.04  --inst_sel_renew                        solver
% 2.06/1.04  --inst_lit_activity_flag                true
% 2.06/1.04  --inst_restr_to_given                   false
% 2.06/1.04  --inst_activity_threshold               500
% 2.06/1.04  --inst_out_proof                        true
% 2.06/1.04  
% 2.06/1.04  ------ Resolution Options
% 2.06/1.04  
% 2.06/1.04  --resolution_flag                       true
% 2.06/1.04  --res_lit_sel                           adaptive
% 2.06/1.04  --res_lit_sel_side                      none
% 2.06/1.04  --res_ordering                          kbo
% 2.06/1.04  --res_to_prop_solver                    active
% 2.06/1.04  --res_prop_simpl_new                    false
% 2.06/1.04  --res_prop_simpl_given                  true
% 2.06/1.04  --res_passive_queue_type                priority_queues
% 2.06/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/1.04  --res_passive_queues_freq               [15;5]
% 2.06/1.04  --res_forward_subs                      full
% 2.06/1.04  --res_backward_subs                     full
% 2.06/1.04  --res_forward_subs_resolution           true
% 2.06/1.04  --res_backward_subs_resolution          true
% 2.06/1.04  --res_orphan_elimination                true
% 2.06/1.04  --res_time_limit                        2.
% 2.06/1.04  --res_out_proof                         true
% 2.06/1.04  
% 2.06/1.04  ------ Superposition Options
% 2.06/1.04  
% 2.06/1.04  --superposition_flag                    true
% 2.06/1.04  --sup_passive_queue_type                priority_queues
% 2.06/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.06/1.04  --demod_completeness_check              fast
% 2.06/1.04  --demod_use_ground                      true
% 2.06/1.04  --sup_to_prop_solver                    passive
% 2.06/1.04  --sup_prop_simpl_new                    true
% 2.06/1.04  --sup_prop_simpl_given                  true
% 2.06/1.04  --sup_fun_splitting                     false
% 2.06/1.04  --sup_smt_interval                      50000
% 2.06/1.04  
% 2.06/1.04  ------ Superposition Simplification Setup
% 2.06/1.04  
% 2.06/1.04  --sup_indices_passive                   []
% 2.06/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.04  --sup_full_bw                           [BwDemod]
% 2.06/1.04  --sup_immed_triv                        [TrivRules]
% 2.06/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.04  --sup_immed_bw_main                     []
% 2.06/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.04  
% 2.06/1.04  ------ Combination Options
% 2.06/1.04  
% 2.06/1.04  --comb_res_mult                         3
% 2.06/1.04  --comb_sup_mult                         2
% 2.06/1.04  --comb_inst_mult                        10
% 2.06/1.04  
% 2.06/1.04  ------ Debug Options
% 2.06/1.04  
% 2.06/1.04  --dbg_backtrace                         false
% 2.06/1.04  --dbg_dump_prop_clauses                 false
% 2.06/1.04  --dbg_dump_prop_clauses_file            -
% 2.06/1.04  --dbg_out_stat                          false
% 2.06/1.04  ------ Parsing...
% 2.06/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.06/1.04  
% 2.06/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.06/1.04  
% 2.06/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.06/1.04  
% 2.06/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.06/1.04  ------ Proving...
% 2.06/1.04  ------ Problem Properties 
% 2.06/1.04  
% 2.06/1.04  
% 2.06/1.04  clauses                                 31
% 2.06/1.04  conjectures                             3
% 2.06/1.04  EPR                                     1
% 2.06/1.04  Horn                                    28
% 2.06/1.04  unary                                   8
% 2.06/1.04  binary                                  12
% 2.06/1.04  lits                                    72
% 2.06/1.04  lits eq                                 37
% 2.06/1.04  fd_pure                                 0
% 2.06/1.04  fd_pseudo                               0
% 2.06/1.04  fd_cond                                 4
% 2.06/1.04  fd_pseudo_cond                          0
% 2.06/1.04  AC symbols                              0
% 2.06/1.04  
% 2.06/1.04  ------ Schedule dynamic 5 is on 
% 2.06/1.04  
% 2.06/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.06/1.04  
% 2.06/1.04  
% 2.06/1.04  ------ 
% 2.06/1.04  Current options:
% 2.06/1.04  ------ 
% 2.06/1.04  
% 2.06/1.04  ------ Input Options
% 2.06/1.04  
% 2.06/1.04  --out_options                           all
% 2.06/1.04  --tptp_safe_out                         true
% 2.06/1.04  --problem_path                          ""
% 2.06/1.04  --include_path                          ""
% 2.06/1.04  --clausifier                            res/vclausify_rel
% 2.06/1.04  --clausifier_options                    --mode clausify
% 2.06/1.04  --stdin                                 false
% 2.06/1.04  --stats_out                             all
% 2.06/1.04  
% 2.06/1.04  ------ General Options
% 2.06/1.04  
% 2.06/1.04  --fof                                   false
% 2.06/1.04  --time_out_real                         305.
% 2.06/1.04  --time_out_virtual                      -1.
% 2.06/1.04  --symbol_type_check                     false
% 2.06/1.04  --clausify_out                          false
% 2.06/1.04  --sig_cnt_out                           false
% 2.06/1.04  --trig_cnt_out                          false
% 2.06/1.04  --trig_cnt_out_tolerance                1.
% 2.06/1.04  --trig_cnt_out_sk_spl                   false
% 2.06/1.04  --abstr_cl_out                          false
% 2.06/1.04  
% 2.06/1.04  ------ Global Options
% 2.06/1.04  
% 2.06/1.04  --schedule                              default
% 2.06/1.04  --add_important_lit                     false
% 2.06/1.04  --prop_solver_per_cl                    1000
% 2.06/1.04  --min_unsat_core                        false
% 2.06/1.04  --soft_assumptions                      false
% 2.06/1.04  --soft_lemma_size                       3
% 2.06/1.04  --prop_impl_unit_size                   0
% 2.06/1.04  --prop_impl_unit                        []
% 2.06/1.04  --share_sel_clauses                     true
% 2.06/1.04  --reset_solvers                         false
% 2.06/1.04  --bc_imp_inh                            [conj_cone]
% 2.06/1.04  --conj_cone_tolerance                   3.
% 2.06/1.04  --extra_neg_conj                        none
% 2.06/1.04  --large_theory_mode                     true
% 2.06/1.04  --prolific_symb_bound                   200
% 2.06/1.04  --lt_threshold                          2000
% 2.06/1.04  --clause_weak_htbl                      true
% 2.06/1.04  --gc_record_bc_elim                     false
% 2.06/1.04  
% 2.06/1.04  ------ Preprocessing Options
% 2.06/1.04  
% 2.06/1.04  --preprocessing_flag                    true
% 2.06/1.04  --time_out_prep_mult                    0.1
% 2.06/1.04  --splitting_mode                        input
% 2.06/1.04  --splitting_grd                         true
% 2.06/1.04  --splitting_cvd                         false
% 2.06/1.04  --splitting_cvd_svl                     false
% 2.06/1.04  --splitting_nvd                         32
% 2.06/1.04  --sub_typing                            true
% 2.06/1.04  --prep_gs_sim                           true
% 2.06/1.04  --prep_unflatten                        true
% 2.06/1.04  --prep_res_sim                          true
% 2.06/1.04  --prep_upred                            true
% 2.06/1.04  --prep_sem_filter                       exhaustive
% 2.06/1.04  --prep_sem_filter_out                   false
% 2.06/1.04  --pred_elim                             true
% 2.06/1.04  --res_sim_input                         true
% 2.06/1.04  --eq_ax_congr_red                       true
% 2.06/1.04  --pure_diseq_elim                       true
% 2.06/1.04  --brand_transform                       false
% 2.06/1.04  --non_eq_to_eq                          false
% 2.06/1.04  --prep_def_merge                        true
% 2.06/1.04  --prep_def_merge_prop_impl              false
% 2.06/1.04  --prep_def_merge_mbd                    true
% 2.06/1.04  --prep_def_merge_tr_red                 false
% 2.06/1.04  --prep_def_merge_tr_cl                  false
% 2.06/1.04  --smt_preprocessing                     true
% 2.06/1.04  --smt_ac_axioms                         fast
% 2.06/1.04  --preprocessed_out                      false
% 2.06/1.04  --preprocessed_stats                    false
% 2.06/1.04  
% 2.06/1.04  ------ Abstraction refinement Options
% 2.06/1.04  
% 2.06/1.04  --abstr_ref                             []
% 2.06/1.04  --abstr_ref_prep                        false
% 2.06/1.04  --abstr_ref_until_sat                   false
% 2.06/1.04  --abstr_ref_sig_restrict                funpre
% 2.06/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/1.04  --abstr_ref_under                       []
% 2.06/1.04  
% 2.06/1.04  ------ SAT Options
% 2.06/1.04  
% 2.06/1.04  --sat_mode                              false
% 2.06/1.04  --sat_fm_restart_options                ""
% 2.06/1.04  --sat_gr_def                            false
% 2.06/1.04  --sat_epr_types                         true
% 2.06/1.04  --sat_non_cyclic_types                  false
% 2.06/1.04  --sat_finite_models                     false
% 2.06/1.04  --sat_fm_lemmas                         false
% 2.06/1.04  --sat_fm_prep                           false
% 2.06/1.04  --sat_fm_uc_incr                        true
% 2.06/1.04  --sat_out_model                         small
% 2.06/1.04  --sat_out_clauses                       false
% 2.06/1.04  
% 2.06/1.04  ------ QBF Options
% 2.06/1.04  
% 2.06/1.04  --qbf_mode                              false
% 2.06/1.04  --qbf_elim_univ                         false
% 2.06/1.04  --qbf_dom_inst                          none
% 2.06/1.04  --qbf_dom_pre_inst                      false
% 2.06/1.04  --qbf_sk_in                             false
% 2.06/1.04  --qbf_pred_elim                         true
% 2.06/1.04  --qbf_split                             512
% 2.06/1.04  
% 2.06/1.04  ------ BMC1 Options
% 2.06/1.04  
% 2.06/1.04  --bmc1_incremental                      false
% 2.06/1.04  --bmc1_axioms                           reachable_all
% 2.06/1.04  --bmc1_min_bound                        0
% 2.06/1.04  --bmc1_max_bound                        -1
% 2.06/1.04  --bmc1_max_bound_default                -1
% 2.06/1.04  --bmc1_symbol_reachability              true
% 2.06/1.04  --bmc1_property_lemmas                  false
% 2.06/1.04  --bmc1_k_induction                      false
% 2.06/1.04  --bmc1_non_equiv_states                 false
% 2.06/1.04  --bmc1_deadlock                         false
% 2.06/1.04  --bmc1_ucm                              false
% 2.06/1.04  --bmc1_add_unsat_core                   none
% 2.06/1.04  --bmc1_unsat_core_children              false
% 2.06/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/1.04  --bmc1_out_stat                         full
% 2.06/1.04  --bmc1_ground_init                      false
% 2.06/1.04  --bmc1_pre_inst_next_state              false
% 2.06/1.04  --bmc1_pre_inst_state                   false
% 2.06/1.04  --bmc1_pre_inst_reach_state             false
% 2.06/1.04  --bmc1_out_unsat_core                   false
% 2.06/1.04  --bmc1_aig_witness_out                  false
% 2.06/1.04  --bmc1_verbose                          false
% 2.06/1.04  --bmc1_dump_clauses_tptp                false
% 2.06/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.06/1.04  --bmc1_dump_file                        -
% 2.06/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.06/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.06/1.04  --bmc1_ucm_extend_mode                  1
% 2.06/1.04  --bmc1_ucm_init_mode                    2
% 2.06/1.04  --bmc1_ucm_cone_mode                    none
% 2.06/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.06/1.04  --bmc1_ucm_relax_model                  4
% 2.06/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.06/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/1.04  --bmc1_ucm_layered_model                none
% 2.06/1.04  --bmc1_ucm_max_lemma_size               10
% 2.06/1.04  
% 2.06/1.04  ------ AIG Options
% 2.06/1.04  
% 2.06/1.04  --aig_mode                              false
% 2.06/1.04  
% 2.06/1.04  ------ Instantiation Options
% 2.06/1.04  
% 2.06/1.04  --instantiation_flag                    true
% 2.06/1.04  --inst_sos_flag                         false
% 2.06/1.04  --inst_sos_phase                        true
% 2.06/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/1.04  --inst_lit_sel_side                     none
% 2.06/1.04  --inst_solver_per_active                1400
% 2.06/1.04  --inst_solver_calls_frac                1.
% 2.06/1.04  --inst_passive_queue_type               priority_queues
% 2.06/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/1.04  --inst_passive_queues_freq              [25;2]
% 2.06/1.04  --inst_dismatching                      true
% 2.06/1.04  --inst_eager_unprocessed_to_passive     true
% 2.06/1.04  --inst_prop_sim_given                   true
% 2.06/1.04  --inst_prop_sim_new                     false
% 2.06/1.04  --inst_subs_new                         false
% 2.06/1.04  --inst_eq_res_simp                      false
% 2.06/1.04  --inst_subs_given                       false
% 2.06/1.04  --inst_orphan_elimination               true
% 2.06/1.04  --inst_learning_loop_flag               true
% 2.06/1.04  --inst_learning_start                   3000
% 2.06/1.04  --inst_learning_factor                  2
% 2.06/1.04  --inst_start_prop_sim_after_learn       3
% 2.06/1.04  --inst_sel_renew                        solver
% 2.06/1.04  --inst_lit_activity_flag                true
% 2.06/1.04  --inst_restr_to_given                   false
% 2.06/1.04  --inst_activity_threshold               500
% 2.06/1.04  --inst_out_proof                        true
% 2.06/1.04  
% 2.06/1.04  ------ Resolution Options
% 2.06/1.04  
% 2.06/1.04  --resolution_flag                       false
% 2.06/1.04  --res_lit_sel                           adaptive
% 2.06/1.04  --res_lit_sel_side                      none
% 2.06/1.04  --res_ordering                          kbo
% 2.06/1.04  --res_to_prop_solver                    active
% 2.06/1.04  --res_prop_simpl_new                    false
% 2.06/1.04  --res_prop_simpl_given                  true
% 2.06/1.04  --res_passive_queue_type                priority_queues
% 2.06/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/1.04  --res_passive_queues_freq               [15;5]
% 2.06/1.04  --res_forward_subs                      full
% 2.06/1.04  --res_backward_subs                     full
% 2.06/1.04  --res_forward_subs_resolution           true
% 2.06/1.04  --res_backward_subs_resolution          true
% 2.06/1.04  --res_orphan_elimination                true
% 2.06/1.04  --res_time_limit                        2.
% 2.06/1.04  --res_out_proof                         true
% 2.06/1.04  
% 2.06/1.04  ------ Superposition Options
% 2.06/1.04  
% 2.06/1.04  --superposition_flag                    true
% 2.06/1.04  --sup_passive_queue_type                priority_queues
% 2.06/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.06/1.04  --demod_completeness_check              fast
% 2.06/1.04  --demod_use_ground                      true
% 2.06/1.04  --sup_to_prop_solver                    passive
% 2.06/1.04  --sup_prop_simpl_new                    true
% 2.06/1.04  --sup_prop_simpl_given                  true
% 2.06/1.04  --sup_fun_splitting                     false
% 2.06/1.04  --sup_smt_interval                      50000
% 2.06/1.04  
% 2.06/1.04  ------ Superposition Simplification Setup
% 2.06/1.04  
% 2.06/1.04  --sup_indices_passive                   []
% 2.06/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.04  --sup_full_bw                           [BwDemod]
% 2.06/1.04  --sup_immed_triv                        [TrivRules]
% 2.06/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.04  --sup_immed_bw_main                     []
% 2.06/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/1.04  
% 2.06/1.04  ------ Combination Options
% 2.06/1.04  
% 2.06/1.04  --comb_res_mult                         3
% 2.06/1.04  --comb_sup_mult                         2
% 2.06/1.04  --comb_inst_mult                        10
% 2.06/1.04  
% 2.06/1.04  ------ Debug Options
% 2.06/1.04  
% 2.06/1.04  --dbg_backtrace                         false
% 2.06/1.04  --dbg_dump_prop_clauses                 false
% 2.06/1.04  --dbg_dump_prop_clauses_file            -
% 2.06/1.04  --dbg_out_stat                          false
% 2.06/1.04  
% 2.06/1.04  
% 2.06/1.04  
% 2.06/1.04  
% 2.06/1.04  ------ Proving...
% 2.06/1.04  
% 2.06/1.04  
% 2.06/1.04  % SZS status Theorem for theBenchmark.p
% 2.06/1.04  
% 2.06/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.06/1.04  
% 2.06/1.04  fof(f19,conjecture,(
% 2.06/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.06/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.04  
% 2.06/1.04  fof(f20,negated_conjecture,(
% 2.06/1.04    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.06/1.04    inference(negated_conjecture,[],[f19])).
% 2.06/1.04  
% 2.06/1.04  fof(f41,plain,(
% 2.06/1.04    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.06/1.04    inference(ennf_transformation,[],[f20])).
% 2.06/1.04  
% 2.06/1.04  fof(f42,plain,(
% 2.06/1.04    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.06/1.04    inference(flattening,[],[f41])).
% 2.06/1.04  
% 2.06/1.04  fof(f46,plain,(
% 2.06/1.04    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.06/1.04    introduced(choice_axiom,[])).
% 2.06/1.04  
% 2.06/1.04  fof(f47,plain,(
% 2.06/1.04    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.06/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f46])).
% 2.06/1.04  
% 2.06/1.04  fof(f78,plain,(
% 2.06/1.04    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.06/1.04    inference(cnf_transformation,[],[f47])).
% 2.06/1.04  
% 2.06/1.04  fof(f15,axiom,(
% 2.06/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.06/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.04  
% 2.06/1.04  fof(f36,plain,(
% 2.06/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/1.04    inference(ennf_transformation,[],[f15])).
% 2.06/1.04  
% 2.06/1.04  fof(f67,plain,(
% 2.06/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/1.04    inference(cnf_transformation,[],[f36])).
% 2.06/1.04  
% 2.06/1.04  fof(f18,axiom,(
% 2.06/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.06/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.04  
% 2.06/1.04  fof(f39,plain,(
% 2.06/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/1.04    inference(ennf_transformation,[],[f18])).
% 2.06/1.04  
% 2.06/1.04  fof(f40,plain,(
% 2.06/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/1.04    inference(flattening,[],[f39])).
% 2.06/1.04  
% 2.06/1.04  fof(f45,plain,(
% 2.06/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/1.04    inference(nnf_transformation,[],[f40])).
% 2.06/1.04  
% 2.06/1.04  fof(f70,plain,(
% 2.06/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/1.04    inference(cnf_transformation,[],[f45])).
% 2.06/1.04  
% 2.06/1.04  fof(f77,plain,(
% 2.06/1.04    v1_funct_2(sK2,sK0,sK1)),
% 2.06/1.04    inference(cnf_transformation,[],[f47])).
% 2.06/1.04  
% 2.06/1.04  fof(f9,axiom,(
% 2.06/1.04    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.06/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.04  
% 2.06/1.04  fof(f27,plain,(
% 2.06/1.04    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.06/1.04    inference(ennf_transformation,[],[f9])).
% 2.06/1.04  
% 2.06/1.04  fof(f28,plain,(
% 2.06/1.04    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.06/1.04    inference(flattening,[],[f27])).
% 2.06/1.04  
% 2.06/1.04  fof(f59,plain,(
% 2.06/1.04    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/1.04    inference(cnf_transformation,[],[f28])).
% 2.06/1.04  
% 2.06/1.04  fof(f12,axiom,(
% 2.06/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.06/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.04  
% 2.06/1.04  fof(f33,plain,(
% 2.06/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/1.04    inference(ennf_transformation,[],[f12])).
% 2.06/1.04  
% 2.06/1.04  fof(f64,plain,(
% 2.06/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/1.04    inference(cnf_transformation,[],[f33])).
% 2.06/1.04  
% 2.06/1.04  fof(f72,plain,(
% 2.06/1.04    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/1.04    inference(cnf_transformation,[],[f45])).
% 2.06/1.04  
% 2.06/1.04  fof(f81,plain,(
% 2.06/1.04    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.06/1.04    inference(cnf_transformation,[],[f47])).
% 2.06/1.04  
% 2.06/1.04  fof(f76,plain,(
% 2.06/1.04    v1_funct_1(sK2)),
% 2.06/1.04    inference(cnf_transformation,[],[f47])).
% 2.06/1.04  
% 2.06/1.04  fof(f11,axiom,(
% 2.06/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.06/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.04  
% 2.06/1.04  fof(f31,plain,(
% 2.06/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.06/1.04    inference(ennf_transformation,[],[f11])).
% 2.06/1.04  
% 2.06/1.04  fof(f32,plain,(
% 2.06/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.06/1.04    inference(flattening,[],[f31])).
% 2.06/1.04  
% 2.06/1.04  fof(f63,plain,(
% 2.06/1.04    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/1.04    inference(cnf_transformation,[],[f32])).
% 2.06/1.04  
% 2.06/1.04  fof(f10,axiom,(
% 2.06/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.06/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.04  
% 2.06/1.04  fof(f29,plain,(
% 2.06/1.04    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.06/1.04    inference(ennf_transformation,[],[f10])).
% 2.06/1.04  
% 2.06/1.04  fof(f30,plain,(
% 2.06/1.04    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.06/1.04    inference(flattening,[],[f29])).
% 2.06/1.04  
% 2.06/1.04  fof(f61,plain,(
% 2.06/1.04    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/1.04    inference(cnf_transformation,[],[f30])).
% 2.06/1.04  
% 2.06/1.04  fof(f79,plain,(
% 2.06/1.04    v2_funct_1(sK2)),
% 2.06/1.04    inference(cnf_transformation,[],[f47])).
% 2.06/1.04  
% 2.06/1.04  fof(f17,axiom,(
% 2.06/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 2.06/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.04  
% 2.06/1.04  fof(f38,plain,(
% 2.06/1.04    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/1.04    inference(ennf_transformation,[],[f17])).
% 2.06/1.04  
% 2.06/1.04  fof(f69,plain,(
% 2.06/1.04    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/1.04    inference(cnf_transformation,[],[f38])).
% 2.06/1.04  
% 2.06/1.04  fof(f14,axiom,(
% 2.06/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.06/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.04  
% 2.06/1.04  fof(f35,plain,(
% 2.06/1.04    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/1.04    inference(ennf_transformation,[],[f14])).
% 2.06/1.04  
% 2.06/1.04  fof(f66,plain,(
% 2.06/1.04    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/1.04    inference(cnf_transformation,[],[f35])).
% 2.06/1.04  
% 2.06/1.04  fof(f16,axiom,(
% 2.06/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.06/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.04  
% 2.06/1.04  fof(f37,plain,(
% 2.06/1.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/1.04    inference(ennf_transformation,[],[f16])).
% 2.06/1.04  
% 2.06/1.04  fof(f68,plain,(
% 2.06/1.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/1.04    inference(cnf_transformation,[],[f37])).
% 2.06/1.04  
% 2.06/1.04  fof(f80,plain,(
% 2.06/1.04    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.06/1.04    inference(cnf_transformation,[],[f47])).
% 2.06/1.04  
% 2.06/1.04  fof(f60,plain,(
% 2.06/1.04    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/1.04    inference(cnf_transformation,[],[f28])).
% 2.06/1.04  
% 2.06/1.04  fof(f7,axiom,(
% 2.06/1.04    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.06/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.04  
% 2.06/1.04  fof(f26,plain,(
% 2.06/1.04    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.06/1.04    inference(ennf_transformation,[],[f7])).
% 2.06/1.04  
% 2.06/1.04  fof(f55,plain,(
% 2.06/1.04    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.06/1.05    inference(cnf_transformation,[],[f26])).
% 2.06/1.05  
% 2.06/1.05  fof(f4,axiom,(
% 2.06/1.05    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.06/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.05  
% 2.06/1.05  fof(f53,plain,(
% 2.06/1.05    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.06/1.05    inference(cnf_transformation,[],[f4])).
% 2.06/1.05  
% 2.06/1.05  fof(f8,axiom,(
% 2.06/1.05    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.06/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.05  
% 2.06/1.05  fof(f58,plain,(
% 2.06/1.05    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.06/1.05    inference(cnf_transformation,[],[f8])).
% 2.06/1.05  
% 2.06/1.05  fof(f62,plain,(
% 2.06/1.05    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/1.05    inference(cnf_transformation,[],[f32])).
% 2.06/1.05  
% 2.06/1.05  fof(f73,plain,(
% 2.06/1.05    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/1.05    inference(cnf_transformation,[],[f45])).
% 2.06/1.05  
% 2.06/1.05  fof(f87,plain,(
% 2.06/1.05    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.06/1.05    inference(equality_resolution,[],[f73])).
% 2.06/1.05  
% 2.06/1.05  fof(f3,axiom,(
% 2.06/1.05    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.06/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/1.05  
% 2.06/1.05  fof(f43,plain,(
% 2.06/1.05    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.06/1.05    inference(nnf_transformation,[],[f3])).
% 2.06/1.05  
% 2.06/1.05  fof(f44,plain,(
% 2.06/1.05    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.06/1.05    inference(flattening,[],[f43])).
% 2.06/1.05  
% 2.06/1.05  fof(f51,plain,(
% 2.06/1.05    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.06/1.05    inference(cnf_transformation,[],[f44])).
% 2.06/1.05  
% 2.06/1.05  fof(f83,plain,(
% 2.06/1.05    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.06/1.05    inference(equality_resolution,[],[f51])).
% 2.06/1.05  
% 2.06/1.05  cnf(c_31,negated_conjecture,
% 2.06/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.06/1.05      inference(cnf_transformation,[],[f78]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1093,plain,
% 2.06/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_19,plain,
% 2.06/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/1.05      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.06/1.05      inference(cnf_transformation,[],[f67]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1096,plain,
% 2.06/1.05      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.06/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4180,plain,
% 2.06/1.05      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_1093,c_1096]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_27,plain,
% 2.06/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 2.06/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/1.05      | k1_relset_1(X1,X2,X0) = X1
% 2.06/1.05      | k1_xboole_0 = X2 ),
% 2.06/1.05      inference(cnf_transformation,[],[f70]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_32,negated_conjecture,
% 2.06/1.05      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.06/1.05      inference(cnf_transformation,[],[f77]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_455,plain,
% 2.06/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/1.05      | k1_relset_1(X1,X2,X0) = X1
% 2.06/1.05      | sK0 != X1
% 2.06/1.05      | sK1 != X2
% 2.06/1.05      | sK2 != X0
% 2.06/1.05      | k1_xboole_0 = X2 ),
% 2.06/1.05      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_456,plain,
% 2.06/1.05      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.06/1.05      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.06/1.05      | k1_xboole_0 = sK1 ),
% 2.06/1.05      inference(unflattening,[status(thm)],[c_455]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_458,plain,
% 2.06/1.05      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.06/1.05      inference(global_propositional_subsumption,
% 2.06/1.05                [status(thm)],
% 2.06/1.05                [c_456,c_31]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4371,plain,
% 2.06/1.05      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_4180,c_458]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_12,plain,
% 2.06/1.05      ( ~ v1_relat_1(X0)
% 2.06/1.05      | k1_relat_1(X0) != k1_xboole_0
% 2.06/1.05      | k1_xboole_0 = X0 ),
% 2.06/1.05      inference(cnf_transformation,[],[f59]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1102,plain,
% 2.06/1.05      ( k1_relat_1(X0) != k1_xboole_0
% 2.06/1.05      | k1_xboole_0 = X0
% 2.06/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4383,plain,
% 2.06/1.05      ( sK0 != k1_xboole_0
% 2.06/1.05      | sK1 = k1_xboole_0
% 2.06/1.05      | sK2 = k1_xboole_0
% 2.06/1.05      | v1_relat_1(sK2) != iProver_top ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_4371,c_1102]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_36,plain,
% 2.06/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_16,plain,
% 2.06/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/1.05      | v1_relat_1(X0) ),
% 2.06/1.05      inference(cnf_transformation,[],[f64]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1324,plain,
% 2.06/1.05      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.06/1.05      | v1_relat_1(sK2) ),
% 2.06/1.05      inference(instantiation,[status(thm)],[c_16]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1325,plain,
% 2.06/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.06/1.05      | v1_relat_1(sK2) = iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_25,plain,
% 2.06/1.05      ( v1_funct_2(X0,X1,X2)
% 2.06/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/1.05      | k1_relset_1(X1,X2,X0) != X1
% 2.06/1.05      | k1_xboole_0 = X2 ),
% 2.06/1.05      inference(cnf_transformation,[],[f72]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_28,negated_conjecture,
% 2.06/1.05      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.06/1.05      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.06/1.05      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.06/1.05      inference(cnf_transformation,[],[f81]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_439,plain,
% 2.06/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/1.05      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.06/1.05      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.06/1.05      | k1_relset_1(X1,X2,X0) != X1
% 2.06/1.05      | k2_funct_1(sK2) != X0
% 2.06/1.05      | sK0 != X2
% 2.06/1.05      | sK1 != X1
% 2.06/1.05      | k1_xboole_0 = X2 ),
% 2.06/1.05      inference(resolution_lifted,[status(thm)],[c_25,c_28]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_440,plain,
% 2.06/1.05      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.06/1.05      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.06/1.05      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.06/1.05      | k1_xboole_0 = sK0 ),
% 2.06/1.05      inference(unflattening,[status(thm)],[c_439]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1085,plain,
% 2.06/1.05      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.06/1.05      | k1_xboole_0 = sK0
% 2.06/1.05      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.06/1.05      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_33,negated_conjecture,
% 2.06/1.05      ( v1_funct_1(sK2) ),
% 2.06/1.05      inference(cnf_transformation,[],[f76]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_34,plain,
% 2.06/1.05      ( v1_funct_1(sK2) = iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_441,plain,
% 2.06/1.05      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.06/1.05      | k1_xboole_0 = sK0
% 2.06/1.05      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.06/1.05      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_14,plain,
% 2.06/1.05      ( ~ v1_funct_1(X0)
% 2.06/1.05      | v1_funct_1(k2_funct_1(X0))
% 2.06/1.05      | ~ v1_relat_1(X0) ),
% 2.06/1.05      inference(cnf_transformation,[],[f63]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1310,plain,
% 2.06/1.05      ( v1_funct_1(k2_funct_1(sK2))
% 2.06/1.05      | ~ v1_funct_1(sK2)
% 2.06/1.05      | ~ v1_relat_1(sK2) ),
% 2.06/1.05      inference(instantiation,[status(thm)],[c_14]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1311,plain,
% 2.06/1.05      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.06/1.05      | v1_funct_1(sK2) != iProver_top
% 2.06/1.05      | v1_relat_1(sK2) != iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_1310]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1374,plain,
% 2.06/1.05      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.06/1.05      | k1_xboole_0 = sK0
% 2.06/1.05      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1 ),
% 2.06/1.05      inference(global_propositional_subsumption,
% 2.06/1.05                [status(thm)],
% 2.06/1.05                [c_1085,c_34,c_36,c_441,c_1311,c_1325]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1375,plain,
% 2.06/1.05      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.06/1.05      | k1_xboole_0 = sK0
% 2.06/1.05      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.06/1.05      inference(renaming,[status(thm)],[c_1374]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_13,plain,
% 2.06/1.05      ( ~ v1_funct_1(X0)
% 2.06/1.05      | ~ v2_funct_1(X0)
% 2.06/1.05      | ~ v1_relat_1(X0)
% 2.06/1.05      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.06/1.05      inference(cnf_transformation,[],[f61]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_30,negated_conjecture,
% 2.06/1.05      ( v2_funct_1(sK2) ),
% 2.06/1.05      inference(cnf_transformation,[],[f79]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_336,plain,
% 2.06/1.05      ( ~ v1_funct_1(X0)
% 2.06/1.05      | ~ v1_relat_1(X0)
% 2.06/1.05      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.06/1.05      | sK2 != X0 ),
% 2.06/1.05      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_337,plain,
% 2.06/1.05      ( ~ v1_funct_1(sK2)
% 2.06/1.05      | ~ v1_relat_1(sK2)
% 2.06/1.05      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.06/1.05      inference(unflattening,[status(thm)],[c_336]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_339,plain,
% 2.06/1.05      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.06/1.05      inference(global_propositional_subsumption,
% 2.06/1.05                [status(thm)],
% 2.06/1.05                [c_337,c_33]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1090,plain,
% 2.06/1.05      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 2.06/1.05      | v1_relat_1(sK2) != iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1328,plain,
% 2.06/1.05      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.06/1.05      inference(global_propositional_subsumption,
% 2.06/1.05                [status(thm)],
% 2.06/1.05                [c_1090,c_33,c_31,c_337,c_1324]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1378,plain,
% 2.06/1.05      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != sK1
% 2.06/1.05      | sK0 = k1_xboole_0
% 2.06/1.05      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.06/1.05      inference(light_normalisation,[status(thm)],[c_1375,c_1328]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_21,plain,
% 2.06/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/1.05      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 2.06/1.05      inference(cnf_transformation,[],[f69]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1094,plain,
% 2.06/1.05      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
% 2.06/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3167,plain,
% 2.06/1.05      ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_1093,c_1094]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_18,plain,
% 2.06/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/1.05      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.06/1.05      inference(cnf_transformation,[],[f66]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1097,plain,
% 2.06/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.06/1.05      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3200,plain,
% 2.06/1.05      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 2.06/1.05      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_3167,c_1097]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_20,plain,
% 2.06/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/1.05      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.06/1.05      inference(cnf_transformation,[],[f68]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1095,plain,
% 2.06/1.05      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.06/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3518,plain,
% 2.06/1.05      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_1093,c_1095]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_29,negated_conjecture,
% 2.06/1.05      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.06/1.05      inference(cnf_transformation,[],[f80]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3530,plain,
% 2.06/1.05      ( k2_relat_1(sK2) = sK1 ),
% 2.06/1.05      inference(light_normalisation,[status(thm)],[c_3518,c_29]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_11,plain,
% 2.06/1.05      ( ~ v1_relat_1(X0)
% 2.06/1.05      | k2_relat_1(X0) != k1_xboole_0
% 2.06/1.05      | k1_xboole_0 = X0 ),
% 2.06/1.05      inference(cnf_transformation,[],[f60]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1103,plain,
% 2.06/1.05      ( k2_relat_1(X0) != k1_xboole_0
% 2.06/1.05      | k1_xboole_0 = X0
% 2.06/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3651,plain,
% 2.06/1.05      ( sK1 != k1_xboole_0
% 2.06/1.05      | sK2 = k1_xboole_0
% 2.06/1.05      | v1_relat_1(sK2) != iProver_top ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_3530,c_1103]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3652,plain,
% 2.06/1.05      ( ~ v1_relat_1(sK2) | sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.06/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_3651]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3705,plain,
% 2.06/1.05      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 2.06/1.05      inference(global_propositional_subsumption,
% 2.06/1.05                [status(thm)],
% 2.06/1.05                [c_3651,c_31,c_1324,c_3652]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3706,plain,
% 2.06/1.05      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.06/1.05      inference(renaming,[status(thm)],[c_3705]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3856,plain,
% 2.06/1.05      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.06/1.05      inference(global_propositional_subsumption,
% 2.06/1.05                [status(thm)],
% 2.06/1.05                [c_3200,c_36]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4181,plain,
% 2.06/1.05      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_3856,c_1096]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1099,plain,
% 2.06/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.06/1.05      | v1_relat_1(X0) = iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_2006,plain,
% 2.06/1.05      ( v1_relat_1(sK2) = iProver_top ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_1093,c_1099]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_8,plain,
% 2.06/1.05      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.06/1.05      inference(cnf_transformation,[],[f55]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1104,plain,
% 2.06/1.05      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 2.06/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_2030,plain,
% 2.06/1.05      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_2006,c_1104]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3641,plain,
% 2.06/1.05      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 2.06/1.05      inference(demodulation,[status(thm)],[c_3530,c_2030]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4193,plain,
% 2.06/1.05      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 ),
% 2.06/1.05      inference(light_normalisation,[status(thm)],[c_4181,c_3641]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4631,plain,
% 2.06/1.05      ( sK2 = k1_xboole_0 ),
% 2.06/1.05      inference(global_propositional_subsumption,
% 2.06/1.05                [status(thm)],
% 2.06/1.05                [c_4383,c_36,c_1325,c_1378,c_3200,c_3706,c_4193]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4636,plain,
% 2.06/1.05      ( k1_relset_1(sK1,sK0,k4_relat_1(k1_xboole_0)) = sK1 ),
% 2.06/1.05      inference(demodulation,[status(thm)],[c_4631,c_4193]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4663,plain,
% 2.06/1.05      ( k2_relset_1(sK0,sK1,k1_xboole_0) = sK1 ),
% 2.06/1.05      inference(demodulation,[status(thm)],[c_4631,c_29]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_5,plain,
% 2.06/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.06/1.05      inference(cnf_transformation,[],[f53]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1106,plain,
% 2.06/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3515,plain,
% 2.06/1.05      ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_1106,c_1095]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_9,plain,
% 2.06/1.05      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.06/1.05      inference(cnf_transformation,[],[f58]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3541,plain,
% 2.06/1.05      ( k2_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 2.06/1.05      inference(light_normalisation,[status(thm)],[c_3515,c_9]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4665,plain,
% 2.06/1.05      ( sK1 = k1_xboole_0 ),
% 2.06/1.05      inference(demodulation,[status(thm)],[c_4663,c_3541]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_2599,plain,
% 2.06/1.05      ( k2_relat_1(sK2) != k1_xboole_0
% 2.06/1.05      | k4_relat_1(sK2) = k1_xboole_0
% 2.06/1.05      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_2030,c_1102]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3640,plain,
% 2.06/1.05      ( k4_relat_1(sK2) = k1_xboole_0
% 2.06/1.05      | sK1 != k1_xboole_0
% 2.06/1.05      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.06/1.05      inference(demodulation,[status(thm)],[c_3530,c_2599]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_15,plain,
% 2.06/1.05      ( ~ v1_funct_1(X0)
% 2.06/1.05      | ~ v1_relat_1(X0)
% 2.06/1.05      | v1_relat_1(k2_funct_1(X0)) ),
% 2.06/1.05      inference(cnf_transformation,[],[f62]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1100,plain,
% 2.06/1.05      ( v1_funct_1(X0) != iProver_top
% 2.06/1.05      | v1_relat_1(X0) != iProver_top
% 2.06/1.05      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3291,plain,
% 2.06/1.05      ( v1_funct_1(sK2) != iProver_top
% 2.06/1.05      | v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 2.06/1.05      | v1_relat_1(sK2) != iProver_top ),
% 2.06/1.05      inference(superposition,[status(thm)],[c_1328,c_1100]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3710,plain,
% 2.06/1.05      ( sK1 != k1_xboole_0 | k4_relat_1(sK2) = k1_xboole_0 ),
% 2.06/1.05      inference(global_propositional_subsumption,
% 2.06/1.05                [status(thm)],
% 2.06/1.05                [c_3640,c_34,c_36,c_1325,c_3291]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3711,plain,
% 2.06/1.05      ( k4_relat_1(sK2) = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 2.06/1.05      inference(renaming,[status(thm)],[c_3710]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4644,plain,
% 2.06/1.05      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 2.06/1.05      inference(demodulation,[status(thm)],[c_4631,c_3711]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4707,plain,
% 2.06/1.05      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
% 2.06/1.05      | k1_xboole_0 != k1_xboole_0 ),
% 2.06/1.05      inference(light_normalisation,[status(thm)],[c_4644,c_4665]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4708,plain,
% 2.06/1.05      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.06/1.05      inference(equality_resolution_simp,[status(thm)],[c_4707]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4742,plain,
% 2.06/1.05      ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) = k1_xboole_0 ),
% 2.06/1.05      inference(light_normalisation,[status(thm)],[c_4636,c_4665,c_4708]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_24,plain,
% 2.06/1.05      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.06/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.06/1.05      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.06/1.05      inference(cnf_transformation,[],[f87]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_407,plain,
% 2.06/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.06/1.05      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.06/1.05      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.06/1.05      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.06/1.05      | k2_funct_1(sK2) != X0
% 2.06/1.05      | sK0 != X1
% 2.06/1.05      | sK1 != k1_xboole_0 ),
% 2.06/1.05      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_408,plain,
% 2.06/1.05      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.06/1.05      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.06/1.05      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.06/1.05      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.06/1.05      | sK1 != k1_xboole_0 ),
% 2.06/1.05      inference(unflattening,[status(thm)],[c_407]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1087,plain,
% 2.06/1.05      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.06/1.05      | sK1 != k1_xboole_0
% 2.06/1.05      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.06/1.05      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.06/1.05      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_3,plain,
% 2.06/1.05      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.06/1.05      inference(cnf_transformation,[],[f83]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1243,plain,
% 2.06/1.05      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.06/1.05      | sK1 != k1_xboole_0
% 2.06/1.05      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.06/1.05      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.06/1.05      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.06/1.05      inference(demodulation,[status(thm)],[c_1087,c_3]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1551,plain,
% 2.06/1.05      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.06/1.05      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.06/1.05      | sK1 != k1_xboole_0
% 2.06/1.05      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.06/1.05      inference(global_propositional_subsumption,
% 2.06/1.05                [status(thm)],
% 2.06/1.05                [c_1243,c_34,c_36,c_1311,c_1325]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1552,plain,
% 2.06/1.05      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.06/1.05      | sK1 != k1_xboole_0
% 2.06/1.05      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.06/1.05      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.06/1.05      inference(renaming,[status(thm)],[c_1551]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_1555,plain,
% 2.06/1.05      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(sK2)) != k1_xboole_0
% 2.06/1.05      | sK1 != k1_xboole_0
% 2.06/1.05      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.06/1.05      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.06/1.05      inference(light_normalisation,[status(thm)],[c_1552,c_1328]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4655,plain,
% 2.06/1.05      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) != k1_xboole_0
% 2.06/1.05      | sK1 != k1_xboole_0
% 2.06/1.05      | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.06/1.05      | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.06/1.05      inference(demodulation,[status(thm)],[c_4631,c_1555]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4689,plain,
% 2.06/1.05      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) != k1_xboole_0
% 2.06/1.05      | k1_xboole_0 != k1_xboole_0
% 2.06/1.05      | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.06/1.05      | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.06/1.05      inference(light_normalisation,[status(thm)],[c_4655,c_4665]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4690,plain,
% 2.06/1.05      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) != k1_xboole_0
% 2.06/1.05      | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.06/1.05      | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.06/1.05      inference(equality_resolution_simp,[status(thm)],[c_4689]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4694,plain,
% 2.06/1.05      ( k1_relset_1(k1_xboole_0,sK0,k4_relat_1(k1_xboole_0)) != k1_xboole_0
% 2.06/1.05      | m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.06/1.05      inference(demodulation,[status(thm)],[c_4690,c_3]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4711,plain,
% 2.06/1.05      ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0
% 2.06/1.05      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.06/1.05      inference(demodulation,[status(thm)],[c_4708,c_4694]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4744,plain,
% 2.06/1.05      ( k1_xboole_0 != k1_xboole_0
% 2.06/1.05      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.06/1.05      inference(demodulation,[status(thm)],[c_4742,c_4711]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_4746,plain,
% 2.06/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.06/1.05      inference(equality_resolution_simp,[status(thm)],[c_4744]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_99,plain,
% 2.06/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.06/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(c_101,plain,
% 2.06/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.06/1.05      inference(instantiation,[status(thm)],[c_99]) ).
% 2.06/1.05  
% 2.06/1.05  cnf(contradiction,plain,
% 2.06/1.05      ( $false ),
% 2.06/1.05      inference(minisat,[status(thm)],[c_4746,c_101]) ).
% 2.06/1.05  
% 2.06/1.05  
% 2.06/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.06/1.05  
% 2.06/1.05  ------                               Statistics
% 2.06/1.05  
% 2.06/1.05  ------ General
% 2.06/1.05  
% 2.06/1.05  abstr_ref_over_cycles:                  0
% 2.06/1.05  abstr_ref_under_cycles:                 0
% 2.06/1.05  gc_basic_clause_elim:                   0
% 2.06/1.05  forced_gc_time:                         0
% 2.06/1.05  parsing_time:                           0.013
% 2.06/1.05  unif_index_cands_time:                  0.
% 2.06/1.05  unif_index_add_time:                    0.
% 2.06/1.05  orderings_time:                         0.
% 2.06/1.05  out_proof_time:                         0.01
% 2.06/1.05  total_time:                             0.15
% 2.06/1.05  num_of_symbols:                         51
% 2.06/1.05  num_of_terms:                           4684
% 2.06/1.05  
% 2.06/1.05  ------ Preprocessing
% 2.06/1.05  
% 2.06/1.05  num_of_splits:                          0
% 2.06/1.05  num_of_split_atoms:                     0
% 2.06/1.05  num_of_reused_defs:                     0
% 2.06/1.05  num_eq_ax_congr_red:                    20
% 2.06/1.05  num_of_sem_filtered_clauses:            1
% 2.06/1.05  num_of_subtypes:                        0
% 2.06/1.05  monotx_restored_types:                  0
% 2.06/1.05  sat_num_of_epr_types:                   0
% 2.06/1.05  sat_num_of_non_cyclic_types:            0
% 2.06/1.05  sat_guarded_non_collapsed_types:        0
% 2.06/1.05  num_pure_diseq_elim:                    0
% 2.06/1.05  simp_replaced_by:                       0
% 2.06/1.05  res_preprocessed:                       154
% 2.06/1.05  prep_upred:                             0
% 2.06/1.05  prep_unflattend:                        34
% 2.06/1.05  smt_new_axioms:                         0
% 2.06/1.05  pred_elim_cands:                        3
% 2.06/1.05  pred_elim:                              3
% 2.06/1.05  pred_elim_cl:                           3
% 2.06/1.05  pred_elim_cycles:                       5
% 2.06/1.05  merged_defs:                            0
% 2.06/1.05  merged_defs_ncl:                        0
% 2.06/1.05  bin_hyper_res:                          0
% 2.06/1.05  prep_cycles:                            4
% 2.06/1.05  pred_elim_time:                         0.004
% 2.06/1.05  splitting_time:                         0.
% 2.06/1.05  sem_filter_time:                        0.
% 2.06/1.05  monotx_time:                            0.
% 2.06/1.05  subtype_inf_time:                       0.
% 2.06/1.05  
% 2.06/1.05  ------ Problem properties
% 2.06/1.05  
% 2.06/1.05  clauses:                                31
% 2.06/1.05  conjectures:                            3
% 2.06/1.05  epr:                                    1
% 2.06/1.05  horn:                                   28
% 2.06/1.05  ground:                                 13
% 2.06/1.05  unary:                                  8
% 2.06/1.05  binary:                                 12
% 2.06/1.05  lits:                                   72
% 2.06/1.05  lits_eq:                                37
% 2.06/1.05  fd_pure:                                0
% 2.06/1.05  fd_pseudo:                              0
% 2.06/1.05  fd_cond:                                4
% 2.06/1.05  fd_pseudo_cond:                         0
% 2.06/1.05  ac_symbols:                             0
% 2.06/1.05  
% 2.06/1.05  ------ Propositional Solver
% 2.06/1.05  
% 2.06/1.05  prop_solver_calls:                      27
% 2.06/1.05  prop_fast_solver_calls:                 940
% 2.06/1.05  smt_solver_calls:                       0
% 2.06/1.05  smt_fast_solver_calls:                  0
% 2.06/1.05  prop_num_of_clauses:                    1783
% 2.06/1.05  prop_preprocess_simplified:             6033
% 2.06/1.05  prop_fo_subsumed:                       19
% 2.06/1.05  prop_solver_time:                       0.
% 2.06/1.05  smt_solver_time:                        0.
% 2.06/1.05  smt_fast_solver_time:                   0.
% 2.06/1.05  prop_fast_solver_time:                  0.
% 2.06/1.05  prop_unsat_core_time:                   0.
% 2.06/1.05  
% 2.06/1.05  ------ QBF
% 2.06/1.05  
% 2.06/1.05  qbf_q_res:                              0
% 2.06/1.05  qbf_num_tautologies:                    0
% 2.06/1.05  qbf_prep_cycles:                        0
% 2.06/1.05  
% 2.06/1.05  ------ BMC1
% 2.06/1.05  
% 2.06/1.05  bmc1_current_bound:                     -1
% 2.06/1.05  bmc1_last_solved_bound:                 -1
% 2.06/1.05  bmc1_unsat_core_size:                   -1
% 2.06/1.05  bmc1_unsat_core_parents_size:           -1
% 2.06/1.05  bmc1_merge_next_fun:                    0
% 2.06/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.06/1.05  
% 2.06/1.05  ------ Instantiation
% 2.06/1.05  
% 2.06/1.05  inst_num_of_clauses:                    738
% 2.06/1.05  inst_num_in_passive:                    74
% 2.06/1.05  inst_num_in_active:                     312
% 2.06/1.05  inst_num_in_unprocessed:                352
% 2.06/1.05  inst_num_of_loops:                      340
% 2.06/1.05  inst_num_of_learning_restarts:          0
% 2.06/1.05  inst_num_moves_active_passive:          26
% 2.06/1.05  inst_lit_activity:                      0
% 2.06/1.05  inst_lit_activity_moves:                0
% 2.06/1.05  inst_num_tautologies:                   0
% 2.06/1.05  inst_num_prop_implied:                  0
% 2.06/1.05  inst_num_existing_simplified:           0
% 2.06/1.05  inst_num_eq_res_simplified:             0
% 2.06/1.05  inst_num_child_elim:                    0
% 2.06/1.05  inst_num_of_dismatching_blockings:      204
% 2.06/1.05  inst_num_of_non_proper_insts:           460
% 2.06/1.05  inst_num_of_duplicates:                 0
% 2.06/1.05  inst_inst_num_from_inst_to_res:         0
% 2.06/1.05  inst_dismatching_checking_time:         0.
% 2.06/1.05  
% 2.06/1.05  ------ Resolution
% 2.06/1.05  
% 2.06/1.05  res_num_of_clauses:                     0
% 2.06/1.05  res_num_in_passive:                     0
% 2.06/1.05  res_num_in_active:                      0
% 2.06/1.05  res_num_of_loops:                       158
% 2.06/1.05  res_forward_subset_subsumed:            19
% 2.06/1.05  res_backward_subset_subsumed:           2
% 2.06/1.05  res_forward_subsumed:                   0
% 2.06/1.05  res_backward_subsumed:                  0
% 2.06/1.05  res_forward_subsumption_resolution:     1
% 2.06/1.05  res_backward_subsumption_resolution:    0
% 2.06/1.05  res_clause_to_clause_subsumption:       190
% 2.06/1.05  res_orphan_elimination:                 0
% 2.06/1.05  res_tautology_del:                      56
% 2.06/1.05  res_num_eq_res_simplified:              0
% 2.06/1.05  res_num_sel_changes:                    0
% 2.06/1.05  res_moves_from_active_to_pass:          0
% 2.06/1.05  
% 2.06/1.05  ------ Superposition
% 2.06/1.05  
% 2.06/1.05  sup_time_total:                         0.
% 2.06/1.05  sup_time_generating:                    0.
% 2.06/1.05  sup_time_sim_full:                      0.
% 2.06/1.05  sup_time_sim_immed:                     0.
% 2.06/1.05  
% 2.06/1.05  sup_num_of_clauses:                     78
% 2.06/1.05  sup_num_in_active:                      32
% 2.06/1.05  sup_num_in_passive:                     46
% 2.06/1.05  sup_num_of_loops:                       67
% 2.06/1.05  sup_fw_superposition:                   51
% 2.06/1.05  sup_bw_superposition:                   32
% 2.06/1.05  sup_immediate_simplified:               58
% 2.06/1.05  sup_given_eliminated:                   0
% 2.06/1.05  comparisons_done:                       0
% 2.06/1.05  comparisons_avoided:                    8
% 2.06/1.05  
% 2.06/1.05  ------ Simplifications
% 2.06/1.05  
% 2.06/1.05  
% 2.06/1.05  sim_fw_subset_subsumed:                 4
% 2.06/1.05  sim_bw_subset_subsumed:                 2
% 2.06/1.05  sim_fw_subsumed:                        9
% 2.06/1.05  sim_bw_subsumed:                        2
% 2.06/1.05  sim_fw_subsumption_res:                 0
% 2.06/1.05  sim_bw_subsumption_res:                 0
% 2.06/1.05  sim_tautology_del:                      1
% 2.06/1.05  sim_eq_tautology_del:                   9
% 2.06/1.05  sim_eq_res_simp:                        4
% 2.06/1.05  sim_fw_demodulated:                     16
% 2.06/1.05  sim_bw_demodulated:                     38
% 2.06/1.05  sim_light_normalised:                   35
% 2.06/1.05  sim_joinable_taut:                      0
% 2.06/1.05  sim_joinable_simp:                      0
% 2.06/1.05  sim_ac_normalised:                      0
% 2.06/1.05  sim_smt_subsumption:                    0
% 2.06/1.05  
%------------------------------------------------------------------------------

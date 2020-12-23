%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:53 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :  153 (1842 expanded)
%              Number of clauses        :  100 ( 766 expanded)
%              Number of leaves         :   13 ( 319 expanded)
%              Depth                    :   21
%              Number of atoms          :  443 (8561 expanded)
%              Number of equality atoms :  203 (1834 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f31,plain,
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

fof(f32,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f31])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_594,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1070,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_599,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k3_relset_1(X1_46,X2_46,X0_46) = k4_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1066,plain,
    ( k3_relset_1(X0_46,X1_46,X2_46) = k4_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_1902,plain,
    ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1070,c_1066])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | m1_subset_1(k3_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1064,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
    | m1_subset_1(k3_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_2110,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1902,c_1064])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2247,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2110,c_29])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1065,plain,
    ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_2254,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2247,c_1065])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_607,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ v1_relat_1(X1_46)
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1058,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | v1_relat_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_1426,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1070,c_1058])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_606,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1495,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_1496,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1495])).

cnf(c_1538,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1426,c_1496])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_604,plain,
    ( ~ v1_relat_1(X0_46)
    | k1_relat_1(k4_relat_1(X0_46)) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1061,plain,
    ( k1_relat_1(k4_relat_1(X0_46)) = k2_relat_1(X0_46)
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_1544,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1538,c_1061])).

cnf(c_2259,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2254,c_1544])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_290,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_291,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_293,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_291,c_26])).

cnf(c_592,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_1072,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_1543,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1538,c_1072])).

cnf(c_15,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_21,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_463,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_584,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_463])).

cnf(c_1080,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_1711,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != sK1
    | sK0 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1543,c_1080])).

cnf(c_27,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_603,plain,
    ( ~ v1_funct_1(X0_46)
    | v1_funct_1(k2_funct_1(X0_46))
    | ~ v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1062,plain,
    ( v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(k2_funct_1(X0_46)) = iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_1758,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_1062])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_597,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k1_relset_1(X2_46,X1_46,k3_relset_1(X1_46,X2_46,X0_46)) = k2_relset_1(X1_46,X2_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1068,plain,
    ( k1_relset_1(X0_46,X1_46,k3_relset_1(X1_46,X0_46,X2_46)) = k2_relset_1(X1_46,X0_46,X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X0_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_2384,plain,
    ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) = k2_relset_1(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1070,c_1068])).

cnf(c_22,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_595,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2395,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2384,c_595,c_1902])).

cnf(c_2581,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1711,c_27,c_29,c_1426,c_1496,c_1758,c_2110,c_2395])).

cnf(c_2585,plain,
    ( k1_relset_1(sK1,k1_xboole_0,k4_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2581,c_2395])).

cnf(c_3493,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2259,c_2581,c_2585])).

cnf(c_19,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_489,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_21])).

cnf(c_490,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_582,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(subtyping,[status(esa)],[c_490])).

cnf(c_1081,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_676,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_602,plain,
    ( ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X0_46)
    | v1_relat_1(k2_funct_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1299,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_1300,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1299])).

cnf(c_1302,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_1303,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_1593,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1081,c_27,c_676,c_1300,c_1303,c_1426,c_1496])).

cnf(c_1710,plain,
    ( k1_relat_1(k4_relat_1(sK2)) != sK1
    | k2_relat_1(k4_relat_1(sK2)) != sK0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1543,c_1593])).

cnf(c_2275,plain,
    ( k2_relat_1(k4_relat_1(sK2)) != sK0
    | k1_relat_1(k4_relat_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1710,c_29,c_2110])).

cnf(c_2276,plain,
    ( k1_relat_1(k4_relat_1(sK2)) != sK1
    | k2_relat_1(k4_relat_1(sK2)) != sK0 ),
    inference(renaming,[status(thm)],[c_2275])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_605,plain,
    ( ~ v1_relat_1(X0_46)
    | k2_relat_1(k4_relat_1(X0_46)) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1060,plain,
    ( k2_relat_1(k4_relat_1(X0_46)) = k1_relat_1(X0_46)
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_1545,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1538,c_1060])).

cnf(c_2277,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1 ),
    inference(light_normalisation,[status(thm)],[c_2276,c_1544,c_1545])).

cnf(c_2587,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) != sK1 ),
    inference(demodulation,[status(thm)],[c_2581,c_2277])).

cnf(c_1898,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1070,c_1065])).

cnf(c_2592,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2581,c_1898])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_426,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_586,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_426])).

cnf(c_1078,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_2594,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2581,c_1078])).

cnf(c_2606,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2594])).

cnf(c_2596,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2581,c_1070])).

cnf(c_2609,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2606,c_2596])).

cnf(c_2611,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2592,c_2609])).

cnf(c_2621,plain,
    ( k2_relat_1(sK2) != sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2587,c_2611])).

cnf(c_2622,plain,
    ( k2_relat_1(sK2) != sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_2621])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3493,c_2622])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.08  % Command    : iproveropt_run.sh %d %s
% 0.07/0.26  % Computer   : n024.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 12:33:51 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  % Running in FOF mode
% 2.48/0.91  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/0.91  
% 2.48/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.48/0.91  
% 2.48/0.91  ------  iProver source info
% 2.48/0.91  
% 2.48/0.91  git: date: 2020-06-30 10:37:57 +0100
% 2.48/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.48/0.91  git: non_committed_changes: false
% 2.48/0.91  git: last_make_outside_of_git: false
% 2.48/0.91  
% 2.48/0.91  ------ 
% 2.48/0.91  
% 2.48/0.91  ------ Input Options
% 2.48/0.91  
% 2.48/0.91  --out_options                           all
% 2.48/0.91  --tptp_safe_out                         true
% 2.48/0.91  --problem_path                          ""
% 2.48/0.91  --include_path                          ""
% 2.48/0.91  --clausifier                            res/vclausify_rel
% 2.48/0.91  --clausifier_options                    --mode clausify
% 2.48/0.91  --stdin                                 false
% 2.48/0.91  --stats_out                             all
% 2.48/0.91  
% 2.48/0.91  ------ General Options
% 2.48/0.91  
% 2.48/0.91  --fof                                   false
% 2.48/0.91  --time_out_real                         305.
% 2.48/0.91  --time_out_virtual                      -1.
% 2.48/0.91  --symbol_type_check                     false
% 2.48/0.91  --clausify_out                          false
% 2.48/0.91  --sig_cnt_out                           false
% 2.48/0.91  --trig_cnt_out                          false
% 2.48/0.91  --trig_cnt_out_tolerance                1.
% 2.48/0.91  --trig_cnt_out_sk_spl                   false
% 2.48/0.91  --abstr_cl_out                          false
% 2.48/0.91  
% 2.48/0.91  ------ Global Options
% 2.48/0.91  
% 2.48/0.91  --schedule                              default
% 2.48/0.91  --add_important_lit                     false
% 2.48/0.91  --prop_solver_per_cl                    1000
% 2.48/0.91  --min_unsat_core                        false
% 2.48/0.91  --soft_assumptions                      false
% 2.48/0.91  --soft_lemma_size                       3
% 2.48/0.91  --prop_impl_unit_size                   0
% 2.48/0.91  --prop_impl_unit                        []
% 2.48/0.91  --share_sel_clauses                     true
% 2.48/0.91  --reset_solvers                         false
% 2.48/0.91  --bc_imp_inh                            [conj_cone]
% 2.48/0.91  --conj_cone_tolerance                   3.
% 2.48/0.91  --extra_neg_conj                        none
% 2.48/0.91  --large_theory_mode                     true
% 2.48/0.91  --prolific_symb_bound                   200
% 2.48/0.91  --lt_threshold                          2000
% 2.48/0.91  --clause_weak_htbl                      true
% 2.48/0.91  --gc_record_bc_elim                     false
% 2.48/0.91  
% 2.48/0.91  ------ Preprocessing Options
% 2.48/0.91  
% 2.48/0.91  --preprocessing_flag                    true
% 2.48/0.91  --time_out_prep_mult                    0.1
% 2.48/0.91  --splitting_mode                        input
% 2.48/0.91  --splitting_grd                         true
% 2.48/0.91  --splitting_cvd                         false
% 2.48/0.91  --splitting_cvd_svl                     false
% 2.48/0.91  --splitting_nvd                         32
% 2.48/0.91  --sub_typing                            true
% 2.48/0.91  --prep_gs_sim                           true
% 2.48/0.91  --prep_unflatten                        true
% 2.48/0.91  --prep_res_sim                          true
% 2.48/0.91  --prep_upred                            true
% 2.48/0.91  --prep_sem_filter                       exhaustive
% 2.48/0.91  --prep_sem_filter_out                   false
% 2.48/0.91  --pred_elim                             true
% 2.48/0.91  --res_sim_input                         true
% 2.48/0.91  --eq_ax_congr_red                       true
% 2.48/0.91  --pure_diseq_elim                       true
% 2.48/0.91  --brand_transform                       false
% 2.48/0.91  --non_eq_to_eq                          false
% 2.48/0.91  --prep_def_merge                        true
% 2.48/0.91  --prep_def_merge_prop_impl              false
% 2.48/0.91  --prep_def_merge_mbd                    true
% 2.48/0.91  --prep_def_merge_tr_red                 false
% 2.48/0.91  --prep_def_merge_tr_cl                  false
% 2.48/0.91  --smt_preprocessing                     true
% 2.48/0.91  --smt_ac_axioms                         fast
% 2.48/0.91  --preprocessed_out                      false
% 2.48/0.91  --preprocessed_stats                    false
% 2.48/0.91  
% 2.48/0.91  ------ Abstraction refinement Options
% 2.48/0.91  
% 2.48/0.91  --abstr_ref                             []
% 2.48/0.91  --abstr_ref_prep                        false
% 2.48/0.91  --abstr_ref_until_sat                   false
% 2.48/0.91  --abstr_ref_sig_restrict                funpre
% 2.48/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/0.91  --abstr_ref_under                       []
% 2.48/0.91  
% 2.48/0.91  ------ SAT Options
% 2.48/0.91  
% 2.48/0.91  --sat_mode                              false
% 2.48/0.91  --sat_fm_restart_options                ""
% 2.48/0.91  --sat_gr_def                            false
% 2.48/0.91  --sat_epr_types                         true
% 2.48/0.91  --sat_non_cyclic_types                  false
% 2.48/0.91  --sat_finite_models                     false
% 2.48/0.91  --sat_fm_lemmas                         false
% 2.48/0.91  --sat_fm_prep                           false
% 2.48/0.91  --sat_fm_uc_incr                        true
% 2.48/0.91  --sat_out_model                         small
% 2.48/0.91  --sat_out_clauses                       false
% 2.48/0.91  
% 2.48/0.91  ------ QBF Options
% 2.48/0.91  
% 2.48/0.91  --qbf_mode                              false
% 2.48/0.91  --qbf_elim_univ                         false
% 2.48/0.91  --qbf_dom_inst                          none
% 2.48/0.91  --qbf_dom_pre_inst                      false
% 2.48/0.91  --qbf_sk_in                             false
% 2.48/0.91  --qbf_pred_elim                         true
% 2.48/0.91  --qbf_split                             512
% 2.48/0.91  
% 2.48/0.91  ------ BMC1 Options
% 2.48/0.91  
% 2.48/0.91  --bmc1_incremental                      false
% 2.48/0.91  --bmc1_axioms                           reachable_all
% 2.48/0.91  --bmc1_min_bound                        0
% 2.48/0.91  --bmc1_max_bound                        -1
% 2.48/0.91  --bmc1_max_bound_default                -1
% 2.48/0.91  --bmc1_symbol_reachability              true
% 2.48/0.91  --bmc1_property_lemmas                  false
% 2.48/0.91  --bmc1_k_induction                      false
% 2.48/0.91  --bmc1_non_equiv_states                 false
% 2.48/0.91  --bmc1_deadlock                         false
% 2.48/0.91  --bmc1_ucm                              false
% 2.48/0.91  --bmc1_add_unsat_core                   none
% 2.48/0.91  --bmc1_unsat_core_children              false
% 2.48/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/0.91  --bmc1_out_stat                         full
% 2.48/0.91  --bmc1_ground_init                      false
% 2.48/0.91  --bmc1_pre_inst_next_state              false
% 2.48/0.91  --bmc1_pre_inst_state                   false
% 2.48/0.91  --bmc1_pre_inst_reach_state             false
% 2.48/0.91  --bmc1_out_unsat_core                   false
% 2.48/0.91  --bmc1_aig_witness_out                  false
% 2.48/0.91  --bmc1_verbose                          false
% 2.48/0.91  --bmc1_dump_clauses_tptp                false
% 2.48/0.91  --bmc1_dump_unsat_core_tptp             false
% 2.48/0.91  --bmc1_dump_file                        -
% 2.48/0.91  --bmc1_ucm_expand_uc_limit              128
% 2.48/0.91  --bmc1_ucm_n_expand_iterations          6
% 2.48/0.91  --bmc1_ucm_extend_mode                  1
% 2.48/0.91  --bmc1_ucm_init_mode                    2
% 2.48/0.91  --bmc1_ucm_cone_mode                    none
% 2.48/0.91  --bmc1_ucm_reduced_relation_type        0
% 2.48/0.91  --bmc1_ucm_relax_model                  4
% 2.48/0.91  --bmc1_ucm_full_tr_after_sat            true
% 2.48/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/0.91  --bmc1_ucm_layered_model                none
% 2.48/0.91  --bmc1_ucm_max_lemma_size               10
% 2.48/0.91  
% 2.48/0.91  ------ AIG Options
% 2.48/0.91  
% 2.48/0.91  --aig_mode                              false
% 2.48/0.91  
% 2.48/0.91  ------ Instantiation Options
% 2.48/0.91  
% 2.48/0.91  --instantiation_flag                    true
% 2.48/0.91  --inst_sos_flag                         false
% 2.48/0.91  --inst_sos_phase                        true
% 2.48/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/0.91  --inst_lit_sel_side                     num_symb
% 2.48/0.91  --inst_solver_per_active                1400
% 2.48/0.91  --inst_solver_calls_frac                1.
% 2.48/0.91  --inst_passive_queue_type               priority_queues
% 2.48/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/0.91  --inst_passive_queues_freq              [25;2]
% 2.48/0.91  --inst_dismatching                      true
% 2.48/0.91  --inst_eager_unprocessed_to_passive     true
% 2.48/0.91  --inst_prop_sim_given                   true
% 2.48/0.91  --inst_prop_sim_new                     false
% 2.48/0.91  --inst_subs_new                         false
% 2.48/0.91  --inst_eq_res_simp                      false
% 2.48/0.91  --inst_subs_given                       false
% 2.48/0.91  --inst_orphan_elimination               true
% 2.48/0.91  --inst_learning_loop_flag               true
% 2.48/0.91  --inst_learning_start                   3000
% 2.48/0.91  --inst_learning_factor                  2
% 2.48/0.91  --inst_start_prop_sim_after_learn       3
% 2.48/0.91  --inst_sel_renew                        solver
% 2.48/0.91  --inst_lit_activity_flag                true
% 2.48/0.91  --inst_restr_to_given                   false
% 2.48/0.91  --inst_activity_threshold               500
% 2.48/0.91  --inst_out_proof                        true
% 2.48/0.91  
% 2.48/0.91  ------ Resolution Options
% 2.48/0.91  
% 2.48/0.91  --resolution_flag                       true
% 2.48/0.91  --res_lit_sel                           adaptive
% 2.48/0.91  --res_lit_sel_side                      none
% 2.48/0.91  --res_ordering                          kbo
% 2.48/0.91  --res_to_prop_solver                    active
% 2.48/0.91  --res_prop_simpl_new                    false
% 2.48/0.91  --res_prop_simpl_given                  true
% 2.48/0.91  --res_passive_queue_type                priority_queues
% 2.48/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/0.91  --res_passive_queues_freq               [15;5]
% 2.48/0.91  --res_forward_subs                      full
% 2.48/0.91  --res_backward_subs                     full
% 2.48/0.91  --res_forward_subs_resolution           true
% 2.48/0.91  --res_backward_subs_resolution          true
% 2.48/0.91  --res_orphan_elimination                true
% 2.48/0.91  --res_time_limit                        2.
% 2.48/0.91  --res_out_proof                         true
% 2.48/0.91  
% 2.48/0.91  ------ Superposition Options
% 2.48/0.91  
% 2.48/0.91  --superposition_flag                    true
% 2.48/0.91  --sup_passive_queue_type                priority_queues
% 2.48/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/0.91  --sup_passive_queues_freq               [8;1;4]
% 2.48/0.91  --demod_completeness_check              fast
% 2.48/0.91  --demod_use_ground                      true
% 2.48/0.91  --sup_to_prop_solver                    passive
% 2.48/0.91  --sup_prop_simpl_new                    true
% 2.48/0.91  --sup_prop_simpl_given                  true
% 2.48/0.91  --sup_fun_splitting                     false
% 2.48/0.91  --sup_smt_interval                      50000
% 2.48/0.91  
% 2.48/0.91  ------ Superposition Simplification Setup
% 2.48/0.91  
% 2.48/0.91  --sup_indices_passive                   []
% 2.48/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.91  --sup_full_bw                           [BwDemod]
% 2.48/0.91  --sup_immed_triv                        [TrivRules]
% 2.48/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.91  --sup_immed_bw_main                     []
% 2.48/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/0.91  
% 2.48/0.91  ------ Combination Options
% 2.48/0.91  
% 2.48/0.91  --comb_res_mult                         3
% 2.48/0.91  --comb_sup_mult                         2
% 2.48/0.91  --comb_inst_mult                        10
% 2.48/0.91  
% 2.48/0.91  ------ Debug Options
% 2.48/0.91  
% 2.48/0.91  --dbg_backtrace                         false
% 2.48/0.91  --dbg_dump_prop_clauses                 false
% 2.48/0.91  --dbg_dump_prop_clauses_file            -
% 2.48/0.91  --dbg_out_stat                          false
% 2.48/0.91  ------ Parsing...
% 2.48/0.91  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.48/0.91  
% 2.48/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.48/0.91  
% 2.48/0.91  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.48/0.91  
% 2.48/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.48/0.91  ------ Proving...
% 2.48/0.91  ------ Problem Properties 
% 2.48/0.91  
% 2.48/0.91  
% 2.48/0.91  clauses                                 27
% 2.48/0.91  conjectures                             3
% 2.48/0.91  EPR                                     1
% 2.48/0.91  Horn                                    23
% 2.48/0.91  unary                                   4
% 2.48/0.91  binary                                  9
% 2.48/0.91  lits                                    80
% 2.48/0.91  lits eq                                 33
% 2.48/0.91  fd_pure                                 0
% 2.48/0.91  fd_pseudo                               0
% 2.48/0.91  fd_cond                                 1
% 2.48/0.91  fd_pseudo_cond                          0
% 2.48/0.91  AC symbols                              0
% 2.48/0.91  
% 2.48/0.91  ------ Schedule dynamic 5 is on 
% 2.48/0.91  
% 2.48/0.91  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.48/0.91  
% 2.48/0.91  
% 2.48/0.91  ------ 
% 2.48/0.91  Current options:
% 2.48/0.91  ------ 
% 2.48/0.91  
% 2.48/0.91  ------ Input Options
% 2.48/0.91  
% 2.48/0.91  --out_options                           all
% 2.48/0.91  --tptp_safe_out                         true
% 2.48/0.91  --problem_path                          ""
% 2.48/0.91  --include_path                          ""
% 2.48/0.91  --clausifier                            res/vclausify_rel
% 2.48/0.91  --clausifier_options                    --mode clausify
% 2.48/0.91  --stdin                                 false
% 2.48/0.91  --stats_out                             all
% 2.48/0.91  
% 2.48/0.91  ------ General Options
% 2.48/0.91  
% 2.48/0.91  --fof                                   false
% 2.48/0.91  --time_out_real                         305.
% 2.48/0.91  --time_out_virtual                      -1.
% 2.48/0.91  --symbol_type_check                     false
% 2.48/0.91  --clausify_out                          false
% 2.48/0.91  --sig_cnt_out                           false
% 2.48/0.91  --trig_cnt_out                          false
% 2.48/0.91  --trig_cnt_out_tolerance                1.
% 2.48/0.91  --trig_cnt_out_sk_spl                   false
% 2.48/0.91  --abstr_cl_out                          false
% 2.48/0.91  
% 2.48/0.91  ------ Global Options
% 2.48/0.91  
% 2.48/0.91  --schedule                              default
% 2.48/0.91  --add_important_lit                     false
% 2.48/0.91  --prop_solver_per_cl                    1000
% 2.48/0.91  --min_unsat_core                        false
% 2.48/0.91  --soft_assumptions                      false
% 2.48/0.91  --soft_lemma_size                       3
% 2.48/0.91  --prop_impl_unit_size                   0
% 2.48/0.91  --prop_impl_unit                        []
% 2.48/0.91  --share_sel_clauses                     true
% 2.48/0.91  --reset_solvers                         false
% 2.48/0.91  --bc_imp_inh                            [conj_cone]
% 2.48/0.91  --conj_cone_tolerance                   3.
% 2.48/0.91  --extra_neg_conj                        none
% 2.48/0.91  --large_theory_mode                     true
% 2.48/0.91  --prolific_symb_bound                   200
% 2.48/0.91  --lt_threshold                          2000
% 2.48/0.91  --clause_weak_htbl                      true
% 2.48/0.91  --gc_record_bc_elim                     false
% 2.48/0.91  
% 2.48/0.91  ------ Preprocessing Options
% 2.48/0.91  
% 2.48/0.91  --preprocessing_flag                    true
% 2.48/0.91  --time_out_prep_mult                    0.1
% 2.48/0.91  --splitting_mode                        input
% 2.48/0.91  --splitting_grd                         true
% 2.48/0.91  --splitting_cvd                         false
% 2.48/0.91  --splitting_cvd_svl                     false
% 2.48/0.91  --splitting_nvd                         32
% 2.48/0.91  --sub_typing                            true
% 2.48/0.91  --prep_gs_sim                           true
% 2.48/0.91  --prep_unflatten                        true
% 2.48/0.91  --prep_res_sim                          true
% 2.48/0.91  --prep_upred                            true
% 2.48/0.91  --prep_sem_filter                       exhaustive
% 2.48/0.91  --prep_sem_filter_out                   false
% 2.48/0.91  --pred_elim                             true
% 2.48/0.91  --res_sim_input                         true
% 2.48/0.91  --eq_ax_congr_red                       true
% 2.48/0.91  --pure_diseq_elim                       true
% 2.48/0.91  --brand_transform                       false
% 2.48/0.91  --non_eq_to_eq                          false
% 2.48/0.91  --prep_def_merge                        true
% 2.48/0.91  --prep_def_merge_prop_impl              false
% 2.48/0.91  --prep_def_merge_mbd                    true
% 2.48/0.91  --prep_def_merge_tr_red                 false
% 2.48/0.91  --prep_def_merge_tr_cl                  false
% 2.48/0.91  --smt_preprocessing                     true
% 2.48/0.91  --smt_ac_axioms                         fast
% 2.48/0.91  --preprocessed_out                      false
% 2.48/0.91  --preprocessed_stats                    false
% 2.48/0.91  
% 2.48/0.91  ------ Abstraction refinement Options
% 2.48/0.91  
% 2.48/0.91  --abstr_ref                             []
% 2.48/0.91  --abstr_ref_prep                        false
% 2.48/0.91  --abstr_ref_until_sat                   false
% 2.48/0.91  --abstr_ref_sig_restrict                funpre
% 2.48/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/0.91  --abstr_ref_under                       []
% 2.48/0.91  
% 2.48/0.91  ------ SAT Options
% 2.48/0.91  
% 2.48/0.91  --sat_mode                              false
% 2.48/0.91  --sat_fm_restart_options                ""
% 2.48/0.91  --sat_gr_def                            false
% 2.48/0.91  --sat_epr_types                         true
% 2.48/0.91  --sat_non_cyclic_types                  false
% 2.48/0.91  --sat_finite_models                     false
% 2.48/0.91  --sat_fm_lemmas                         false
% 2.48/0.91  --sat_fm_prep                           false
% 2.48/0.91  --sat_fm_uc_incr                        true
% 2.48/0.91  --sat_out_model                         small
% 2.48/0.91  --sat_out_clauses                       false
% 2.48/0.91  
% 2.48/0.91  ------ QBF Options
% 2.48/0.91  
% 2.48/0.91  --qbf_mode                              false
% 2.48/0.91  --qbf_elim_univ                         false
% 2.48/0.91  --qbf_dom_inst                          none
% 2.48/0.91  --qbf_dom_pre_inst                      false
% 2.48/0.91  --qbf_sk_in                             false
% 2.48/0.91  --qbf_pred_elim                         true
% 2.48/0.91  --qbf_split                             512
% 2.48/0.91  
% 2.48/0.91  ------ BMC1 Options
% 2.48/0.91  
% 2.48/0.91  --bmc1_incremental                      false
% 2.48/0.91  --bmc1_axioms                           reachable_all
% 2.48/0.91  --bmc1_min_bound                        0
% 2.48/0.91  --bmc1_max_bound                        -1
% 2.48/0.91  --bmc1_max_bound_default                -1
% 2.48/0.91  --bmc1_symbol_reachability              true
% 2.48/0.91  --bmc1_property_lemmas                  false
% 2.48/0.91  --bmc1_k_induction                      false
% 2.48/0.91  --bmc1_non_equiv_states                 false
% 2.48/0.91  --bmc1_deadlock                         false
% 2.48/0.91  --bmc1_ucm                              false
% 2.48/0.91  --bmc1_add_unsat_core                   none
% 2.48/0.91  --bmc1_unsat_core_children              false
% 2.48/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/0.91  --bmc1_out_stat                         full
% 2.48/0.91  --bmc1_ground_init                      false
% 2.48/0.91  --bmc1_pre_inst_next_state              false
% 2.48/0.91  --bmc1_pre_inst_state                   false
% 2.48/0.91  --bmc1_pre_inst_reach_state             false
% 2.48/0.91  --bmc1_out_unsat_core                   false
% 2.48/0.91  --bmc1_aig_witness_out                  false
% 2.48/0.91  --bmc1_verbose                          false
% 2.48/0.91  --bmc1_dump_clauses_tptp                false
% 2.48/0.91  --bmc1_dump_unsat_core_tptp             false
% 2.48/0.91  --bmc1_dump_file                        -
% 2.48/0.91  --bmc1_ucm_expand_uc_limit              128
% 2.48/0.91  --bmc1_ucm_n_expand_iterations          6
% 2.48/0.91  --bmc1_ucm_extend_mode                  1
% 2.48/0.91  --bmc1_ucm_init_mode                    2
% 2.48/0.91  --bmc1_ucm_cone_mode                    none
% 2.48/0.91  --bmc1_ucm_reduced_relation_type        0
% 2.48/0.91  --bmc1_ucm_relax_model                  4
% 2.48/0.91  --bmc1_ucm_full_tr_after_sat            true
% 2.48/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/0.91  --bmc1_ucm_layered_model                none
% 2.48/0.91  --bmc1_ucm_max_lemma_size               10
% 2.48/0.91  
% 2.48/0.91  ------ AIG Options
% 2.48/0.91  
% 2.48/0.91  --aig_mode                              false
% 2.48/0.91  
% 2.48/0.91  ------ Instantiation Options
% 2.48/0.91  
% 2.48/0.91  --instantiation_flag                    true
% 2.48/0.91  --inst_sos_flag                         false
% 2.48/0.91  --inst_sos_phase                        true
% 2.48/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/0.91  --inst_lit_sel_side                     none
% 2.48/0.91  --inst_solver_per_active                1400
% 2.48/0.91  --inst_solver_calls_frac                1.
% 2.48/0.91  --inst_passive_queue_type               priority_queues
% 2.48/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/0.91  --inst_passive_queues_freq              [25;2]
% 2.48/0.91  --inst_dismatching                      true
% 2.48/0.91  --inst_eager_unprocessed_to_passive     true
% 2.48/0.91  --inst_prop_sim_given                   true
% 2.48/0.91  --inst_prop_sim_new                     false
% 2.48/0.91  --inst_subs_new                         false
% 2.48/0.91  --inst_eq_res_simp                      false
% 2.48/0.91  --inst_subs_given                       false
% 2.48/0.91  --inst_orphan_elimination               true
% 2.48/0.91  --inst_learning_loop_flag               true
% 2.48/0.91  --inst_learning_start                   3000
% 2.48/0.91  --inst_learning_factor                  2
% 2.48/0.91  --inst_start_prop_sim_after_learn       3
% 2.48/0.91  --inst_sel_renew                        solver
% 2.48/0.91  --inst_lit_activity_flag                true
% 2.48/0.91  --inst_restr_to_given                   false
% 2.48/0.91  --inst_activity_threshold               500
% 2.48/0.91  --inst_out_proof                        true
% 2.48/0.91  
% 2.48/0.91  ------ Resolution Options
% 2.48/0.91  
% 2.48/0.91  --resolution_flag                       false
% 2.48/0.91  --res_lit_sel                           adaptive
% 2.48/0.91  --res_lit_sel_side                      none
% 2.48/0.91  --res_ordering                          kbo
% 2.48/0.91  --res_to_prop_solver                    active
% 2.48/0.91  --res_prop_simpl_new                    false
% 2.48/0.91  --res_prop_simpl_given                  true
% 2.48/0.91  --res_passive_queue_type                priority_queues
% 2.48/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/0.91  --res_passive_queues_freq               [15;5]
% 2.48/0.91  --res_forward_subs                      full
% 2.48/0.91  --res_backward_subs                     full
% 2.48/0.91  --res_forward_subs_resolution           true
% 2.48/0.91  --res_backward_subs_resolution          true
% 2.48/0.91  --res_orphan_elimination                true
% 2.48/0.91  --res_time_limit                        2.
% 2.48/0.91  --res_out_proof                         true
% 2.48/0.91  
% 2.48/0.91  ------ Superposition Options
% 2.48/0.91  
% 2.48/0.91  --superposition_flag                    true
% 2.48/0.91  --sup_passive_queue_type                priority_queues
% 2.48/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/0.91  --sup_passive_queues_freq               [8;1;4]
% 2.48/0.91  --demod_completeness_check              fast
% 2.48/0.91  --demod_use_ground                      true
% 2.48/0.91  --sup_to_prop_solver                    passive
% 2.48/0.91  --sup_prop_simpl_new                    true
% 2.48/0.91  --sup_prop_simpl_given                  true
% 2.48/0.91  --sup_fun_splitting                     false
% 2.48/0.91  --sup_smt_interval                      50000
% 2.48/0.91  
% 2.48/0.91  ------ Superposition Simplification Setup
% 2.48/0.91  
% 2.48/0.91  --sup_indices_passive                   []
% 2.48/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.91  --sup_full_bw                           [BwDemod]
% 2.48/0.91  --sup_immed_triv                        [TrivRules]
% 2.48/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.91  --sup_immed_bw_main                     []
% 2.48/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/0.91  
% 2.48/0.91  ------ Combination Options
% 2.48/0.91  
% 2.48/0.91  --comb_res_mult                         3
% 2.48/0.91  --comb_sup_mult                         2
% 2.48/0.91  --comb_inst_mult                        10
% 2.48/0.91  
% 2.48/0.91  ------ Debug Options
% 2.48/0.91  
% 2.48/0.91  --dbg_backtrace                         false
% 2.48/0.91  --dbg_dump_prop_clauses                 false
% 2.48/0.91  --dbg_dump_prop_clauses_file            -
% 2.48/0.91  --dbg_out_stat                          false
% 2.48/0.91  
% 2.48/0.91  
% 2.48/0.91  
% 2.48/0.91  
% 2.48/0.91  ------ Proving...
% 2.48/0.91  
% 2.48/0.91  
% 2.48/0.91  % SZS status Theorem for theBenchmark.p
% 2.48/0.91  
% 2.48/0.91  % SZS output start CNFRefutation for theBenchmark.p
% 2.48/0.91  
% 2.48/0.91  fof(f12,conjecture,(
% 2.48/0.91    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.48/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/0.91  
% 2.48/0.91  fof(f13,negated_conjecture,(
% 2.48/0.91    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.48/0.91    inference(negated_conjecture,[],[f12])).
% 2.48/0.91  
% 2.48/0.91  fof(f28,plain,(
% 2.48/0.91    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.48/0.91    inference(ennf_transformation,[],[f13])).
% 2.48/0.91  
% 2.48/0.91  fof(f29,plain,(
% 2.48/0.91    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.48/0.91    inference(flattening,[],[f28])).
% 2.48/0.91  
% 2.48/0.91  fof(f31,plain,(
% 2.48/0.91    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.48/0.91    introduced(choice_axiom,[])).
% 2.48/0.91  
% 2.48/0.91  fof(f32,plain,(
% 2.48/0.91    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.48/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f31])).
% 2.48/0.91  
% 2.48/0.91  fof(f56,plain,(
% 2.48/0.91    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.48/0.91    inference(cnf_transformation,[],[f32])).
% 2.48/0.91  
% 2.48/0.91  fof(f8,axiom,(
% 2.48/0.91    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 2.48/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/0.91  
% 2.48/0.91  fof(f22,plain,(
% 2.48/0.91    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/0.91    inference(ennf_transformation,[],[f8])).
% 2.48/0.91  
% 2.48/0.91  fof(f42,plain,(
% 2.48/0.91    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.48/0.91    inference(cnf_transformation,[],[f22])).
% 2.48/0.91  
% 2.48/0.91  fof(f6,axiom,(
% 2.48/0.91    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.48/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/0.91  
% 2.48/0.91  fof(f20,plain,(
% 2.48/0.91    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/0.91    inference(ennf_transformation,[],[f6])).
% 2.48/0.91  
% 2.48/0.91  fof(f40,plain,(
% 2.48/0.91    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.48/0.91    inference(cnf_transformation,[],[f20])).
% 2.48/0.91  
% 2.48/0.91  fof(f7,axiom,(
% 2.48/0.91    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.48/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/0.91  
% 2.48/0.91  fof(f21,plain,(
% 2.48/0.91    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/0.91    inference(ennf_transformation,[],[f7])).
% 2.48/0.91  
% 2.48/0.91  fof(f41,plain,(
% 2.48/0.91    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.48/0.91    inference(cnf_transformation,[],[f21])).
% 2.48/0.91  
% 2.48/0.91  fof(f1,axiom,(
% 2.48/0.91    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.48/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/0.91  
% 2.48/0.91  fof(f14,plain,(
% 2.48/0.91    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.48/0.91    inference(ennf_transformation,[],[f1])).
% 2.48/0.91  
% 2.48/0.91  fof(f33,plain,(
% 2.48/0.91    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.48/0.91    inference(cnf_transformation,[],[f14])).
% 2.48/0.91  
% 2.48/0.91  fof(f2,axiom,(
% 2.48/0.91    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.48/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/0.91  
% 2.48/0.91  fof(f34,plain,(
% 2.48/0.91    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.48/0.91    inference(cnf_transformation,[],[f2])).
% 2.48/0.91  
% 2.48/0.91  fof(f3,axiom,(
% 2.48/0.91    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.48/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/0.91  
% 2.48/0.91  fof(f15,plain,(
% 2.48/0.91    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.48/0.91    inference(ennf_transformation,[],[f3])).
% 2.48/0.91  
% 2.48/0.91  fof(f35,plain,(
% 2.48/0.91    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.48/0.91    inference(cnf_transformation,[],[f15])).
% 2.48/0.91  
% 2.48/0.91  fof(f4,axiom,(
% 2.48/0.91    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.48/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/0.91  
% 2.48/0.91  fof(f16,plain,(
% 2.48/0.91    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.48/0.91    inference(ennf_transformation,[],[f4])).
% 2.48/0.91  
% 2.48/0.91  fof(f17,plain,(
% 2.48/0.91    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.48/0.91    inference(flattening,[],[f16])).
% 2.48/0.91  
% 2.48/0.91  fof(f37,plain,(
% 2.48/0.91    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.48/0.91    inference(cnf_transformation,[],[f17])).
% 2.48/0.91  
% 2.48/0.91  fof(f57,plain,(
% 2.48/0.91    v2_funct_1(sK2)),
% 2.48/0.91    inference(cnf_transformation,[],[f32])).
% 2.48/0.91  
% 2.48/0.91  fof(f54,plain,(
% 2.48/0.91    v1_funct_1(sK2)),
% 2.48/0.91    inference(cnf_transformation,[],[f32])).
% 2.48/0.91  
% 2.48/0.91  fof(f10,axiom,(
% 2.48/0.91    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.48/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/0.91  
% 2.48/0.91  fof(f24,plain,(
% 2.48/0.91    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/0.91    inference(ennf_transformation,[],[f10])).
% 2.48/0.91  
% 2.48/0.91  fof(f25,plain,(
% 2.48/0.91    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/0.91    inference(flattening,[],[f24])).
% 2.48/0.91  
% 2.48/0.91  fof(f30,plain,(
% 2.48/0.91    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/0.91    inference(nnf_transformation,[],[f25])).
% 2.48/0.91  
% 2.48/0.91  fof(f47,plain,(
% 2.48/0.91    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.48/0.91    inference(cnf_transformation,[],[f30])).
% 2.48/0.91  
% 2.48/0.91  fof(f59,plain,(
% 2.48/0.91    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.48/0.91    inference(cnf_transformation,[],[f32])).
% 2.48/0.91  
% 2.48/0.91  fof(f5,axiom,(
% 2.48/0.91    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.48/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/0.91  
% 2.48/0.91  fof(f18,plain,(
% 2.48/0.91    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.48/0.91    inference(ennf_transformation,[],[f5])).
% 2.48/0.91  
% 2.48/0.91  fof(f19,plain,(
% 2.48/0.91    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.48/0.91    inference(flattening,[],[f18])).
% 2.48/0.91  
% 2.48/0.91  fof(f39,plain,(
% 2.48/0.91    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.48/0.91    inference(cnf_transformation,[],[f19])).
% 2.48/0.91  
% 2.48/0.91  fof(f9,axiom,(
% 2.48/0.91    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)))),
% 2.48/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/0.91  
% 2.48/0.91  fof(f23,plain,(
% 2.48/0.91    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/0.91    inference(ennf_transformation,[],[f9])).
% 2.48/0.91  
% 2.48/0.91  fof(f43,plain,(
% 2.48/0.91    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.48/0.91    inference(cnf_transformation,[],[f23])).
% 2.48/0.91  
% 2.48/0.91  fof(f58,plain,(
% 2.48/0.91    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.48/0.91    inference(cnf_transformation,[],[f32])).
% 2.48/0.91  
% 2.48/0.91  fof(f11,axiom,(
% 2.48/0.91    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.48/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/0.91  
% 2.48/0.91  fof(f26,plain,(
% 2.48/0.91    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.48/0.91    inference(ennf_transformation,[],[f11])).
% 2.48/0.91  
% 2.48/0.91  fof(f27,plain,(
% 2.48/0.91    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.48/0.91    inference(flattening,[],[f26])).
% 2.48/0.91  
% 2.48/0.91  fof(f52,plain,(
% 2.48/0.91    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.48/0.91    inference(cnf_transformation,[],[f27])).
% 2.48/0.91  
% 2.48/0.91  fof(f38,plain,(
% 2.48/0.91    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.48/0.91    inference(cnf_transformation,[],[f19])).
% 2.48/0.91  
% 2.48/0.91  fof(f36,plain,(
% 2.48/0.91    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.48/0.91    inference(cnf_transformation,[],[f15])).
% 2.48/0.91  
% 2.48/0.91  fof(f46,plain,(
% 2.48/0.91    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.48/0.91    inference(cnf_transformation,[],[f30])).
% 2.48/0.91  
% 2.48/0.91  fof(f64,plain,(
% 2.48/0.91    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.48/0.91    inference(equality_resolution,[],[f46])).
% 2.48/0.92  
% 2.48/0.92  fof(f55,plain,(
% 2.48/0.92    v1_funct_2(sK2,sK0,sK1)),
% 2.48/0.92    inference(cnf_transformation,[],[f32])).
% 2.48/0.92  
% 2.48/0.92  cnf(c_24,negated_conjecture,
% 2.48/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.48/0.92      inference(cnf_transformation,[],[f56]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_594,negated_conjecture,
% 2.48/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_24]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1070,plain,
% 2.48/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_9,plain,
% 2.48/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/0.92      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 2.48/0.92      inference(cnf_transformation,[],[f42]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_599,plain,
% 2.48/0.92      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.48/0.92      | k3_relset_1(X1_46,X2_46,X0_46) = k4_relat_1(X0_46) ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_9]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1066,plain,
% 2.48/0.92      ( k3_relset_1(X0_46,X1_46,X2_46) = k4_relat_1(X2_46)
% 2.48/0.92      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1902,plain,
% 2.48/0.92      ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
% 2.48/0.92      inference(superposition,[status(thm)],[c_1070,c_1066]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_7,plain,
% 2.48/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/0.92      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.48/0.92      inference(cnf_transformation,[],[f40]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_601,plain,
% 2.48/0.92      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.48/0.92      | m1_subset_1(k3_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46))) ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_7]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1064,plain,
% 2.48/0.92      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
% 2.48/0.92      | m1_subset_1(k3_relset_1(X1_46,X2_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46))) = iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2110,plain,
% 2.48/0.92      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 2.48/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.48/0.92      inference(superposition,[status(thm)],[c_1902,c_1064]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_29,plain,
% 2.48/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2247,plain,
% 2.48/0.92      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.48/0.92      inference(global_propositional_subsumption,
% 2.48/0.92                [status(thm)],
% 2.48/0.92                [c_2110,c_29]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_8,plain,
% 2.48/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/0.92      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.48/0.92      inference(cnf_transformation,[],[f41]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_600,plain,
% 2.48/0.92      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.48/0.92      | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_8]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1065,plain,
% 2.48/0.92      ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
% 2.48/0.92      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2254,plain,
% 2.48/0.92      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 2.48/0.92      inference(superposition,[status(thm)],[c_2247,c_1065]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_0,plain,
% 2.48/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.48/0.92      | ~ v1_relat_1(X1)
% 2.48/0.92      | v1_relat_1(X0) ),
% 2.48/0.92      inference(cnf_transformation,[],[f33]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_607,plain,
% 2.48/0.92      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.48/0.92      | ~ v1_relat_1(X1_46)
% 2.48/0.92      | v1_relat_1(X0_46) ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_0]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1058,plain,
% 2.48/0.92      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 2.48/0.92      | v1_relat_1(X1_46) != iProver_top
% 2.48/0.92      | v1_relat_1(X0_46) = iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1426,plain,
% 2.48/0.92      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.48/0.92      | v1_relat_1(sK2) = iProver_top ),
% 2.48/0.92      inference(superposition,[status(thm)],[c_1070,c_1058]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1,plain,
% 2.48/0.92      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.48/0.92      inference(cnf_transformation,[],[f34]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_606,plain,
% 2.48/0.92      ( v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_1]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1495,plain,
% 2.48/0.92      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.48/0.92      inference(instantiation,[status(thm)],[c_606]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1496,plain,
% 2.48/0.92      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_1495]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1538,plain,
% 2.48/0.92      ( v1_relat_1(sK2) = iProver_top ),
% 2.48/0.92      inference(global_propositional_subsumption,
% 2.48/0.92                [status(thm)],
% 2.48/0.92                [c_1426,c_1496]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_3,plain,
% 2.48/0.92      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.48/0.92      inference(cnf_transformation,[],[f35]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_604,plain,
% 2.48/0.92      ( ~ v1_relat_1(X0_46)
% 2.48/0.92      | k1_relat_1(k4_relat_1(X0_46)) = k2_relat_1(X0_46) ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_3]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1061,plain,
% 2.48/0.92      ( k1_relat_1(k4_relat_1(X0_46)) = k2_relat_1(X0_46)
% 2.48/0.92      | v1_relat_1(X0_46) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1544,plain,
% 2.48/0.92      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.48/0.92      inference(superposition,[status(thm)],[c_1538,c_1061]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2259,plain,
% 2.48/0.92      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.48/0.92      inference(light_normalisation,[status(thm)],[c_2254,c_1544]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_4,plain,
% 2.48/0.92      ( ~ v1_funct_1(X0)
% 2.48/0.92      | ~ v2_funct_1(X0)
% 2.48/0.92      | ~ v1_relat_1(X0)
% 2.48/0.92      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.48/0.92      inference(cnf_transformation,[],[f37]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_23,negated_conjecture,
% 2.48/0.92      ( v2_funct_1(sK2) ),
% 2.48/0.92      inference(cnf_transformation,[],[f57]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_290,plain,
% 2.48/0.92      ( ~ v1_funct_1(X0)
% 2.48/0.92      | ~ v1_relat_1(X0)
% 2.48/0.92      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.48/0.92      | sK2 != X0 ),
% 2.48/0.92      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_291,plain,
% 2.48/0.92      ( ~ v1_funct_1(sK2)
% 2.48/0.92      | ~ v1_relat_1(sK2)
% 2.48/0.92      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.48/0.92      inference(unflattening,[status(thm)],[c_290]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_26,negated_conjecture,
% 2.48/0.92      ( v1_funct_1(sK2) ),
% 2.48/0.92      inference(cnf_transformation,[],[f54]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_293,plain,
% 2.48/0.92      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.48/0.92      inference(global_propositional_subsumption,
% 2.48/0.92                [status(thm)],
% 2.48/0.92                [c_291,c_26]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_592,plain,
% 2.48/0.92      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_293]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1072,plain,
% 2.48/0.92      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 2.48/0.92      | v1_relat_1(sK2) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1543,plain,
% 2.48/0.92      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.48/0.92      inference(superposition,[status(thm)],[c_1538,c_1072]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_15,plain,
% 2.48/0.92      ( v1_funct_2(X0,X1,X2)
% 2.48/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/0.92      | k1_relset_1(X1,X2,X0) != X1
% 2.48/0.92      | k1_xboole_0 = X2 ),
% 2.48/0.92      inference(cnf_transformation,[],[f47]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_21,negated_conjecture,
% 2.48/0.92      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.48/0.92      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.48/0.92      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.48/0.92      inference(cnf_transformation,[],[f59]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_462,plain,
% 2.48/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/0.92      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.48/0.92      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.48/0.92      | k1_relset_1(X1,X2,X0) != X1
% 2.48/0.92      | k2_funct_1(sK2) != X0
% 2.48/0.92      | sK0 != X2
% 2.48/0.92      | sK1 != X1
% 2.48/0.92      | k1_xboole_0 = X2 ),
% 2.48/0.92      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_463,plain,
% 2.48/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.48/0.92      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.48/0.92      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.48/0.92      | k1_xboole_0 = sK0 ),
% 2.48/0.92      inference(unflattening,[status(thm)],[c_462]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_584,plain,
% 2.48/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.48/0.92      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.48/0.92      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.48/0.92      | k1_xboole_0 = sK0 ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_463]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1080,plain,
% 2.48/0.92      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.48/0.92      | k1_xboole_0 = sK0
% 2.48/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.48/0.92      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1711,plain,
% 2.48/0.92      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != sK1
% 2.48/0.92      | sK0 = k1_xboole_0
% 2.48/0.92      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.48/0.92      | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 2.48/0.92      inference(demodulation,[status(thm)],[c_1543,c_1080]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_27,plain,
% 2.48/0.92      ( v1_funct_1(sK2) = iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_5,plain,
% 2.48/0.92      ( ~ v1_funct_1(X0)
% 2.48/0.92      | v1_funct_1(k2_funct_1(X0))
% 2.48/0.92      | ~ v1_relat_1(X0) ),
% 2.48/0.92      inference(cnf_transformation,[],[f39]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_603,plain,
% 2.48/0.92      ( ~ v1_funct_1(X0_46)
% 2.48/0.92      | v1_funct_1(k2_funct_1(X0_46))
% 2.48/0.92      | ~ v1_relat_1(X0_46) ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_5]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1062,plain,
% 2.48/0.92      ( v1_funct_1(X0_46) != iProver_top
% 2.48/0.92      | v1_funct_1(k2_funct_1(X0_46)) = iProver_top
% 2.48/0.92      | v1_relat_1(X0_46) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1758,plain,
% 2.48/0.92      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.48/0.92      | v1_funct_1(sK2) != iProver_top
% 2.48/0.92      | v1_relat_1(sK2) != iProver_top ),
% 2.48/0.92      inference(superposition,[status(thm)],[c_1543,c_1062]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_11,plain,
% 2.48/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/0.92      | k1_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k2_relset_1(X1,X2,X0) ),
% 2.48/0.92      inference(cnf_transformation,[],[f43]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_597,plain,
% 2.48/0.92      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.48/0.92      | k1_relset_1(X2_46,X1_46,k3_relset_1(X1_46,X2_46,X0_46)) = k2_relset_1(X1_46,X2_46,X0_46) ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_11]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1068,plain,
% 2.48/0.92      ( k1_relset_1(X0_46,X1_46,k3_relset_1(X1_46,X0_46,X2_46)) = k2_relset_1(X1_46,X0_46,X2_46)
% 2.48/0.92      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X0_46))) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2384,plain,
% 2.48/0.92      ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) = k2_relset_1(sK0,sK1,sK2) ),
% 2.48/0.92      inference(superposition,[status(thm)],[c_1070,c_1068]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_22,negated_conjecture,
% 2.48/0.92      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.48/0.92      inference(cnf_transformation,[],[f58]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_595,negated_conjecture,
% 2.48/0.92      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_22]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2395,plain,
% 2.48/0.92      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 ),
% 2.48/0.92      inference(light_normalisation,[status(thm)],[c_2384,c_595,c_1902]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2581,plain,
% 2.48/0.92      ( sK0 = k1_xboole_0 ),
% 2.48/0.92      inference(global_propositional_subsumption,
% 2.48/0.92                [status(thm)],
% 2.48/0.92                [c_1711,c_27,c_29,c_1426,c_1496,c_1758,c_2110,c_2395]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2585,plain,
% 2.48/0.92      ( k1_relset_1(sK1,k1_xboole_0,k4_relat_1(sK2)) = sK1 ),
% 2.48/0.92      inference(demodulation,[status(thm)],[c_2581,c_2395]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_3493,plain,
% 2.48/0.92      ( k2_relat_1(sK2) = sK1 ),
% 2.48/0.92      inference(light_normalisation,[status(thm)],[c_2259,c_2581,c_2585]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_19,plain,
% 2.48/0.92      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.48/0.92      | ~ v1_funct_1(X0)
% 2.48/0.92      | ~ v1_relat_1(X0) ),
% 2.48/0.92      inference(cnf_transformation,[],[f52]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_489,plain,
% 2.48/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.48/0.92      | ~ v1_funct_1(X0)
% 2.48/0.92      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.48/0.92      | ~ v1_relat_1(X0)
% 2.48/0.92      | k2_funct_1(sK2) != X0
% 2.48/0.92      | k1_relat_1(X0) != sK1
% 2.48/0.92      | k2_relat_1(X0) != sK0 ),
% 2.48/0.92      inference(resolution_lifted,[status(thm)],[c_19,c_21]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_490,plain,
% 2.48/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.48/0.92      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.48/0.92      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.48/0.92      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.48/0.92      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.48/0.92      inference(unflattening,[status(thm)],[c_489]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_582,plain,
% 2.48/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.48/0.92      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.48/0.92      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.48/0.92      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.48/0.92      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_490]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1081,plain,
% 2.48/0.92      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.48/0.92      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.48/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.48/0.92      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.48/0.92      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_676,plain,
% 2.48/0.92      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.48/0.92      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.48/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.48/0.92      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.48/0.92      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_6,plain,
% 2.48/0.92      ( ~ v1_funct_1(X0)
% 2.48/0.92      | ~ v1_relat_1(X0)
% 2.48/0.92      | v1_relat_1(k2_funct_1(X0)) ),
% 2.48/0.92      inference(cnf_transformation,[],[f38]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_602,plain,
% 2.48/0.92      ( ~ v1_funct_1(X0_46)
% 2.48/0.92      | ~ v1_relat_1(X0_46)
% 2.48/0.92      | v1_relat_1(k2_funct_1(X0_46)) ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_6]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1299,plain,
% 2.48/0.92      ( ~ v1_funct_1(sK2)
% 2.48/0.92      | v1_relat_1(k2_funct_1(sK2))
% 2.48/0.92      | ~ v1_relat_1(sK2) ),
% 2.48/0.92      inference(instantiation,[status(thm)],[c_602]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1300,plain,
% 2.48/0.92      ( v1_funct_1(sK2) != iProver_top
% 2.48/0.92      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.48/0.92      | v1_relat_1(sK2) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_1299]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1302,plain,
% 2.48/0.92      ( v1_funct_1(k2_funct_1(sK2))
% 2.48/0.92      | ~ v1_funct_1(sK2)
% 2.48/0.92      | ~ v1_relat_1(sK2) ),
% 2.48/0.92      inference(instantiation,[status(thm)],[c_603]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1303,plain,
% 2.48/0.92      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.48/0.92      | v1_funct_1(sK2) != iProver_top
% 2.48/0.92      | v1_relat_1(sK2) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_1302]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1593,plain,
% 2.48/0.92      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.48/0.92      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.48/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.48/0.92      inference(global_propositional_subsumption,
% 2.48/0.92                [status(thm)],
% 2.48/0.92                [c_1081,c_27,c_676,c_1300,c_1303,c_1426,c_1496]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1710,plain,
% 2.48/0.92      ( k1_relat_1(k4_relat_1(sK2)) != sK1
% 2.48/0.92      | k2_relat_1(k4_relat_1(sK2)) != sK0
% 2.48/0.92      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.48/0.92      inference(demodulation,[status(thm)],[c_1543,c_1593]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2275,plain,
% 2.48/0.92      ( k2_relat_1(k4_relat_1(sK2)) != sK0
% 2.48/0.92      | k1_relat_1(k4_relat_1(sK2)) != sK1 ),
% 2.48/0.92      inference(global_propositional_subsumption,
% 2.48/0.92                [status(thm)],
% 2.48/0.92                [c_1710,c_29,c_2110]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2276,plain,
% 2.48/0.92      ( k1_relat_1(k4_relat_1(sK2)) != sK1
% 2.48/0.92      | k2_relat_1(k4_relat_1(sK2)) != sK0 ),
% 2.48/0.92      inference(renaming,[status(thm)],[c_2275]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2,plain,
% 2.48/0.92      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 2.48/0.92      inference(cnf_transformation,[],[f36]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_605,plain,
% 2.48/0.92      ( ~ v1_relat_1(X0_46)
% 2.48/0.92      | k2_relat_1(k4_relat_1(X0_46)) = k1_relat_1(X0_46) ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_2]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1060,plain,
% 2.48/0.92      ( k2_relat_1(k4_relat_1(X0_46)) = k1_relat_1(X0_46)
% 2.48/0.92      | v1_relat_1(X0_46) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1545,plain,
% 2.48/0.92      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.48/0.92      inference(superposition,[status(thm)],[c_1538,c_1060]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2277,plain,
% 2.48/0.92      ( k1_relat_1(sK2) != sK0 | k2_relat_1(sK2) != sK1 ),
% 2.48/0.92      inference(light_normalisation,[status(thm)],[c_2276,c_1544,c_1545]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2587,plain,
% 2.48/0.92      ( k1_relat_1(sK2) != k1_xboole_0 | k2_relat_1(sK2) != sK1 ),
% 2.48/0.92      inference(demodulation,[status(thm)],[c_2581,c_2277]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1898,plain,
% 2.48/0.92      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.48/0.92      inference(superposition,[status(thm)],[c_1070,c_1065]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2592,plain,
% 2.48/0.92      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.48/0.92      inference(demodulation,[status(thm)],[c_2581,c_1898]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_16,plain,
% 2.48/0.92      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.48/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.48/0.92      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.48/0.92      inference(cnf_transformation,[],[f64]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_25,negated_conjecture,
% 2.48/0.92      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.48/0.92      inference(cnf_transformation,[],[f55]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_425,plain,
% 2.48/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.48/0.92      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.48/0.92      | sK0 != k1_xboole_0
% 2.48/0.92      | sK1 != X1
% 2.48/0.92      | sK2 != X0 ),
% 2.48/0.92      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_426,plain,
% 2.48/0.92      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.48/0.92      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 2.48/0.92      | sK0 != k1_xboole_0 ),
% 2.48/0.92      inference(unflattening,[status(thm)],[c_425]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_586,plain,
% 2.48/0.92      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.48/0.92      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 2.48/0.92      | sK0 != k1_xboole_0 ),
% 2.48/0.92      inference(subtyping,[status(esa)],[c_426]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_1078,plain,
% 2.48/0.92      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 2.48/0.92      | sK0 != k1_xboole_0
% 2.48/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.48/0.92      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2594,plain,
% 2.48/0.92      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 2.48/0.92      | k1_xboole_0 != k1_xboole_0
% 2.48/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.48/0.92      inference(demodulation,[status(thm)],[c_2581,c_1078]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2606,plain,
% 2.48/0.92      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 2.48/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.48/0.92      inference(equality_resolution_simp,[status(thm)],[c_2594]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2596,plain,
% 2.48/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 2.48/0.92      inference(demodulation,[status(thm)],[c_2581,c_1070]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2609,plain,
% 2.48/0.92      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0 ),
% 2.48/0.92      inference(forward_subsumption_resolution,
% 2.48/0.92                [status(thm)],
% 2.48/0.92                [c_2606,c_2596]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2611,plain,
% 2.48/0.92      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 2.48/0.92      inference(light_normalisation,[status(thm)],[c_2592,c_2609]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2621,plain,
% 2.48/0.92      ( k2_relat_1(sK2) != sK1 | k1_xboole_0 != k1_xboole_0 ),
% 2.48/0.92      inference(light_normalisation,[status(thm)],[c_2587,c_2611]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(c_2622,plain,
% 2.48/0.92      ( k2_relat_1(sK2) != sK1 ),
% 2.48/0.92      inference(equality_resolution_simp,[status(thm)],[c_2621]) ).
% 2.48/0.92  
% 2.48/0.92  cnf(contradiction,plain,
% 2.48/0.92      ( $false ),
% 2.48/0.92      inference(minisat,[status(thm)],[c_3493,c_2622]) ).
% 2.48/0.92  
% 2.48/0.92  
% 2.48/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 2.48/0.92  
% 2.48/0.92  ------                               Statistics
% 2.48/0.92  
% 2.48/0.92  ------ General
% 2.48/0.92  
% 2.48/0.92  abstr_ref_over_cycles:                  0
% 2.48/0.92  abstr_ref_under_cycles:                 0
% 2.48/0.92  gc_basic_clause_elim:                   0
% 2.48/0.92  forced_gc_time:                         0
% 2.48/0.92  parsing_time:                           0.01
% 2.48/0.92  unif_index_cands_time:                  0.
% 2.48/0.92  unif_index_add_time:                    0.
% 2.48/0.92  orderings_time:                         0.
% 2.48/0.92  out_proof_time:                         0.01
% 2.48/0.92  total_time:                             0.166
% 2.48/0.92  num_of_symbols:                         51
% 2.48/0.92  num_of_terms:                           3118
% 2.48/0.92  
% 2.48/0.92  ------ Preprocessing
% 2.48/0.92  
% 2.48/0.92  num_of_splits:                          0
% 2.48/0.92  num_of_split_atoms:                     0
% 2.48/0.92  num_of_reused_defs:                     0
% 2.48/0.92  num_eq_ax_congr_red:                    8
% 2.48/0.92  num_of_sem_filtered_clauses:            1
% 2.48/0.92  num_of_subtypes:                        2
% 2.48/0.92  monotx_restored_types:                  0
% 2.48/0.92  sat_num_of_epr_types:                   0
% 2.48/0.92  sat_num_of_non_cyclic_types:            0
% 2.48/0.92  sat_guarded_non_collapsed_types:        1
% 2.48/0.92  num_pure_diseq_elim:                    0
% 2.48/0.92  simp_replaced_by:                       0
% 2.48/0.92  res_preprocessed:                       109
% 2.48/0.92  prep_upred:                             0
% 2.48/0.92  prep_unflattend:                        42
% 2.48/0.92  smt_new_axioms:                         0
% 2.48/0.92  pred_elim_cands:                        5
% 2.48/0.92  pred_elim:                              2
% 2.48/0.92  pred_elim_cl:                           -1
% 2.48/0.92  pred_elim_cycles:                       3
% 2.48/0.92  merged_defs:                            0
% 2.48/0.92  merged_defs_ncl:                        0
% 2.48/0.92  bin_hyper_res:                          0
% 2.48/0.92  prep_cycles:                            3
% 2.48/0.92  pred_elim_time:                         0.006
% 2.48/0.92  splitting_time:                         0.
% 2.48/0.92  sem_filter_time:                        0.
% 2.48/0.92  monotx_time:                            0.
% 2.48/0.92  subtype_inf_time:                       0.001
% 2.48/0.92  
% 2.48/0.92  ------ Problem properties
% 2.48/0.92  
% 2.48/0.92  clauses:                                27
% 2.48/0.92  conjectures:                            3
% 2.48/0.92  epr:                                    1
% 2.48/0.92  horn:                                   23
% 2.48/0.92  ground:                                 12
% 2.48/0.92  unary:                                  4
% 2.48/0.92  binary:                                 9
% 2.48/0.92  lits:                                   80
% 2.48/0.92  lits_eq:                                33
% 2.48/0.92  fd_pure:                                0
% 2.48/0.92  fd_pseudo:                              0
% 2.48/0.92  fd_cond:                                1
% 2.48/0.92  fd_pseudo_cond:                         0
% 2.48/0.92  ac_symbols:                             0
% 2.48/0.92  
% 2.48/0.92  ------ Propositional Solver
% 2.48/0.92  
% 2.48/0.92  prop_solver_calls:                      24
% 2.48/0.92  prop_fast_solver_calls:                 825
% 2.48/0.92  smt_solver_calls:                       0
% 2.48/0.92  smt_fast_solver_calls:                  0
% 2.48/0.92  prop_num_of_clauses:                    1158
% 2.48/0.92  prop_preprocess_simplified:             4070
% 2.48/0.92  prop_fo_subsumed:                       25
% 2.48/0.92  prop_solver_time:                       0.
% 2.48/0.92  smt_solver_time:                        0.
% 2.48/0.92  smt_fast_solver_time:                   0.
% 2.48/0.92  prop_fast_solver_time:                  0.
% 2.48/0.92  prop_unsat_core_time:                   0.
% 2.48/0.92  
% 2.48/0.92  ------ QBF
% 2.48/0.92  
% 2.48/0.92  qbf_q_res:                              0
% 2.48/0.92  qbf_num_tautologies:                    0
% 2.48/0.92  qbf_prep_cycles:                        0
% 2.48/0.92  
% 2.48/0.92  ------ BMC1
% 2.48/0.92  
% 2.48/0.92  bmc1_current_bound:                     -1
% 2.48/0.92  bmc1_last_solved_bound:                 -1
% 2.48/0.92  bmc1_unsat_core_size:                   -1
% 2.48/0.92  bmc1_unsat_core_parents_size:           -1
% 2.48/0.92  bmc1_merge_next_fun:                    0
% 2.48/0.92  bmc1_unsat_core_clauses_time:           0.
% 2.48/0.92  
% 2.48/0.92  ------ Instantiation
% 2.48/0.92  
% 2.48/0.92  inst_num_of_clauses:                    412
% 2.48/0.92  inst_num_in_passive:                    117
% 2.48/0.92  inst_num_in_active:                     250
% 2.48/0.92  inst_num_in_unprocessed:                45
% 2.48/0.92  inst_num_of_loops:                      290
% 2.48/0.92  inst_num_of_learning_restarts:          0
% 2.48/0.92  inst_num_moves_active_passive:          37
% 2.48/0.92  inst_lit_activity:                      0
% 2.48/0.92  inst_lit_activity_moves:                0
% 2.48/0.92  inst_num_tautologies:                   0
% 2.48/0.92  inst_num_prop_implied:                  0
% 2.48/0.92  inst_num_existing_simplified:           0
% 2.48/0.92  inst_num_eq_res_simplified:             0
% 2.48/0.92  inst_num_child_elim:                    0
% 2.48/0.92  inst_num_of_dismatching_blockings:      70
% 2.48/0.92  inst_num_of_non_proper_insts:           282
% 2.48/0.92  inst_num_of_duplicates:                 0
% 2.48/0.92  inst_inst_num_from_inst_to_res:         0
% 2.48/0.92  inst_dismatching_checking_time:         0.
% 2.48/0.92  
% 2.48/0.92  ------ Resolution
% 2.48/0.92  
% 2.48/0.92  res_num_of_clauses:                     0
% 2.48/0.92  res_num_in_passive:                     0
% 2.48/0.92  res_num_in_active:                      0
% 2.48/0.92  res_num_of_loops:                       112
% 2.48/0.92  res_forward_subset_subsumed:            35
% 2.48/0.92  res_backward_subset_subsumed:           4
% 2.48/0.92  res_forward_subsumed:                   0
% 2.48/0.92  res_backward_subsumed:                  0
% 2.48/0.92  res_forward_subsumption_resolution:     0
% 2.48/0.92  res_backward_subsumption_resolution:    0
% 2.48/0.92  res_clause_to_clause_subsumption:       121
% 2.48/0.92  res_orphan_elimination:                 0
% 2.48/0.92  res_tautology_del:                      60
% 2.48/0.92  res_num_eq_res_simplified:              0
% 2.48/0.92  res_num_sel_changes:                    0
% 2.48/0.92  res_moves_from_active_to_pass:          0
% 2.48/0.92  
% 2.48/0.92  ------ Superposition
% 2.48/0.92  
% 2.48/0.92  sup_time_total:                         0.
% 2.48/0.92  sup_time_generating:                    0.
% 2.48/0.92  sup_time_sim_full:                      0.
% 2.48/0.92  sup_time_sim_immed:                     0.
% 2.48/0.92  
% 2.48/0.92  sup_num_of_clauses:                     70
% 2.48/0.92  sup_num_in_active:                      34
% 2.48/0.92  sup_num_in_passive:                     36
% 2.48/0.92  sup_num_of_loops:                       57
% 2.48/0.92  sup_fw_superposition:                   18
% 2.48/0.92  sup_bw_superposition:                   42
% 2.48/0.92  sup_immediate_simplified:               24
% 2.48/0.92  sup_given_eliminated:                   0
% 2.48/0.92  comparisons_done:                       0
% 2.48/0.92  comparisons_avoided:                    5
% 2.48/0.92  
% 2.48/0.92  ------ Simplifications
% 2.48/0.92  
% 2.48/0.92  
% 2.48/0.92  sim_fw_subset_subsumed:                 4
% 2.48/0.92  sim_bw_subset_subsumed:                 4
% 2.48/0.92  sim_fw_subsumed:                        0
% 2.48/0.92  sim_bw_subsumed:                        0
% 2.48/0.92  sim_fw_subsumption_res:                 1
% 2.48/0.92  sim_bw_subsumption_res:                 0
% 2.48/0.92  sim_tautology_del:                      1
% 2.48/0.92  sim_eq_tautology_del:                   1
% 2.48/0.92  sim_eq_res_simp:                        2
% 2.48/0.92  sim_fw_demodulated:                     2
% 2.48/0.92  sim_bw_demodulated:                     23
% 2.48/0.92  sim_light_normalised:                   23
% 2.48/0.92  sim_joinable_taut:                      0
% 2.48/0.92  sim_joinable_simp:                      0
% 2.48/0.92  sim_ac_normalised:                      0
% 2.48/0.92  sim_smt_subsumption:                    0
% 2.48/0.92  
%------------------------------------------------------------------------------

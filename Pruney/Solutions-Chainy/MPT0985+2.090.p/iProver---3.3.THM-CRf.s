%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:38 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  150 (4914 expanded)
%              Number of clauses        :   97 (1798 expanded)
%              Number of leaves         :   16 ( 905 expanded)
%              Depth                    :   25
%              Number of atoms          :  402 (25029 expanded)
%              Number of equality atoms :  196 (5328 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f34,plain,
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

fof(f35,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f34])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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

fof(f33,plain,(
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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_632,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1302,plain,
    ( X0_48 != X1_48
    | X0_48 = sK2
    | sK2 != X1_48 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_2876,plain,
    ( k2_funct_1(sK2) != X0_48
    | k2_funct_1(sK2) = sK2
    | sK2 != X0_48 ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_2877,plain,
    ( k2_funct_1(sK2) = sK2
    | k2_funct_1(sK2) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2876])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_615,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1005,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k1_relset_1(X2_48,X1_48,k3_relset_1(X1_48,X2_48,X0_48)) = k2_relset_1(X1_48,X2_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1004,plain,
    ( k1_relset_1(X0_48,X1_48,k3_relset_1(X1_48,X0_48,X2_48)) = k2_relset_1(X1_48,X0_48,X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_2207,plain,
    ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) = k2_relset_1(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1005,c_1004])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_616,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k3_relset_1(X1_48,X2_48,X0_48) = k4_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1002,plain,
    ( k3_relset_1(X0_48,X1_48,X2_48) = k4_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_1881,plain,
    ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1005,c_1002])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_288,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_289,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_291,plain,
    ( ~ v1_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_25])).

cnf(c_612,plain,
    ( ~ v1_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_291])).

cnf(c_1008,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1179,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_1197,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1008,c_23,c_612,c_1179])).

cnf(c_1888,plain,
    ( k3_relset_1(sK0,sK1,sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1881,c_1197])).

cnf(c_2214,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2207,c_616,c_1888])).

cnf(c_17,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_392,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_607,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_392])).

cnf(c_1013,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_26,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_690,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_624,plain,
    ( ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_1(X0_48))
    | ~ v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1176,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_1177,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1176])).

cnf(c_1180,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1179])).

cnf(c_1233,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_xboole_0 = sK0
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1013,c_26,c_28,c_690,c_1177,c_1180])).

cnf(c_1234,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1233])).

cnf(c_2223,plain,
    ( sK0 = k1_xboole_0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2214,c_1234])).

cnf(c_2427,plain,
    ( sK0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2223])).

cnf(c_1194,plain,
    ( sK0 != X0_48
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0_48 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_1319,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1194])).

cnf(c_629,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1320,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | m1_subset_1(k3_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1000,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(k3_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_1976,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1888,c_1000])).

cnf(c_2429,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2427,c_26,c_28,c_690,c_1177,c_1180,c_1319,c_1320,c_1976,c_2214])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_270,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_8,c_1])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_8,c_7,c_1])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k7_relat_1(X0_48,X1_48) = X0_48 ),
    inference(subtyping,[status(esa)],[c_272])).

cnf(c_1007,plain,
    ( k7_relat_1(X0_48,X1_48) = X0_48
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_1642,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_1005,c_1007])).

cnf(c_2437,plain,
    ( k7_relat_1(sK2,k1_xboole_0) = sK2 ),
    inference(demodulation,[status(thm)],[c_2429,c_1642])).

cnf(c_999,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_1388,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1005,c_999])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_627,plain,
    ( ~ v1_relat_1(X0_48)
    | k7_relat_1(X0_48,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_996,plain,
    ( k7_relat_1(X0_48,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_1392,plain,
    ( k7_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1388,c_996])).

cnf(c_2483,plain,
    ( sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2437,c_1392])).

cnf(c_2444,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2429,c_1005])).

cnf(c_2488,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2483,c_2444])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1001,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_2659,plain,
    ( k2_relset_1(k1_xboole_0,sK1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2488,c_1001])).

cnf(c_2,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_626,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2445,plain,
    ( k2_relset_1(k1_xboole_0,sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_2429,c_616])).

cnf(c_2489,plain,
    ( k2_relset_1(k1_xboole_0,sK1,k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_2483,c_2445])).

cnf(c_2668,plain,
    ( sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2659,c_626,c_2489])).

cnf(c_2019,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1976,c_28])).

cnf(c_2024,plain,
    ( k7_relat_1(k2_funct_1(sK2),sK1) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_2019,c_1007])).

cnf(c_2681,plain,
    ( k7_relat_1(k2_funct_1(sK2),k1_xboole_0) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2668,c_2024])).

cnf(c_2025,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2019,c_999])).

cnf(c_2066,plain,
    ( k7_relat_1(k2_funct_1(sK2),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2025,c_996])).

cnf(c_2686,plain,
    ( k2_funct_1(sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2681,c_2066])).

cnf(c_1267,plain,
    ( sK0 != X0_48
    | sK0 = sK1
    | sK1 != X0_48 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_1268,plain,
    ( sK0 = sK1
    | sK0 != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_418,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != sK2
    | sK0 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_605,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != sK2
    | sK0 != sK1 ),
    inference(subtyping,[status(esa)],[c_418])).

cnf(c_691,plain,
    ( k2_funct_1(sK2) != sK2
    | sK0 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2877,c_2686,c_2668,c_2483,c_2214,c_1976,c_1320,c_1319,c_1268,c_1180,c_1177,c_691,c_690,c_28,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:47:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.33/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/0.97  
% 2.33/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/0.97  
% 2.33/0.97  ------  iProver source info
% 2.33/0.97  
% 2.33/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.33/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/0.97  git: non_committed_changes: false
% 2.33/0.97  git: last_make_outside_of_git: false
% 2.33/0.97  
% 2.33/0.97  ------ 
% 2.33/0.97  
% 2.33/0.97  ------ Input Options
% 2.33/0.97  
% 2.33/0.97  --out_options                           all
% 2.33/0.97  --tptp_safe_out                         true
% 2.33/0.97  --problem_path                          ""
% 2.33/0.97  --include_path                          ""
% 2.33/0.97  --clausifier                            res/vclausify_rel
% 2.33/0.97  --clausifier_options                    --mode clausify
% 2.33/0.97  --stdin                                 false
% 2.33/0.97  --stats_out                             all
% 2.33/0.97  
% 2.33/0.97  ------ General Options
% 2.33/0.97  
% 2.33/0.97  --fof                                   false
% 2.33/0.97  --time_out_real                         305.
% 2.33/0.97  --time_out_virtual                      -1.
% 2.33/0.97  --symbol_type_check                     false
% 2.33/0.97  --clausify_out                          false
% 2.33/0.97  --sig_cnt_out                           false
% 2.33/0.97  --trig_cnt_out                          false
% 2.33/0.97  --trig_cnt_out_tolerance                1.
% 2.33/0.97  --trig_cnt_out_sk_spl                   false
% 2.33/0.97  --abstr_cl_out                          false
% 2.33/0.97  
% 2.33/0.97  ------ Global Options
% 2.33/0.97  
% 2.33/0.97  --schedule                              default
% 2.33/0.97  --add_important_lit                     false
% 2.33/0.97  --prop_solver_per_cl                    1000
% 2.33/0.97  --min_unsat_core                        false
% 2.33/0.97  --soft_assumptions                      false
% 2.33/0.97  --soft_lemma_size                       3
% 2.33/0.97  --prop_impl_unit_size                   0
% 2.33/0.97  --prop_impl_unit                        []
% 2.33/0.97  --share_sel_clauses                     true
% 2.33/0.97  --reset_solvers                         false
% 2.33/0.97  --bc_imp_inh                            [conj_cone]
% 2.33/0.97  --conj_cone_tolerance                   3.
% 2.33/0.97  --extra_neg_conj                        none
% 2.33/0.97  --large_theory_mode                     true
% 2.33/0.97  --prolific_symb_bound                   200
% 2.33/0.97  --lt_threshold                          2000
% 2.33/0.97  --clause_weak_htbl                      true
% 2.33/0.97  --gc_record_bc_elim                     false
% 2.33/0.97  
% 2.33/0.97  ------ Preprocessing Options
% 2.33/0.97  
% 2.33/0.97  --preprocessing_flag                    true
% 2.33/0.97  --time_out_prep_mult                    0.1
% 2.33/0.97  --splitting_mode                        input
% 2.33/0.97  --splitting_grd                         true
% 2.33/0.97  --splitting_cvd                         false
% 2.33/0.97  --splitting_cvd_svl                     false
% 2.33/0.97  --splitting_nvd                         32
% 2.33/0.97  --sub_typing                            true
% 2.33/0.97  --prep_gs_sim                           true
% 2.33/0.97  --prep_unflatten                        true
% 2.33/0.97  --prep_res_sim                          true
% 2.33/0.97  --prep_upred                            true
% 2.33/0.97  --prep_sem_filter                       exhaustive
% 2.33/0.97  --prep_sem_filter_out                   false
% 2.33/0.97  --pred_elim                             true
% 2.33/0.97  --res_sim_input                         true
% 2.33/0.97  --eq_ax_congr_red                       true
% 2.33/0.97  --pure_diseq_elim                       true
% 2.33/0.97  --brand_transform                       false
% 2.33/0.97  --non_eq_to_eq                          false
% 2.33/0.97  --prep_def_merge                        true
% 2.33/0.97  --prep_def_merge_prop_impl              false
% 2.33/0.97  --prep_def_merge_mbd                    true
% 2.33/0.97  --prep_def_merge_tr_red                 false
% 2.33/0.97  --prep_def_merge_tr_cl                  false
% 2.33/0.97  --smt_preprocessing                     true
% 2.33/0.97  --smt_ac_axioms                         fast
% 2.33/0.97  --preprocessed_out                      false
% 2.33/0.97  --preprocessed_stats                    false
% 2.33/0.97  
% 2.33/0.97  ------ Abstraction refinement Options
% 2.33/0.97  
% 2.33/0.97  --abstr_ref                             []
% 2.33/0.97  --abstr_ref_prep                        false
% 2.33/0.97  --abstr_ref_until_sat                   false
% 2.33/0.97  --abstr_ref_sig_restrict                funpre
% 2.33/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.97  --abstr_ref_under                       []
% 2.33/0.97  
% 2.33/0.97  ------ SAT Options
% 2.33/0.97  
% 2.33/0.97  --sat_mode                              false
% 2.33/0.97  --sat_fm_restart_options                ""
% 2.33/0.97  --sat_gr_def                            false
% 2.33/0.97  --sat_epr_types                         true
% 2.33/0.97  --sat_non_cyclic_types                  false
% 2.33/0.97  --sat_finite_models                     false
% 2.33/0.97  --sat_fm_lemmas                         false
% 2.33/0.97  --sat_fm_prep                           false
% 2.33/0.97  --sat_fm_uc_incr                        true
% 2.33/0.97  --sat_out_model                         small
% 2.33/0.97  --sat_out_clauses                       false
% 2.33/0.97  
% 2.33/0.97  ------ QBF Options
% 2.33/0.97  
% 2.33/0.97  --qbf_mode                              false
% 2.33/0.97  --qbf_elim_univ                         false
% 2.33/0.97  --qbf_dom_inst                          none
% 2.33/0.97  --qbf_dom_pre_inst                      false
% 2.33/0.97  --qbf_sk_in                             false
% 2.33/0.97  --qbf_pred_elim                         true
% 2.33/0.97  --qbf_split                             512
% 2.33/0.97  
% 2.33/0.97  ------ BMC1 Options
% 2.33/0.97  
% 2.33/0.97  --bmc1_incremental                      false
% 2.33/0.97  --bmc1_axioms                           reachable_all
% 2.33/0.97  --bmc1_min_bound                        0
% 2.33/0.97  --bmc1_max_bound                        -1
% 2.33/0.97  --bmc1_max_bound_default                -1
% 2.33/0.97  --bmc1_symbol_reachability              true
% 2.33/0.97  --bmc1_property_lemmas                  false
% 2.33/0.97  --bmc1_k_induction                      false
% 2.33/0.97  --bmc1_non_equiv_states                 false
% 2.33/0.97  --bmc1_deadlock                         false
% 2.33/0.97  --bmc1_ucm                              false
% 2.33/0.97  --bmc1_add_unsat_core                   none
% 2.33/0.97  --bmc1_unsat_core_children              false
% 2.33/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.97  --bmc1_out_stat                         full
% 2.33/0.97  --bmc1_ground_init                      false
% 2.33/0.97  --bmc1_pre_inst_next_state              false
% 2.33/0.97  --bmc1_pre_inst_state                   false
% 2.33/0.97  --bmc1_pre_inst_reach_state             false
% 2.33/0.97  --bmc1_out_unsat_core                   false
% 2.33/0.97  --bmc1_aig_witness_out                  false
% 2.33/0.97  --bmc1_verbose                          false
% 2.33/0.97  --bmc1_dump_clauses_tptp                false
% 2.33/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.97  --bmc1_dump_file                        -
% 2.33/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.97  --bmc1_ucm_extend_mode                  1
% 2.33/0.97  --bmc1_ucm_init_mode                    2
% 2.33/0.97  --bmc1_ucm_cone_mode                    none
% 2.33/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.97  --bmc1_ucm_relax_model                  4
% 2.33/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.97  --bmc1_ucm_layered_model                none
% 2.33/0.97  --bmc1_ucm_max_lemma_size               10
% 2.33/0.97  
% 2.33/0.97  ------ AIG Options
% 2.33/0.97  
% 2.33/0.97  --aig_mode                              false
% 2.33/0.97  
% 2.33/0.97  ------ Instantiation Options
% 2.33/0.97  
% 2.33/0.97  --instantiation_flag                    true
% 2.33/0.97  --inst_sos_flag                         false
% 2.33/0.97  --inst_sos_phase                        true
% 2.33/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.97  --inst_lit_sel_side                     num_symb
% 2.33/0.97  --inst_solver_per_active                1400
% 2.33/0.97  --inst_solver_calls_frac                1.
% 2.33/0.97  --inst_passive_queue_type               priority_queues
% 2.33/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.97  --inst_passive_queues_freq              [25;2]
% 2.33/0.97  --inst_dismatching                      true
% 2.33/0.97  --inst_eager_unprocessed_to_passive     true
% 2.33/0.97  --inst_prop_sim_given                   true
% 2.33/0.97  --inst_prop_sim_new                     false
% 2.33/0.97  --inst_subs_new                         false
% 2.33/0.97  --inst_eq_res_simp                      false
% 2.33/0.97  --inst_subs_given                       false
% 2.33/0.97  --inst_orphan_elimination               true
% 2.33/0.97  --inst_learning_loop_flag               true
% 2.33/0.97  --inst_learning_start                   3000
% 2.33/0.97  --inst_learning_factor                  2
% 2.33/0.97  --inst_start_prop_sim_after_learn       3
% 2.33/0.97  --inst_sel_renew                        solver
% 2.33/0.97  --inst_lit_activity_flag                true
% 2.33/0.97  --inst_restr_to_given                   false
% 2.33/0.97  --inst_activity_threshold               500
% 2.33/0.97  --inst_out_proof                        true
% 2.33/0.97  
% 2.33/0.97  ------ Resolution Options
% 2.33/0.97  
% 2.33/0.97  --resolution_flag                       true
% 2.33/0.97  --res_lit_sel                           adaptive
% 2.33/0.97  --res_lit_sel_side                      none
% 2.33/0.97  --res_ordering                          kbo
% 2.33/0.97  --res_to_prop_solver                    active
% 2.33/0.97  --res_prop_simpl_new                    false
% 2.33/0.97  --res_prop_simpl_given                  true
% 2.33/0.97  --res_passive_queue_type                priority_queues
% 2.33/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.97  --res_passive_queues_freq               [15;5]
% 2.33/0.97  --res_forward_subs                      full
% 2.33/0.97  --res_backward_subs                     full
% 2.33/0.97  --res_forward_subs_resolution           true
% 2.33/0.97  --res_backward_subs_resolution          true
% 2.33/0.97  --res_orphan_elimination                true
% 2.33/0.97  --res_time_limit                        2.
% 2.33/0.97  --res_out_proof                         true
% 2.33/0.97  
% 2.33/0.97  ------ Superposition Options
% 2.33/0.97  
% 2.33/0.97  --superposition_flag                    true
% 2.33/0.97  --sup_passive_queue_type                priority_queues
% 2.33/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.97  --demod_completeness_check              fast
% 2.33/0.97  --demod_use_ground                      true
% 2.33/0.97  --sup_to_prop_solver                    passive
% 2.33/0.97  --sup_prop_simpl_new                    true
% 2.33/0.97  --sup_prop_simpl_given                  true
% 2.33/0.97  --sup_fun_splitting                     false
% 2.33/0.97  --sup_smt_interval                      50000
% 2.33/0.97  
% 2.33/0.97  ------ Superposition Simplification Setup
% 2.33/0.97  
% 2.33/0.97  --sup_indices_passive                   []
% 2.33/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.97  --sup_full_bw                           [BwDemod]
% 2.33/0.97  --sup_immed_triv                        [TrivRules]
% 2.33/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.97  --sup_immed_bw_main                     []
% 2.33/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.97  
% 2.33/0.97  ------ Combination Options
% 2.33/0.97  
% 2.33/0.97  --comb_res_mult                         3
% 2.33/0.97  --comb_sup_mult                         2
% 2.33/0.97  --comb_inst_mult                        10
% 2.33/0.97  
% 2.33/0.97  ------ Debug Options
% 2.33/0.97  
% 2.33/0.97  --dbg_backtrace                         false
% 2.33/0.97  --dbg_dump_prop_clauses                 false
% 2.33/0.97  --dbg_dump_prop_clauses_file            -
% 2.33/0.97  --dbg_out_stat                          false
% 2.33/0.97  ------ Parsing...
% 2.33/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/0.97  
% 2.33/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.33/0.97  
% 2.33/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.97  
% 2.33/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.97  ------ Proving...
% 2.33/0.97  ------ Problem Properties 
% 2.33/0.97  
% 2.33/0.97  
% 2.33/0.97  clauses                                 23
% 2.33/0.97  conjectures                             3
% 2.33/0.97  EPR                                     1
% 2.33/0.97  Horn                                    21
% 2.33/0.97  unary                                   5
% 2.33/0.97  binary                                  10
% 2.33/0.97  lits                                    57
% 2.33/0.97  lits eq                                 26
% 2.33/0.97  fd_pure                                 0
% 2.33/0.97  fd_pseudo                               0
% 2.33/0.97  fd_cond                                 0
% 2.33/0.97  fd_pseudo_cond                          0
% 2.33/0.97  AC symbols                              0
% 2.33/0.97  
% 2.33/0.97  ------ Schedule dynamic 5 is on 
% 2.33/0.97  
% 2.33/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/0.97  
% 2.33/0.97  
% 2.33/0.97  ------ 
% 2.33/0.97  Current options:
% 2.33/0.97  ------ 
% 2.33/0.97  
% 2.33/0.97  ------ Input Options
% 2.33/0.97  
% 2.33/0.97  --out_options                           all
% 2.33/0.97  --tptp_safe_out                         true
% 2.33/0.97  --problem_path                          ""
% 2.33/0.97  --include_path                          ""
% 2.33/0.97  --clausifier                            res/vclausify_rel
% 2.33/0.97  --clausifier_options                    --mode clausify
% 2.33/0.97  --stdin                                 false
% 2.33/0.97  --stats_out                             all
% 2.33/0.97  
% 2.33/0.97  ------ General Options
% 2.33/0.97  
% 2.33/0.97  --fof                                   false
% 2.33/0.97  --time_out_real                         305.
% 2.33/0.97  --time_out_virtual                      -1.
% 2.33/0.97  --symbol_type_check                     false
% 2.33/0.97  --clausify_out                          false
% 2.33/0.97  --sig_cnt_out                           false
% 2.33/0.97  --trig_cnt_out                          false
% 2.33/0.97  --trig_cnt_out_tolerance                1.
% 2.33/0.97  --trig_cnt_out_sk_spl                   false
% 2.33/0.97  --abstr_cl_out                          false
% 2.33/0.97  
% 2.33/0.97  ------ Global Options
% 2.33/0.97  
% 2.33/0.97  --schedule                              default
% 2.33/0.97  --add_important_lit                     false
% 2.33/0.97  --prop_solver_per_cl                    1000
% 2.33/0.97  --min_unsat_core                        false
% 2.33/0.97  --soft_assumptions                      false
% 2.33/0.97  --soft_lemma_size                       3
% 2.33/0.97  --prop_impl_unit_size                   0
% 2.33/0.97  --prop_impl_unit                        []
% 2.33/0.97  --share_sel_clauses                     true
% 2.33/0.97  --reset_solvers                         false
% 2.33/0.97  --bc_imp_inh                            [conj_cone]
% 2.33/0.97  --conj_cone_tolerance                   3.
% 2.33/0.97  --extra_neg_conj                        none
% 2.33/0.97  --large_theory_mode                     true
% 2.33/0.97  --prolific_symb_bound                   200
% 2.33/0.97  --lt_threshold                          2000
% 2.33/0.97  --clause_weak_htbl                      true
% 2.33/0.97  --gc_record_bc_elim                     false
% 2.33/0.97  
% 2.33/0.97  ------ Preprocessing Options
% 2.33/0.97  
% 2.33/0.97  --preprocessing_flag                    true
% 2.33/0.97  --time_out_prep_mult                    0.1
% 2.33/0.97  --splitting_mode                        input
% 2.33/0.97  --splitting_grd                         true
% 2.33/0.97  --splitting_cvd                         false
% 2.33/0.97  --splitting_cvd_svl                     false
% 2.33/0.97  --splitting_nvd                         32
% 2.33/0.97  --sub_typing                            true
% 2.33/0.97  --prep_gs_sim                           true
% 2.33/0.97  --prep_unflatten                        true
% 2.33/0.97  --prep_res_sim                          true
% 2.33/0.97  --prep_upred                            true
% 2.33/0.97  --prep_sem_filter                       exhaustive
% 2.33/0.97  --prep_sem_filter_out                   false
% 2.33/0.97  --pred_elim                             true
% 2.33/0.97  --res_sim_input                         true
% 2.33/0.97  --eq_ax_congr_red                       true
% 2.33/0.97  --pure_diseq_elim                       true
% 2.33/0.97  --brand_transform                       false
% 2.33/0.97  --non_eq_to_eq                          false
% 2.33/0.97  --prep_def_merge                        true
% 2.33/0.97  --prep_def_merge_prop_impl              false
% 2.33/0.97  --prep_def_merge_mbd                    true
% 2.33/0.97  --prep_def_merge_tr_red                 false
% 2.33/0.97  --prep_def_merge_tr_cl                  false
% 2.33/0.97  --smt_preprocessing                     true
% 2.33/0.97  --smt_ac_axioms                         fast
% 2.33/0.97  --preprocessed_out                      false
% 2.33/0.97  --preprocessed_stats                    false
% 2.33/0.97  
% 2.33/0.97  ------ Abstraction refinement Options
% 2.33/0.97  
% 2.33/0.97  --abstr_ref                             []
% 2.33/0.97  --abstr_ref_prep                        false
% 2.33/0.97  --abstr_ref_until_sat                   false
% 2.33/0.97  --abstr_ref_sig_restrict                funpre
% 2.33/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.97  --abstr_ref_under                       []
% 2.33/0.97  
% 2.33/0.97  ------ SAT Options
% 2.33/0.97  
% 2.33/0.97  --sat_mode                              false
% 2.33/0.97  --sat_fm_restart_options                ""
% 2.33/0.97  --sat_gr_def                            false
% 2.33/0.97  --sat_epr_types                         true
% 2.33/0.97  --sat_non_cyclic_types                  false
% 2.33/0.97  --sat_finite_models                     false
% 2.33/0.97  --sat_fm_lemmas                         false
% 2.33/0.97  --sat_fm_prep                           false
% 2.33/0.97  --sat_fm_uc_incr                        true
% 2.33/0.97  --sat_out_model                         small
% 2.33/0.97  --sat_out_clauses                       false
% 2.33/0.97  
% 2.33/0.97  ------ QBF Options
% 2.33/0.97  
% 2.33/0.97  --qbf_mode                              false
% 2.33/0.97  --qbf_elim_univ                         false
% 2.33/0.97  --qbf_dom_inst                          none
% 2.33/0.97  --qbf_dom_pre_inst                      false
% 2.33/0.97  --qbf_sk_in                             false
% 2.33/0.97  --qbf_pred_elim                         true
% 2.33/0.97  --qbf_split                             512
% 2.33/0.97  
% 2.33/0.97  ------ BMC1 Options
% 2.33/0.97  
% 2.33/0.97  --bmc1_incremental                      false
% 2.33/0.97  --bmc1_axioms                           reachable_all
% 2.33/0.97  --bmc1_min_bound                        0
% 2.33/0.97  --bmc1_max_bound                        -1
% 2.33/0.97  --bmc1_max_bound_default                -1
% 2.33/0.97  --bmc1_symbol_reachability              true
% 2.33/0.97  --bmc1_property_lemmas                  false
% 2.33/0.97  --bmc1_k_induction                      false
% 2.33/0.97  --bmc1_non_equiv_states                 false
% 2.33/0.97  --bmc1_deadlock                         false
% 2.33/0.97  --bmc1_ucm                              false
% 2.33/0.97  --bmc1_add_unsat_core                   none
% 2.33/0.97  --bmc1_unsat_core_children              false
% 2.33/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.97  --bmc1_out_stat                         full
% 2.33/0.97  --bmc1_ground_init                      false
% 2.33/0.97  --bmc1_pre_inst_next_state              false
% 2.33/0.97  --bmc1_pre_inst_state                   false
% 2.33/0.97  --bmc1_pre_inst_reach_state             false
% 2.33/0.97  --bmc1_out_unsat_core                   false
% 2.33/0.97  --bmc1_aig_witness_out                  false
% 2.33/0.97  --bmc1_verbose                          false
% 2.33/0.97  --bmc1_dump_clauses_tptp                false
% 2.33/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.97  --bmc1_dump_file                        -
% 2.33/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.97  --bmc1_ucm_extend_mode                  1
% 2.33/0.97  --bmc1_ucm_init_mode                    2
% 2.33/0.97  --bmc1_ucm_cone_mode                    none
% 2.33/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.97  --bmc1_ucm_relax_model                  4
% 2.33/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.97  --bmc1_ucm_layered_model                none
% 2.33/0.97  --bmc1_ucm_max_lemma_size               10
% 2.33/0.97  
% 2.33/0.97  ------ AIG Options
% 2.33/0.97  
% 2.33/0.97  --aig_mode                              false
% 2.33/0.97  
% 2.33/0.97  ------ Instantiation Options
% 2.33/0.97  
% 2.33/0.97  --instantiation_flag                    true
% 2.33/0.97  --inst_sos_flag                         false
% 2.33/0.97  --inst_sos_phase                        true
% 2.33/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.97  --inst_lit_sel_side                     none
% 2.33/0.97  --inst_solver_per_active                1400
% 2.33/0.97  --inst_solver_calls_frac                1.
% 2.33/0.97  --inst_passive_queue_type               priority_queues
% 2.33/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.97  --inst_passive_queues_freq              [25;2]
% 2.33/0.97  --inst_dismatching                      true
% 2.33/0.97  --inst_eager_unprocessed_to_passive     true
% 2.33/0.97  --inst_prop_sim_given                   true
% 2.33/0.97  --inst_prop_sim_new                     false
% 2.33/0.97  --inst_subs_new                         false
% 2.33/0.97  --inst_eq_res_simp                      false
% 2.33/0.97  --inst_subs_given                       false
% 2.33/0.97  --inst_orphan_elimination               true
% 2.33/0.97  --inst_learning_loop_flag               true
% 2.33/0.97  --inst_learning_start                   3000
% 2.33/0.97  --inst_learning_factor                  2
% 2.33/0.97  --inst_start_prop_sim_after_learn       3
% 2.33/0.97  --inst_sel_renew                        solver
% 2.33/0.97  --inst_lit_activity_flag                true
% 2.33/0.97  --inst_restr_to_given                   false
% 2.33/0.97  --inst_activity_threshold               500
% 2.33/0.97  --inst_out_proof                        true
% 2.33/0.97  
% 2.33/0.97  ------ Resolution Options
% 2.33/0.97  
% 2.33/0.97  --resolution_flag                       false
% 2.33/0.97  --res_lit_sel                           adaptive
% 2.33/0.97  --res_lit_sel_side                      none
% 2.33/0.97  --res_ordering                          kbo
% 2.33/0.97  --res_to_prop_solver                    active
% 2.33/0.97  --res_prop_simpl_new                    false
% 2.33/0.97  --res_prop_simpl_given                  true
% 2.33/0.97  --res_passive_queue_type                priority_queues
% 2.33/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.97  --res_passive_queues_freq               [15;5]
% 2.33/0.97  --res_forward_subs                      full
% 2.33/0.97  --res_backward_subs                     full
% 2.33/0.97  --res_forward_subs_resolution           true
% 2.33/0.97  --res_backward_subs_resolution          true
% 2.33/0.97  --res_orphan_elimination                true
% 2.33/0.97  --res_time_limit                        2.
% 2.33/0.97  --res_out_proof                         true
% 2.33/0.97  
% 2.33/0.97  ------ Superposition Options
% 2.33/0.97  
% 2.33/0.97  --superposition_flag                    true
% 2.33/0.97  --sup_passive_queue_type                priority_queues
% 2.33/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.97  --demod_completeness_check              fast
% 2.33/0.97  --demod_use_ground                      true
% 2.33/0.97  --sup_to_prop_solver                    passive
% 2.33/0.97  --sup_prop_simpl_new                    true
% 2.33/0.97  --sup_prop_simpl_given                  true
% 2.33/0.97  --sup_fun_splitting                     false
% 2.33/0.97  --sup_smt_interval                      50000
% 2.33/0.97  
% 2.33/0.97  ------ Superposition Simplification Setup
% 2.33/0.97  
% 2.33/0.97  --sup_indices_passive                   []
% 2.33/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.97  --sup_full_bw                           [BwDemod]
% 2.33/0.97  --sup_immed_triv                        [TrivRules]
% 2.33/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.97  --sup_immed_bw_main                     []
% 2.33/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.97  
% 2.33/0.97  ------ Combination Options
% 2.33/0.97  
% 2.33/0.97  --comb_res_mult                         3
% 2.33/0.97  --comb_sup_mult                         2
% 2.33/0.97  --comb_inst_mult                        10
% 2.33/0.97  
% 2.33/0.97  ------ Debug Options
% 2.33/0.97  
% 2.33/0.97  --dbg_backtrace                         false
% 2.33/0.97  --dbg_dump_prop_clauses                 false
% 2.33/0.97  --dbg_dump_prop_clauses_file            -
% 2.33/0.97  --dbg_out_stat                          false
% 2.33/0.97  
% 2.33/0.97  
% 2.33/0.97  
% 2.33/0.97  
% 2.33/0.97  ------ Proving...
% 2.33/0.97  
% 2.33/0.97  
% 2.33/0.97  % SZS status Theorem for theBenchmark.p
% 2.33/0.97  
% 2.33/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/0.97  
% 2.33/0.97  fof(f13,conjecture,(
% 2.33/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f14,negated_conjecture,(
% 2.33/0.97    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.33/0.97    inference(negated_conjecture,[],[f13])).
% 2.33/0.97  
% 2.33/0.97  fof(f31,plain,(
% 2.33/0.97    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.33/0.97    inference(ennf_transformation,[],[f14])).
% 2.33/0.97  
% 2.33/0.97  fof(f32,plain,(
% 2.33/0.97    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.33/0.97    inference(flattening,[],[f31])).
% 2.33/0.97  
% 2.33/0.97  fof(f34,plain,(
% 2.33/0.97    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.33/0.97    introduced(choice_axiom,[])).
% 2.33/0.97  
% 2.33/0.97  fof(f35,plain,(
% 2.33/0.97    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.33/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f34])).
% 2.33/0.97  
% 2.33/0.97  fof(f58,plain,(
% 2.33/0.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.33/0.97    inference(cnf_transformation,[],[f35])).
% 2.33/0.97  
% 2.33/0.97  fof(f11,axiom,(
% 2.33/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))))),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f28,plain,(
% 2.33/0.97    ! [X0,X1,X2] : ((k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.97    inference(ennf_transformation,[],[f11])).
% 2.33/0.97  
% 2.33/0.97  fof(f48,plain,(
% 2.33/0.97    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.97    inference(cnf_transformation,[],[f28])).
% 2.33/0.97  
% 2.33/0.97  fof(f60,plain,(
% 2.33/0.97    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.33/0.97    inference(cnf_transformation,[],[f35])).
% 2.33/0.97  
% 2.33/0.97  fof(f10,axiom,(
% 2.33/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f27,plain,(
% 2.33/0.97    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.97    inference(ennf_transformation,[],[f10])).
% 2.33/0.97  
% 2.33/0.97  fof(f47,plain,(
% 2.33/0.97    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.97    inference(cnf_transformation,[],[f27])).
% 2.33/0.97  
% 2.33/0.97  fof(f4,axiom,(
% 2.33/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f19,plain,(
% 2.33/0.97    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.97    inference(ennf_transformation,[],[f4])).
% 2.33/0.97  
% 2.33/0.97  fof(f20,plain,(
% 2.33/0.97    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.97    inference(flattening,[],[f19])).
% 2.33/0.97  
% 2.33/0.97  fof(f40,plain,(
% 2.33/0.97    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.97    inference(cnf_transformation,[],[f20])).
% 2.33/0.97  
% 2.33/0.97  fof(f59,plain,(
% 2.33/0.97    v2_funct_1(sK2)),
% 2.33/0.97    inference(cnf_transformation,[],[f35])).
% 2.33/0.97  
% 2.33/0.97  fof(f56,plain,(
% 2.33/0.97    v1_funct_1(sK2)),
% 2.33/0.97    inference(cnf_transformation,[],[f35])).
% 2.33/0.97  
% 2.33/0.97  fof(f6,axiom,(
% 2.33/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f23,plain,(
% 2.33/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.97    inference(ennf_transformation,[],[f6])).
% 2.33/0.97  
% 2.33/0.97  fof(f43,plain,(
% 2.33/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.97    inference(cnf_transformation,[],[f23])).
% 2.33/0.97  
% 2.33/0.97  fof(f12,axiom,(
% 2.33/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f29,plain,(
% 2.33/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.97    inference(ennf_transformation,[],[f12])).
% 2.33/0.97  
% 2.33/0.97  fof(f30,plain,(
% 2.33/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.97    inference(flattening,[],[f29])).
% 2.33/0.97  
% 2.33/0.97  fof(f33,plain,(
% 2.33/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.97    inference(nnf_transformation,[],[f30])).
% 2.33/0.97  
% 2.33/0.97  fof(f52,plain,(
% 2.33/0.97    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.97    inference(cnf_transformation,[],[f33])).
% 2.33/0.97  
% 2.33/0.97  fof(f61,plain,(
% 2.33/0.97    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.33/0.97    inference(cnf_transformation,[],[f35])).
% 2.33/0.97  
% 2.33/0.97  fof(f5,axiom,(
% 2.33/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f21,plain,(
% 2.33/0.97    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.97    inference(ennf_transformation,[],[f5])).
% 2.33/0.97  
% 2.33/0.97  fof(f22,plain,(
% 2.33/0.97    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.97    inference(flattening,[],[f21])).
% 2.33/0.97  
% 2.33/0.97  fof(f42,plain,(
% 2.33/0.97    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.97    inference(cnf_transformation,[],[f22])).
% 2.33/0.97  
% 2.33/0.97  fof(f8,axiom,(
% 2.33/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f25,plain,(
% 2.33/0.97    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.97    inference(ennf_transformation,[],[f8])).
% 2.33/0.97  
% 2.33/0.97  fof(f45,plain,(
% 2.33/0.97    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.97    inference(cnf_transformation,[],[f25])).
% 2.33/0.97  
% 2.33/0.97  fof(f7,axiom,(
% 2.33/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f15,plain,(
% 2.33/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.33/0.97    inference(pure_predicate_removal,[],[f7])).
% 2.33/0.97  
% 2.33/0.97  fof(f24,plain,(
% 2.33/0.97    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.97    inference(ennf_transformation,[],[f15])).
% 2.33/0.97  
% 2.33/0.97  fof(f44,plain,(
% 2.33/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.97    inference(cnf_transformation,[],[f24])).
% 2.33/0.97  
% 2.33/0.97  fof(f2,axiom,(
% 2.33/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f17,plain,(
% 2.33/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.33/0.97    inference(ennf_transformation,[],[f2])).
% 2.33/0.97  
% 2.33/0.97  fof(f18,plain,(
% 2.33/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.33/0.97    inference(flattening,[],[f17])).
% 2.33/0.97  
% 2.33/0.97  fof(f37,plain,(
% 2.33/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.33/0.97    inference(cnf_transformation,[],[f18])).
% 2.33/0.97  
% 2.33/0.97  fof(f1,axiom,(
% 2.33/0.97    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f16,plain,(
% 2.33/0.97    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 2.33/0.97    inference(ennf_transformation,[],[f1])).
% 2.33/0.97  
% 2.33/0.97  fof(f36,plain,(
% 2.33/0.97    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 2.33/0.97    inference(cnf_transformation,[],[f16])).
% 2.33/0.97  
% 2.33/0.97  fof(f9,axiom,(
% 2.33/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f26,plain,(
% 2.33/0.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.97    inference(ennf_transformation,[],[f9])).
% 2.33/0.97  
% 2.33/0.97  fof(f46,plain,(
% 2.33/0.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.97    inference(cnf_transformation,[],[f26])).
% 2.33/0.97  
% 2.33/0.97  fof(f3,axiom,(
% 2.33/0.97    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.97  
% 2.33/0.97  fof(f39,plain,(
% 2.33/0.97    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.33/0.97    inference(cnf_transformation,[],[f3])).
% 2.33/0.97  
% 2.33/0.97  fof(f57,plain,(
% 2.33/0.97    v1_funct_2(sK2,sK0,sK1)),
% 2.33/0.97    inference(cnf_transformation,[],[f35])).
% 2.33/0.97  
% 2.33/0.97  cnf(c_632,plain,
% 2.33/0.97      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 2.33/0.97      theory(equality) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1302,plain,
% 2.33/0.97      ( X0_48 != X1_48 | X0_48 = sK2 | sK2 != X1_48 ),
% 2.33/0.97      inference(instantiation,[status(thm)],[c_632]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2876,plain,
% 2.33/0.97      ( k2_funct_1(sK2) != X0_48 | k2_funct_1(sK2) = sK2 | sK2 != X0_48 ),
% 2.33/0.97      inference(instantiation,[status(thm)],[c_1302]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2877,plain,
% 2.33/0.97      ( k2_funct_1(sK2) = sK2
% 2.33/0.97      | k2_funct_1(sK2) != k1_xboole_0
% 2.33/0.97      | sK2 != k1_xboole_0 ),
% 2.33/0.97      inference(instantiation,[status(thm)],[c_2876]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_23,negated_conjecture,
% 2.33/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.33/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_615,negated_conjecture,
% 2.33/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_23]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1005,plain,
% 2.33/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_13,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.97      | k1_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k2_relset_1(X1,X2,X0) ),
% 2.33/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_617,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.33/0.97      | k1_relset_1(X2_48,X1_48,k3_relset_1(X1_48,X2_48,X0_48)) = k2_relset_1(X1_48,X2_48,X0_48) ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_13]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1004,plain,
% 2.33/0.97      ( k1_relset_1(X0_48,X1_48,k3_relset_1(X1_48,X0_48,X2_48)) = k2_relset_1(X1_48,X0_48,X2_48)
% 2.33/0.97      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48))) != iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2207,plain,
% 2.33/0.97      ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) = k2_relset_1(sK0,sK1,sK2) ),
% 2.33/0.97      inference(superposition,[status(thm)],[c_1005,c_1004]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_21,negated_conjecture,
% 2.33/0.97      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.33/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_616,negated_conjecture,
% 2.33/0.97      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_21]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_11,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.97      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 2.33/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_619,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.33/0.97      | k3_relset_1(X1_48,X2_48,X0_48) = k4_relat_1(X0_48) ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_11]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1002,plain,
% 2.33/0.97      ( k3_relset_1(X0_48,X1_48,X2_48) = k4_relat_1(X2_48)
% 2.33/0.97      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1881,plain,
% 2.33/0.97      ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
% 2.33/0.97      inference(superposition,[status(thm)],[c_1005,c_1002]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_4,plain,
% 2.33/0.97      ( ~ v1_funct_1(X0)
% 2.33/0.97      | ~ v2_funct_1(X0)
% 2.33/0.97      | ~ v1_relat_1(X0)
% 2.33/0.97      | k4_relat_1(X0) = k2_funct_1(X0) ),
% 2.33/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_22,negated_conjecture,
% 2.33/0.97      ( v2_funct_1(sK2) ),
% 2.33/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_288,plain,
% 2.33/0.97      ( ~ v1_funct_1(X0)
% 2.33/0.97      | ~ v1_relat_1(X0)
% 2.33/0.97      | k4_relat_1(X0) = k2_funct_1(X0)
% 2.33/0.97      | sK2 != X0 ),
% 2.33/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_289,plain,
% 2.33/0.97      ( ~ v1_funct_1(sK2)
% 2.33/0.97      | ~ v1_relat_1(sK2)
% 2.33/0.97      | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.33/0.97      inference(unflattening,[status(thm)],[c_288]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_25,negated_conjecture,
% 2.33/0.97      ( v1_funct_1(sK2) ),
% 2.33/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_291,plain,
% 2.33/0.97      ( ~ v1_relat_1(sK2) | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.33/0.97      inference(global_propositional_subsumption,
% 2.33/0.97                [status(thm)],
% 2.33/0.97                [c_289,c_25]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_612,plain,
% 2.33/0.97      ( ~ v1_relat_1(sK2) | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_291]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1008,plain,
% 2.33/0.97      ( k4_relat_1(sK2) = k2_funct_1(sK2)
% 2.33/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_7,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.97      | v1_relat_1(X0) ),
% 2.33/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_622,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.33/0.97      | v1_relat_1(X0_48) ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_7]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1179,plain,
% 2.33/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.33/0.97      | v1_relat_1(sK2) ),
% 2.33/0.97      inference(instantiation,[status(thm)],[c_622]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1197,plain,
% 2.33/0.97      ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.33/0.97      inference(global_propositional_subsumption,
% 2.33/0.97                [status(thm)],
% 2.33/0.97                [c_1008,c_23,c_612,c_1179]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1888,plain,
% 2.33/0.97      ( k3_relset_1(sK0,sK1,sK2) = k2_funct_1(sK2) ),
% 2.33/0.97      inference(light_normalisation,[status(thm)],[c_1881,c_1197]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2214,plain,
% 2.33/0.97      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1 ),
% 2.33/0.97      inference(light_normalisation,[status(thm)],[c_2207,c_616,c_1888]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_17,plain,
% 2.33/0.97      ( v1_funct_2(X0,X1,X2)
% 2.33/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.97      | k1_relset_1(X1,X2,X0) != X1
% 2.33/0.97      | k1_xboole_0 = X2 ),
% 2.33/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_20,negated_conjecture,
% 2.33/0.97      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.33/0.97      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.97      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.33/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_391,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.97      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.97      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.97      | k1_relset_1(X1,X2,X0) != X1
% 2.33/0.97      | k2_funct_1(sK2) != X0
% 2.33/0.97      | sK0 != X2
% 2.33/0.97      | sK1 != X1
% 2.33/0.97      | k1_xboole_0 = X2 ),
% 2.33/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_392,plain,
% 2.33/0.97      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.97      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.97      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.33/0.97      | k1_xboole_0 = sK0 ),
% 2.33/0.97      inference(unflattening,[status(thm)],[c_391]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_607,plain,
% 2.33/0.97      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.97      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.97      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.33/0.97      | k1_xboole_0 = sK0 ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_392]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1013,plain,
% 2.33/0.97      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.33/0.97      | k1_xboole_0 = sK0
% 2.33/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.33/0.97      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_26,plain,
% 2.33/0.97      ( v1_funct_1(sK2) = iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_28,plain,
% 2.33/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_690,plain,
% 2.33/0.97      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.33/0.97      | k1_xboole_0 = sK0
% 2.33/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.33/0.97      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_5,plain,
% 2.33/0.97      ( ~ v1_funct_1(X0)
% 2.33/0.97      | v1_funct_1(k2_funct_1(X0))
% 2.33/0.97      | ~ v1_relat_1(X0) ),
% 2.33/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_624,plain,
% 2.33/0.97      ( ~ v1_funct_1(X0_48)
% 2.33/0.97      | v1_funct_1(k2_funct_1(X0_48))
% 2.33/0.97      | ~ v1_relat_1(X0_48) ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_5]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1176,plain,
% 2.33/0.97      ( v1_funct_1(k2_funct_1(sK2))
% 2.33/0.97      | ~ v1_funct_1(sK2)
% 2.33/0.97      | ~ v1_relat_1(sK2) ),
% 2.33/0.97      inference(instantiation,[status(thm)],[c_624]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1177,plain,
% 2.33/0.97      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.33/0.97      | v1_funct_1(sK2) != iProver_top
% 2.33/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_1176]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1180,plain,
% 2.33/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.33/0.97      | v1_relat_1(sK2) = iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_1179]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1233,plain,
% 2.33/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.33/0.97      | k1_xboole_0 = sK0
% 2.33/0.97      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1 ),
% 2.33/0.97      inference(global_propositional_subsumption,
% 2.33/0.97                [status(thm)],
% 2.33/0.97                [c_1013,c_26,c_28,c_690,c_1177,c_1180]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1234,plain,
% 2.33/0.97      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 2.33/0.97      | k1_xboole_0 = sK0
% 2.33/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.33/0.97      inference(renaming,[status(thm)],[c_1233]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2223,plain,
% 2.33/0.97      ( sK0 = k1_xboole_0
% 2.33/0.97      | sK1 != sK1
% 2.33/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.33/0.97      inference(demodulation,[status(thm)],[c_2214,c_1234]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2427,plain,
% 2.33/0.97      ( sK0 = k1_xboole_0
% 2.33/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.33/0.97      inference(equality_resolution_simp,[status(thm)],[c_2223]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1194,plain,
% 2.33/0.97      ( sK0 != X0_48 | sK0 = k1_xboole_0 | k1_xboole_0 != X0_48 ),
% 2.33/0.97      inference(instantiation,[status(thm)],[c_632]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1319,plain,
% 2.33/0.97      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 2.33/0.97      inference(instantiation,[status(thm)],[c_1194]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_629,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1320,plain,
% 2.33/0.97      ( sK0 = sK0 ),
% 2.33/0.97      inference(instantiation,[status(thm)],[c_629]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_9,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.97      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.33/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_621,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.33/0.97      | m1_subset_1(k3_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_9]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1000,plain,
% 2.33/0.97      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.33/0.97      | m1_subset_1(k3_relset_1(X1_48,X2_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48))) = iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1976,plain,
% 2.33/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 2.33/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.33/0.97      inference(superposition,[status(thm)],[c_1888,c_1000]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2429,plain,
% 2.33/0.97      ( sK0 = k1_xboole_0 ),
% 2.33/0.97      inference(global_propositional_subsumption,
% 2.33/0.97                [status(thm)],
% 2.33/0.97                [c_2427,c_26,c_28,c_690,c_1177,c_1180,c_1319,c_1320,
% 2.33/0.97                 c_1976,c_2214]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_8,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.97      | v4_relat_1(X0,X1) ),
% 2.33/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1,plain,
% 2.33/0.97      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.33/0.97      inference(cnf_transformation,[],[f37]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_270,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.97      | ~ v1_relat_1(X0)
% 2.33/0.97      | k7_relat_1(X0,X1) = X0 ),
% 2.33/0.97      inference(resolution,[status(thm)],[c_8,c_1]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_272,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.97      | k7_relat_1(X0,X1) = X0 ),
% 2.33/0.97      inference(global_propositional_subsumption,
% 2.33/0.97                [status(thm)],
% 2.33/0.97                [c_270,c_8,c_7,c_1]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_613,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.33/0.97      | k7_relat_1(X0_48,X1_48) = X0_48 ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_272]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1007,plain,
% 2.33/0.97      ( k7_relat_1(X0_48,X1_48) = X0_48
% 2.33/0.97      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1642,plain,
% 2.33/0.97      ( k7_relat_1(sK2,sK0) = sK2 ),
% 2.33/0.97      inference(superposition,[status(thm)],[c_1005,c_1007]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2437,plain,
% 2.33/0.97      ( k7_relat_1(sK2,k1_xboole_0) = sK2 ),
% 2.33/0.97      inference(demodulation,[status(thm)],[c_2429,c_1642]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_999,plain,
% 2.33/0.97      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.33/0.97      | v1_relat_1(X0_48) = iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1388,plain,
% 2.33/0.97      ( v1_relat_1(sK2) = iProver_top ),
% 2.33/0.97      inference(superposition,[status(thm)],[c_1005,c_999]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_0,plain,
% 2.33/0.97      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.33/0.97      inference(cnf_transformation,[],[f36]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_627,plain,
% 2.33/0.97      ( ~ v1_relat_1(X0_48)
% 2.33/0.97      | k7_relat_1(X0_48,k1_xboole_0) = k1_xboole_0 ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_0]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_996,plain,
% 2.33/0.97      ( k7_relat_1(X0_48,k1_xboole_0) = k1_xboole_0
% 2.33/0.97      | v1_relat_1(X0_48) != iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1392,plain,
% 2.33/0.97      ( k7_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 2.33/0.97      inference(superposition,[status(thm)],[c_1388,c_996]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2483,plain,
% 2.33/0.97      ( sK2 = k1_xboole_0 ),
% 2.33/0.97      inference(light_normalisation,[status(thm)],[c_2437,c_1392]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2444,plain,
% 2.33/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 2.33/0.97      inference(demodulation,[status(thm)],[c_2429,c_1005]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2488,plain,
% 2.33/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 2.33/0.97      inference(demodulation,[status(thm)],[c_2483,c_2444]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_10,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.33/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_620,plain,
% 2.33/0.97      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.33/0.97      | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_10]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1001,plain,
% 2.33/0.97      ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
% 2.33/0.97      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2659,plain,
% 2.33/0.97      ( k2_relset_1(k1_xboole_0,sK1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 2.33/0.97      inference(superposition,[status(thm)],[c_2488,c_1001]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2,plain,
% 2.33/0.97      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.33/0.97      inference(cnf_transformation,[],[f39]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_626,plain,
% 2.33/0.97      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_2]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2445,plain,
% 2.33/0.97      ( k2_relset_1(k1_xboole_0,sK1,sK2) = sK1 ),
% 2.33/0.97      inference(demodulation,[status(thm)],[c_2429,c_616]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2489,plain,
% 2.33/0.97      ( k2_relset_1(k1_xboole_0,sK1,k1_xboole_0) = sK1 ),
% 2.33/0.97      inference(demodulation,[status(thm)],[c_2483,c_2445]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2668,plain,
% 2.33/0.97      ( sK1 = k1_xboole_0 ),
% 2.33/0.97      inference(light_normalisation,[status(thm)],[c_2659,c_626,c_2489]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2019,plain,
% 2.33/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.33/0.97      inference(global_propositional_subsumption,
% 2.33/0.97                [status(thm)],
% 2.33/0.97                [c_1976,c_28]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2024,plain,
% 2.33/0.97      ( k7_relat_1(k2_funct_1(sK2),sK1) = k2_funct_1(sK2) ),
% 2.33/0.97      inference(superposition,[status(thm)],[c_2019,c_1007]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2681,plain,
% 2.33/0.97      ( k7_relat_1(k2_funct_1(sK2),k1_xboole_0) = k2_funct_1(sK2) ),
% 2.33/0.97      inference(demodulation,[status(thm)],[c_2668,c_2024]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2025,plain,
% 2.33/0.97      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.33/0.97      inference(superposition,[status(thm)],[c_2019,c_999]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2066,plain,
% 2.33/0.97      ( k7_relat_1(k2_funct_1(sK2),k1_xboole_0) = k1_xboole_0 ),
% 2.33/0.97      inference(superposition,[status(thm)],[c_2025,c_996]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_2686,plain,
% 2.33/0.97      ( k2_funct_1(sK2) = k1_xboole_0 ),
% 2.33/0.97      inference(light_normalisation,[status(thm)],[c_2681,c_2066]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1267,plain,
% 2.33/0.97      ( sK0 != X0_48 | sK0 = sK1 | sK1 != X0_48 ),
% 2.33/0.97      inference(instantiation,[status(thm)],[c_632]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_1268,plain,
% 2.33/0.97      ( sK0 = sK1 | sK0 != k1_xboole_0 | sK1 != k1_xboole_0 ),
% 2.33/0.97      inference(instantiation,[status(thm)],[c_1267]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_24,negated_conjecture,
% 2.33/0.97      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.33/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_418,plain,
% 2.33/0.97      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.97      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.97      | k2_funct_1(sK2) != sK2
% 2.33/0.97      | sK0 != sK1 ),
% 2.33/0.97      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_605,plain,
% 2.33/0.97      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.33/0.97      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.33/0.97      | k2_funct_1(sK2) != sK2
% 2.33/0.97      | sK0 != sK1 ),
% 2.33/0.97      inference(subtyping,[status(esa)],[c_418]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(c_691,plain,
% 2.33/0.97      ( k2_funct_1(sK2) != sK2
% 2.33/0.97      | sK0 != sK1
% 2.33/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.33/0.97      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.33/0.97      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 2.33/0.97  
% 2.33/0.97  cnf(contradiction,plain,
% 2.33/0.97      ( $false ),
% 2.33/0.97      inference(minisat,
% 2.33/0.97                [status(thm)],
% 2.33/0.97                [c_2877,c_2686,c_2668,c_2483,c_2214,c_1976,c_1320,c_1319,
% 2.33/0.97                 c_1268,c_1180,c_1177,c_691,c_690,c_28,c_26]) ).
% 2.33/0.97  
% 2.33/0.97  
% 2.33/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/0.97  
% 2.33/0.97  ------                               Statistics
% 2.33/0.97  
% 2.33/0.97  ------ General
% 2.33/0.97  
% 2.33/0.97  abstr_ref_over_cycles:                  0
% 2.33/0.97  abstr_ref_under_cycles:                 0
% 2.33/0.97  gc_basic_clause_elim:                   0
% 2.33/0.97  forced_gc_time:                         0
% 2.33/0.97  parsing_time:                           0.01
% 2.33/0.97  unif_index_cands_time:                  0.
% 2.33/0.97  unif_index_add_time:                    0.
% 2.33/0.97  orderings_time:                         0.
% 2.33/0.97  out_proof_time:                         0.012
% 2.33/0.97  total_time:                             0.123
% 2.33/0.97  num_of_symbols:                         54
% 2.33/0.97  num_of_terms:                           2194
% 2.33/0.97  
% 2.33/0.97  ------ Preprocessing
% 2.33/0.97  
% 2.33/0.97  num_of_splits:                          0
% 2.33/0.97  num_of_split_atoms:                     0
% 2.33/0.97  num_of_reused_defs:                     0
% 2.33/0.97  num_eq_ax_congr_red:                    16
% 2.33/0.97  num_of_sem_filtered_clauses:            1
% 2.33/0.97  num_of_subtypes:                        3
% 2.33/0.97  monotx_restored_types:                  0
% 2.33/0.97  sat_num_of_epr_types:                   0
% 2.33/0.97  sat_num_of_non_cyclic_types:            0
% 2.33/0.97  sat_guarded_non_collapsed_types:        1
% 2.33/0.97  num_pure_diseq_elim:                    0
% 2.33/0.97  simp_replaced_by:                       0
% 2.33/0.97  res_preprocessed:                       128
% 2.33/0.97  prep_upred:                             0
% 2.33/0.97  prep_unflattend:                        34
% 2.33/0.97  smt_new_axioms:                         0
% 2.33/0.97  pred_elim_cands:                        3
% 2.33/0.97  pred_elim:                              3
% 2.33/0.97  pred_elim_cl:                           3
% 2.33/0.97  pred_elim_cycles:                       5
% 2.33/0.97  merged_defs:                            0
% 2.33/0.97  merged_defs_ncl:                        0
% 2.33/0.97  bin_hyper_res:                          0
% 2.33/0.97  prep_cycles:                            4
% 2.33/0.97  pred_elim_time:                         0.005
% 2.33/0.97  splitting_time:                         0.
% 2.33/0.97  sem_filter_time:                        0.
% 2.33/0.97  monotx_time:                            0.
% 2.33/0.97  subtype_inf_time:                       0.
% 2.33/0.97  
% 2.33/0.97  ------ Problem properties
% 2.33/0.97  
% 2.33/0.97  clauses:                                23
% 2.33/0.97  conjectures:                            3
% 2.33/0.97  epr:                                    1
% 2.33/0.97  horn:                                   21
% 2.33/0.97  ground:                                 13
% 2.33/0.97  unary:                                  5
% 2.33/0.97  binary:                                 10
% 2.33/0.97  lits:                                   57
% 2.33/0.97  lits_eq:                                26
% 2.33/0.97  fd_pure:                                0
% 2.33/0.97  fd_pseudo:                              0
% 2.33/0.97  fd_cond:                                0
% 2.33/0.97  fd_pseudo_cond:                         0
% 2.33/0.97  ac_symbols:                             0
% 2.33/0.97  
% 2.33/0.97  ------ Propositional Solver
% 2.33/0.97  
% 2.33/0.97  prop_solver_calls:                      27
% 2.33/0.97  prop_fast_solver_calls:                 764
% 2.33/0.97  smt_solver_calls:                       0
% 2.33/0.97  smt_fast_solver_calls:                  0
% 2.33/0.97  prop_num_of_clauses:                    1013
% 2.33/0.97  prop_preprocess_simplified:             3848
% 2.33/0.97  prop_fo_subsumed:                       10
% 2.33/0.97  prop_solver_time:                       0.
% 2.33/0.97  smt_solver_time:                        0.
% 2.33/0.97  smt_fast_solver_time:                   0.
% 2.33/0.97  prop_fast_solver_time:                  0.
% 2.33/0.97  prop_unsat_core_time:                   0.
% 2.33/0.97  
% 2.33/0.97  ------ QBF
% 2.33/0.97  
% 2.33/0.97  qbf_q_res:                              0
% 2.33/0.97  qbf_num_tautologies:                    0
% 2.33/0.97  qbf_prep_cycles:                        0
% 2.33/0.97  
% 2.33/0.97  ------ BMC1
% 2.33/0.97  
% 2.33/0.97  bmc1_current_bound:                     -1
% 2.33/0.97  bmc1_last_solved_bound:                 -1
% 2.33/0.97  bmc1_unsat_core_size:                   -1
% 2.33/0.97  bmc1_unsat_core_parents_size:           -1
% 2.33/0.97  bmc1_merge_next_fun:                    0
% 2.33/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.33/0.97  
% 2.33/0.97  ------ Instantiation
% 2.33/0.97  
% 2.33/0.97  inst_num_of_clauses:                    348
% 2.33/0.97  inst_num_in_passive:                    174
% 2.33/0.97  inst_num_in_active:                     169
% 2.33/0.97  inst_num_in_unprocessed:                4
% 2.33/0.97  inst_num_of_loops:                      237
% 2.33/0.97  inst_num_of_learning_restarts:          0
% 2.33/0.97  inst_num_moves_active_passive:          63
% 2.33/0.97  inst_lit_activity:                      0
% 2.33/0.97  inst_lit_activity_moves:                0
% 2.33/0.97  inst_num_tautologies:                   0
% 2.33/0.97  inst_num_prop_implied:                  0
% 2.33/0.97  inst_num_existing_simplified:           0
% 2.33/0.97  inst_num_eq_res_simplified:             0
% 2.33/0.97  inst_num_child_elim:                    0
% 2.33/0.97  inst_num_of_dismatching_blockings:      12
% 2.33/0.97  inst_num_of_non_proper_insts:           169
% 2.33/0.97  inst_num_of_duplicates:                 0
% 2.33/0.97  inst_inst_num_from_inst_to_res:         0
% 2.33/0.97  inst_dismatching_checking_time:         0.
% 2.33/0.97  
% 2.33/0.97  ------ Resolution
% 2.33/0.97  
% 2.33/0.97  res_num_of_clauses:                     0
% 2.33/0.97  res_num_in_passive:                     0
% 2.33/0.97  res_num_in_active:                      0
% 2.33/0.97  res_num_of_loops:                       132
% 2.33/0.97  res_forward_subset_subsumed:            18
% 2.33/0.97  res_backward_subset_subsumed:           2
% 2.33/0.97  res_forward_subsumed:                   0
% 2.33/0.97  res_backward_subsumed:                  0
% 2.33/0.97  res_forward_subsumption_resolution:     0
% 2.33/0.97  res_backward_subsumption_resolution:    0
% 2.33/0.97  res_clause_to_clause_subsumption:       117
% 2.33/0.97  res_orphan_elimination:                 0
% 2.33/0.97  res_tautology_del:                      43
% 2.33/0.97  res_num_eq_res_simplified:              0
% 2.33/0.97  res_num_sel_changes:                    0
% 2.33/0.97  res_moves_from_active_to_pass:          0
% 2.33/0.97  
% 2.33/0.97  ------ Superposition
% 2.33/0.97  
% 2.33/0.97  sup_time_total:                         0.
% 2.33/0.97  sup_time_generating:                    0.
% 2.33/0.97  sup_time_sim_full:                      0.
% 2.33/0.97  sup_time_sim_immed:                     0.
% 2.33/0.97  
% 2.33/0.97  sup_num_of_clauses:                     54
% 2.33/0.97  sup_num_in_active:                      24
% 2.33/0.97  sup_num_in_passive:                     30
% 2.33/0.97  sup_num_of_loops:                       46
% 2.33/0.97  sup_fw_superposition:                   16
% 2.33/0.97  sup_bw_superposition:                   19
% 2.33/0.97  sup_immediate_simplified:               35
% 2.33/0.97  sup_given_eliminated:                   1
% 2.33/0.97  comparisons_done:                       0
% 2.33/0.97  comparisons_avoided:                    2
% 2.33/0.97  
% 2.33/0.97  ------ Simplifications
% 2.33/0.97  
% 2.33/0.97  
% 2.33/0.97  sim_fw_subset_subsumed:                 1
% 2.33/0.97  sim_bw_subset_subsumed:                 1
% 2.33/0.97  sim_fw_subsumed:                        0
% 2.33/0.97  sim_bw_subsumed:                        0
% 2.33/0.97  sim_fw_subsumption_res:                 2
% 2.33/0.97  sim_bw_subsumption_res:                 3
% 2.33/0.97  sim_tautology_del:                      0
% 2.33/0.97  sim_eq_tautology_del:                   1
% 2.33/0.97  sim_eq_res_simp:                        3
% 2.33/0.97  sim_fw_demodulated:                     0
% 2.33/0.97  sim_bw_demodulated:                     33
% 2.33/0.97  sim_light_normalised:                   21
% 2.33/0.97  sim_joinable_taut:                      0
% 2.33/0.97  sim_joinable_simp:                      0
% 2.33/0.97  sim_ac_normalised:                      0
% 2.33/0.97  sim_smt_subsumption:                    0
% 2.33/0.97  
%------------------------------------------------------------------------------

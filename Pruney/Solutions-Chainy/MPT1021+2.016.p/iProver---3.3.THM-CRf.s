%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:20 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  209 (2973 expanded)
%              Number of clauses        :  121 ( 937 expanded)
%              Number of leaves         :   21 ( 571 expanded)
%              Depth                    :   29
%              Number of atoms          :  643 (13550 expanded)
%              Number of equality atoms :  305 (1620 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f53,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f53])).

fof(f96,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f54])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f67,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f67,f92])).

fof(f68,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f101,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f68,f92])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f97,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f100,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f66,f92])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f99,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f64,f92])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f106,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1762,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1771,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7704,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1771])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1780,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4279,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1762,c_1780])).

cnf(c_7707,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7704,c_4279])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_43,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_8795,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7707,c_43])).

cnf(c_8796,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8795])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1764,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_10005,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1764])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_42,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_39,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_44,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_10221,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10005,c_42,c_43,c_44])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1770,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10231,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10221,c_1770])).

cnf(c_45,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_11072,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10231,c_42,c_43,c_44,c_45])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1765,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_12045,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11072,c_1765])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1767,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4021,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1767])).

cnf(c_4482,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4021,c_42,c_43,c_44])).

cnf(c_10225,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10221,c_4482])).

cnf(c_16329,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12045,c_10225])).

cnf(c_16330,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_16329])).

cnf(c_16338,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_16330])).

cnf(c_20,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1777,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7683,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1777])).

cnf(c_8081,plain,
    ( v2_funct_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7683,c_42,c_44])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1781,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3141,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1781])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1782,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5896,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3141,c_1782])).

cnf(c_6303,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5896,c_42])).

cnf(c_8086,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_8081,c_6303])).

cnf(c_16342,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16338,c_8086])).

cnf(c_16359,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16342,c_42])).

cnf(c_12044,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1765])).

cnf(c_12064,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12044,c_42])).

cnf(c_12065,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_12064])).

cnf(c_12071,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_12065])).

cnf(c_12456,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_12071])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1783,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6871,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3141,c_1783])).

cnf(c_19,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_485,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_15,c_29])).

cnf(c_497,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_485,c_14])).

cnf(c_570,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_497])).

cnf(c_571,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_1758,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_3026,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1758])).

cnf(c_3772,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3026,c_42,c_44])).

cnf(c_3773,plain,
    ( k2_relat_1(sK1) = sK0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3772])).

cnf(c_3779,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_1762,c_3773])).

cnf(c_6873,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6871,c_3779])).

cnf(c_7088,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v2_funct_1(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6873,c_42])).

cnf(c_8085,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(superposition,[status(thm)],[c_8081,c_7088])).

cnf(c_12460,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12456,c_8085,c_10221])).

cnf(c_12074,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11072,c_12065])).

cnf(c_12077,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12074,c_8085])).

cnf(c_12610,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12460,c_10225,c_12077])).

cnf(c_37,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1763,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_10226,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10221,c_1763])).

cnf(c_12612,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12610,c_10226])).

cnf(c_17,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1855,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2971,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1855])).

cnf(c_2972,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2971])).

cnf(c_34,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4105,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_4106,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4105])).

cnf(c_12938,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12612,c_2972,c_4106])).

cnf(c_16361,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16359,c_12938])).

cnf(c_16740,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8796,c_16361])).

cnf(c_16743,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16740,c_2972,c_4106])).

cnf(c_16745,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16743,c_16361])).

cnf(c_11,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_16816,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16745,c_11])).

cnf(c_10,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2350,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_10])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1784,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2867,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1784])).

cnf(c_16798,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16743,c_2867])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_16803,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16798,c_5])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1786,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1788,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5131,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_1788])).

cnf(c_17177,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16803,c_5131])).

cnf(c_17483,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16816,c_11,c_2350,c_17177])).

cnf(c_2120,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2121,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2120])).

cnf(c_2123,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2121])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1845,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1846,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1845])).

cnf(c_1848,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1846])).

cnf(c_102,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_104,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17483,c_2123,c_1848,c_104])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:43:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 3.86/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.00  
% 3.86/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.86/1.00  
% 3.86/1.00  ------  iProver source info
% 3.86/1.00  
% 3.86/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.86/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.86/1.00  git: non_committed_changes: false
% 3.86/1.00  git: last_make_outside_of_git: false
% 3.86/1.00  
% 3.86/1.00  ------ 
% 3.86/1.00  
% 3.86/1.00  ------ Input Options
% 3.86/1.00  
% 3.86/1.00  --out_options                           all
% 3.86/1.00  --tptp_safe_out                         true
% 3.86/1.00  --problem_path                          ""
% 3.86/1.00  --include_path                          ""
% 3.86/1.00  --clausifier                            res/vclausify_rel
% 3.86/1.00  --clausifier_options                    ""
% 3.86/1.00  --stdin                                 false
% 3.86/1.00  --stats_out                             all
% 3.86/1.00  
% 3.86/1.00  ------ General Options
% 3.86/1.00  
% 3.86/1.00  --fof                                   false
% 3.86/1.00  --time_out_real                         305.
% 3.86/1.00  --time_out_virtual                      -1.
% 3.86/1.00  --symbol_type_check                     false
% 3.86/1.00  --clausify_out                          false
% 3.86/1.00  --sig_cnt_out                           false
% 3.86/1.00  --trig_cnt_out                          false
% 3.86/1.00  --trig_cnt_out_tolerance                1.
% 3.86/1.00  --trig_cnt_out_sk_spl                   false
% 3.86/1.00  --abstr_cl_out                          false
% 3.86/1.00  
% 3.86/1.00  ------ Global Options
% 3.86/1.00  
% 3.86/1.00  --schedule                              default
% 3.86/1.00  --add_important_lit                     false
% 3.86/1.00  --prop_solver_per_cl                    1000
% 3.86/1.00  --min_unsat_core                        false
% 3.86/1.00  --soft_assumptions                      false
% 3.86/1.00  --soft_lemma_size                       3
% 3.86/1.00  --prop_impl_unit_size                   0
% 3.86/1.00  --prop_impl_unit                        []
% 3.86/1.00  --share_sel_clauses                     true
% 3.86/1.00  --reset_solvers                         false
% 3.86/1.00  --bc_imp_inh                            [conj_cone]
% 3.86/1.00  --conj_cone_tolerance                   3.
% 3.86/1.00  --extra_neg_conj                        none
% 3.86/1.00  --large_theory_mode                     true
% 3.86/1.00  --prolific_symb_bound                   200
% 3.86/1.00  --lt_threshold                          2000
% 3.86/1.00  --clause_weak_htbl                      true
% 3.86/1.00  --gc_record_bc_elim                     false
% 3.86/1.00  
% 3.86/1.00  ------ Preprocessing Options
% 3.86/1.00  
% 3.86/1.00  --preprocessing_flag                    true
% 3.86/1.00  --time_out_prep_mult                    0.1
% 3.86/1.00  --splitting_mode                        input
% 3.86/1.00  --splitting_grd                         true
% 3.86/1.00  --splitting_cvd                         false
% 3.86/1.00  --splitting_cvd_svl                     false
% 3.86/1.00  --splitting_nvd                         32
% 3.86/1.00  --sub_typing                            true
% 3.86/1.00  --prep_gs_sim                           true
% 3.86/1.00  --prep_unflatten                        true
% 3.86/1.00  --prep_res_sim                          true
% 3.86/1.00  --prep_upred                            true
% 3.86/1.00  --prep_sem_filter                       exhaustive
% 3.86/1.00  --prep_sem_filter_out                   false
% 3.86/1.00  --pred_elim                             true
% 3.86/1.00  --res_sim_input                         true
% 3.86/1.00  --eq_ax_congr_red                       true
% 3.86/1.00  --pure_diseq_elim                       true
% 3.86/1.00  --brand_transform                       false
% 3.86/1.00  --non_eq_to_eq                          false
% 3.86/1.00  --prep_def_merge                        true
% 3.86/1.00  --prep_def_merge_prop_impl              false
% 3.86/1.00  --prep_def_merge_mbd                    true
% 3.86/1.00  --prep_def_merge_tr_red                 false
% 3.86/1.00  --prep_def_merge_tr_cl                  false
% 3.86/1.00  --smt_preprocessing                     true
% 3.86/1.00  --smt_ac_axioms                         fast
% 3.86/1.00  --preprocessed_out                      false
% 3.86/1.00  --preprocessed_stats                    false
% 3.86/1.00  
% 3.86/1.00  ------ Abstraction refinement Options
% 3.86/1.00  
% 3.86/1.00  --abstr_ref                             []
% 3.86/1.00  --abstr_ref_prep                        false
% 3.86/1.00  --abstr_ref_until_sat                   false
% 3.86/1.00  --abstr_ref_sig_restrict                funpre
% 3.86/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.86/1.00  --abstr_ref_under                       []
% 3.86/1.00  
% 3.86/1.00  ------ SAT Options
% 3.86/1.00  
% 3.86/1.00  --sat_mode                              false
% 3.86/1.00  --sat_fm_restart_options                ""
% 3.86/1.00  --sat_gr_def                            false
% 3.86/1.00  --sat_epr_types                         true
% 3.86/1.00  --sat_non_cyclic_types                  false
% 3.86/1.00  --sat_finite_models                     false
% 3.86/1.00  --sat_fm_lemmas                         false
% 3.86/1.00  --sat_fm_prep                           false
% 3.86/1.00  --sat_fm_uc_incr                        true
% 3.86/1.00  --sat_out_model                         small
% 3.86/1.00  --sat_out_clauses                       false
% 3.86/1.00  
% 3.86/1.00  ------ QBF Options
% 3.86/1.00  
% 3.86/1.00  --qbf_mode                              false
% 3.86/1.00  --qbf_elim_univ                         false
% 3.86/1.00  --qbf_dom_inst                          none
% 3.86/1.00  --qbf_dom_pre_inst                      false
% 3.86/1.00  --qbf_sk_in                             false
% 3.86/1.00  --qbf_pred_elim                         true
% 3.86/1.00  --qbf_split                             512
% 3.86/1.00  
% 3.86/1.00  ------ BMC1 Options
% 3.86/1.00  
% 3.86/1.00  --bmc1_incremental                      false
% 3.86/1.00  --bmc1_axioms                           reachable_all
% 3.86/1.00  --bmc1_min_bound                        0
% 3.86/1.00  --bmc1_max_bound                        -1
% 3.86/1.00  --bmc1_max_bound_default                -1
% 3.86/1.00  --bmc1_symbol_reachability              true
% 3.86/1.00  --bmc1_property_lemmas                  false
% 3.86/1.00  --bmc1_k_induction                      false
% 3.86/1.00  --bmc1_non_equiv_states                 false
% 3.86/1.00  --bmc1_deadlock                         false
% 3.86/1.00  --bmc1_ucm                              false
% 3.86/1.00  --bmc1_add_unsat_core                   none
% 3.86/1.00  --bmc1_unsat_core_children              false
% 3.86/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.86/1.00  --bmc1_out_stat                         full
% 3.86/1.00  --bmc1_ground_init                      false
% 3.86/1.00  --bmc1_pre_inst_next_state              false
% 3.86/1.00  --bmc1_pre_inst_state                   false
% 3.86/1.00  --bmc1_pre_inst_reach_state             false
% 3.86/1.00  --bmc1_out_unsat_core                   false
% 3.86/1.00  --bmc1_aig_witness_out                  false
% 3.86/1.00  --bmc1_verbose                          false
% 3.86/1.00  --bmc1_dump_clauses_tptp                false
% 3.86/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.86/1.00  --bmc1_dump_file                        -
% 3.86/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.86/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.86/1.00  --bmc1_ucm_extend_mode                  1
% 3.86/1.00  --bmc1_ucm_init_mode                    2
% 3.86/1.00  --bmc1_ucm_cone_mode                    none
% 3.86/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.86/1.00  --bmc1_ucm_relax_model                  4
% 3.86/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.86/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.86/1.00  --bmc1_ucm_layered_model                none
% 3.86/1.00  --bmc1_ucm_max_lemma_size               10
% 3.86/1.00  
% 3.86/1.00  ------ AIG Options
% 3.86/1.00  
% 3.86/1.00  --aig_mode                              false
% 3.86/1.00  
% 3.86/1.00  ------ Instantiation Options
% 3.86/1.00  
% 3.86/1.00  --instantiation_flag                    true
% 3.86/1.00  --inst_sos_flag                         true
% 3.86/1.00  --inst_sos_phase                        true
% 3.86/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.86/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.86/1.00  --inst_lit_sel_side                     num_symb
% 3.86/1.00  --inst_solver_per_active                1400
% 3.86/1.00  --inst_solver_calls_frac                1.
% 3.86/1.00  --inst_passive_queue_type               priority_queues
% 3.86/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.86/1.00  --inst_passive_queues_freq              [25;2]
% 3.86/1.00  --inst_dismatching                      true
% 3.86/1.00  --inst_eager_unprocessed_to_passive     true
% 3.86/1.00  --inst_prop_sim_given                   true
% 3.86/1.00  --inst_prop_sim_new                     false
% 3.86/1.00  --inst_subs_new                         false
% 3.86/1.00  --inst_eq_res_simp                      false
% 3.86/1.00  --inst_subs_given                       false
% 3.86/1.00  --inst_orphan_elimination               true
% 3.86/1.00  --inst_learning_loop_flag               true
% 3.86/1.00  --inst_learning_start                   3000
% 3.86/1.00  --inst_learning_factor                  2
% 3.86/1.00  --inst_start_prop_sim_after_learn       3
% 3.86/1.00  --inst_sel_renew                        solver
% 3.86/1.00  --inst_lit_activity_flag                true
% 3.86/1.00  --inst_restr_to_given                   false
% 3.86/1.00  --inst_activity_threshold               500
% 3.86/1.00  --inst_out_proof                        true
% 3.86/1.00  
% 3.86/1.00  ------ Resolution Options
% 3.86/1.00  
% 3.86/1.00  --resolution_flag                       true
% 3.86/1.00  --res_lit_sel                           adaptive
% 3.86/1.00  --res_lit_sel_side                      none
% 3.86/1.00  --res_ordering                          kbo
% 3.86/1.00  --res_to_prop_solver                    active
% 3.86/1.00  --res_prop_simpl_new                    false
% 3.86/1.00  --res_prop_simpl_given                  true
% 3.86/1.00  --res_passive_queue_type                priority_queues
% 3.86/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.86/1.00  --res_passive_queues_freq               [15;5]
% 3.86/1.00  --res_forward_subs                      full
% 3.86/1.00  --res_backward_subs                     full
% 3.86/1.00  --res_forward_subs_resolution           true
% 3.86/1.00  --res_backward_subs_resolution          true
% 3.86/1.00  --res_orphan_elimination                true
% 3.86/1.00  --res_time_limit                        2.
% 3.86/1.00  --res_out_proof                         true
% 3.86/1.00  
% 3.86/1.00  ------ Superposition Options
% 3.86/1.00  
% 3.86/1.00  --superposition_flag                    true
% 3.86/1.00  --sup_passive_queue_type                priority_queues
% 3.86/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.86/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.86/1.00  --demod_completeness_check              fast
% 3.86/1.00  --demod_use_ground                      true
% 3.86/1.00  --sup_to_prop_solver                    passive
% 3.86/1.00  --sup_prop_simpl_new                    true
% 3.86/1.00  --sup_prop_simpl_given                  true
% 3.86/1.00  --sup_fun_splitting                     true
% 3.86/1.00  --sup_smt_interval                      50000
% 3.86/1.00  
% 3.86/1.00  ------ Superposition Simplification Setup
% 3.86/1.00  
% 3.86/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.86/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.86/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.86/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.86/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.86/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.86/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.86/1.00  --sup_immed_triv                        [TrivRules]
% 3.86/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/1.00  --sup_immed_bw_main                     []
% 3.86/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.86/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.86/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/1.00  --sup_input_bw                          []
% 3.86/1.00  
% 3.86/1.00  ------ Combination Options
% 3.86/1.00  
% 3.86/1.00  --comb_res_mult                         3
% 3.86/1.00  --comb_sup_mult                         2
% 3.86/1.00  --comb_inst_mult                        10
% 3.86/1.00  
% 3.86/1.00  ------ Debug Options
% 3.86/1.00  
% 3.86/1.00  --dbg_backtrace                         false
% 3.86/1.00  --dbg_dump_prop_clauses                 false
% 3.86/1.00  --dbg_dump_prop_clauses_file            -
% 3.86/1.00  --dbg_out_stat                          false
% 3.86/1.00  ------ Parsing...
% 3.86/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.86/1.00  
% 3.86/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.86/1.00  
% 3.86/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.86/1.00  
% 3.86/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.86/1.00  ------ Proving...
% 3.86/1.00  ------ Problem Properties 
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  clauses                                 37
% 3.86/1.00  conjectures                             5
% 3.86/1.00  EPR                                     6
% 3.86/1.00  Horn                                    32
% 3.86/1.00  unary                                   12
% 3.86/1.00  binary                                  6
% 3.86/1.00  lits                                    102
% 3.86/1.00  lits eq                                 25
% 3.86/1.00  fd_pure                                 0
% 3.86/1.00  fd_pseudo                               0
% 3.86/1.00  fd_cond                                 4
% 3.86/1.00  fd_pseudo_cond                          3
% 3.86/1.00  AC symbols                              0
% 3.86/1.00  
% 3.86/1.00  ------ Schedule dynamic 5 is on 
% 3.86/1.00  
% 3.86/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  ------ 
% 3.86/1.00  Current options:
% 3.86/1.00  ------ 
% 3.86/1.00  
% 3.86/1.00  ------ Input Options
% 3.86/1.00  
% 3.86/1.00  --out_options                           all
% 3.86/1.00  --tptp_safe_out                         true
% 3.86/1.00  --problem_path                          ""
% 3.86/1.00  --include_path                          ""
% 3.86/1.00  --clausifier                            res/vclausify_rel
% 3.86/1.00  --clausifier_options                    ""
% 3.86/1.00  --stdin                                 false
% 3.86/1.00  --stats_out                             all
% 3.86/1.00  
% 3.86/1.00  ------ General Options
% 3.86/1.00  
% 3.86/1.00  --fof                                   false
% 3.86/1.00  --time_out_real                         305.
% 3.86/1.00  --time_out_virtual                      -1.
% 3.86/1.00  --symbol_type_check                     false
% 3.86/1.00  --clausify_out                          false
% 3.86/1.00  --sig_cnt_out                           false
% 3.86/1.00  --trig_cnt_out                          false
% 3.86/1.00  --trig_cnt_out_tolerance                1.
% 3.86/1.00  --trig_cnt_out_sk_spl                   false
% 3.86/1.00  --abstr_cl_out                          false
% 3.86/1.00  
% 3.86/1.00  ------ Global Options
% 3.86/1.00  
% 3.86/1.00  --schedule                              default
% 3.86/1.00  --add_important_lit                     false
% 3.86/1.00  --prop_solver_per_cl                    1000
% 3.86/1.00  --min_unsat_core                        false
% 3.86/1.00  --soft_assumptions                      false
% 3.86/1.00  --soft_lemma_size                       3
% 3.86/1.00  --prop_impl_unit_size                   0
% 3.86/1.00  --prop_impl_unit                        []
% 3.86/1.00  --share_sel_clauses                     true
% 3.86/1.00  --reset_solvers                         false
% 3.86/1.00  --bc_imp_inh                            [conj_cone]
% 3.86/1.00  --conj_cone_tolerance                   3.
% 3.86/1.00  --extra_neg_conj                        none
% 3.86/1.00  --large_theory_mode                     true
% 3.86/1.00  --prolific_symb_bound                   200
% 3.86/1.00  --lt_threshold                          2000
% 3.86/1.00  --clause_weak_htbl                      true
% 3.86/1.00  --gc_record_bc_elim                     false
% 3.86/1.00  
% 3.86/1.00  ------ Preprocessing Options
% 3.86/1.00  
% 3.86/1.00  --preprocessing_flag                    true
% 3.86/1.00  --time_out_prep_mult                    0.1
% 3.86/1.00  --splitting_mode                        input
% 3.86/1.00  --splitting_grd                         true
% 3.86/1.00  --splitting_cvd                         false
% 3.86/1.00  --splitting_cvd_svl                     false
% 3.86/1.00  --splitting_nvd                         32
% 3.86/1.00  --sub_typing                            true
% 3.86/1.00  --prep_gs_sim                           true
% 3.86/1.00  --prep_unflatten                        true
% 3.86/1.00  --prep_res_sim                          true
% 3.86/1.00  --prep_upred                            true
% 3.86/1.00  --prep_sem_filter                       exhaustive
% 3.86/1.00  --prep_sem_filter_out                   false
% 3.86/1.00  --pred_elim                             true
% 3.86/1.00  --res_sim_input                         true
% 3.86/1.00  --eq_ax_congr_red                       true
% 3.86/1.00  --pure_diseq_elim                       true
% 3.86/1.00  --brand_transform                       false
% 3.86/1.00  --non_eq_to_eq                          false
% 3.86/1.00  --prep_def_merge                        true
% 3.86/1.00  --prep_def_merge_prop_impl              false
% 3.86/1.00  --prep_def_merge_mbd                    true
% 3.86/1.00  --prep_def_merge_tr_red                 false
% 3.86/1.00  --prep_def_merge_tr_cl                  false
% 3.86/1.00  --smt_preprocessing                     true
% 3.86/1.00  --smt_ac_axioms                         fast
% 3.86/1.00  --preprocessed_out                      false
% 3.86/1.00  --preprocessed_stats                    false
% 3.86/1.00  
% 3.86/1.00  ------ Abstraction refinement Options
% 3.86/1.00  
% 3.86/1.00  --abstr_ref                             []
% 3.86/1.00  --abstr_ref_prep                        false
% 3.86/1.00  --abstr_ref_until_sat                   false
% 3.86/1.00  --abstr_ref_sig_restrict                funpre
% 3.86/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.86/1.00  --abstr_ref_under                       []
% 3.86/1.00  
% 3.86/1.00  ------ SAT Options
% 3.86/1.00  
% 3.86/1.00  --sat_mode                              false
% 3.86/1.00  --sat_fm_restart_options                ""
% 3.86/1.00  --sat_gr_def                            false
% 3.86/1.00  --sat_epr_types                         true
% 3.86/1.00  --sat_non_cyclic_types                  false
% 3.86/1.00  --sat_finite_models                     false
% 3.86/1.00  --sat_fm_lemmas                         false
% 3.86/1.00  --sat_fm_prep                           false
% 3.86/1.00  --sat_fm_uc_incr                        true
% 3.86/1.00  --sat_out_model                         small
% 3.86/1.00  --sat_out_clauses                       false
% 3.86/1.00  
% 3.86/1.00  ------ QBF Options
% 3.86/1.00  
% 3.86/1.00  --qbf_mode                              false
% 3.86/1.00  --qbf_elim_univ                         false
% 3.86/1.00  --qbf_dom_inst                          none
% 3.86/1.00  --qbf_dom_pre_inst                      false
% 3.86/1.00  --qbf_sk_in                             false
% 3.86/1.00  --qbf_pred_elim                         true
% 3.86/1.00  --qbf_split                             512
% 3.86/1.00  
% 3.86/1.00  ------ BMC1 Options
% 3.86/1.00  
% 3.86/1.00  --bmc1_incremental                      false
% 3.86/1.00  --bmc1_axioms                           reachable_all
% 3.86/1.00  --bmc1_min_bound                        0
% 3.86/1.00  --bmc1_max_bound                        -1
% 3.86/1.00  --bmc1_max_bound_default                -1
% 3.86/1.00  --bmc1_symbol_reachability              true
% 3.86/1.00  --bmc1_property_lemmas                  false
% 3.86/1.00  --bmc1_k_induction                      false
% 3.86/1.00  --bmc1_non_equiv_states                 false
% 3.86/1.00  --bmc1_deadlock                         false
% 3.86/1.00  --bmc1_ucm                              false
% 3.86/1.00  --bmc1_add_unsat_core                   none
% 3.86/1.00  --bmc1_unsat_core_children              false
% 3.86/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.86/1.00  --bmc1_out_stat                         full
% 3.86/1.00  --bmc1_ground_init                      false
% 3.86/1.00  --bmc1_pre_inst_next_state              false
% 3.86/1.00  --bmc1_pre_inst_state                   false
% 3.86/1.00  --bmc1_pre_inst_reach_state             false
% 3.86/1.00  --bmc1_out_unsat_core                   false
% 3.86/1.00  --bmc1_aig_witness_out                  false
% 3.86/1.00  --bmc1_verbose                          false
% 3.86/1.00  --bmc1_dump_clauses_tptp                false
% 3.86/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.86/1.00  --bmc1_dump_file                        -
% 3.86/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.86/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.86/1.00  --bmc1_ucm_extend_mode                  1
% 3.86/1.00  --bmc1_ucm_init_mode                    2
% 3.86/1.00  --bmc1_ucm_cone_mode                    none
% 3.86/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.86/1.00  --bmc1_ucm_relax_model                  4
% 3.86/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.86/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.86/1.00  --bmc1_ucm_layered_model                none
% 3.86/1.00  --bmc1_ucm_max_lemma_size               10
% 3.86/1.00  
% 3.86/1.00  ------ AIG Options
% 3.86/1.00  
% 3.86/1.00  --aig_mode                              false
% 3.86/1.00  
% 3.86/1.00  ------ Instantiation Options
% 3.86/1.00  
% 3.86/1.00  --instantiation_flag                    true
% 3.86/1.00  --inst_sos_flag                         true
% 3.86/1.00  --inst_sos_phase                        true
% 3.86/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.86/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.86/1.00  --inst_lit_sel_side                     none
% 3.86/1.00  --inst_solver_per_active                1400
% 3.86/1.00  --inst_solver_calls_frac                1.
% 3.86/1.00  --inst_passive_queue_type               priority_queues
% 3.86/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.86/1.00  --inst_passive_queues_freq              [25;2]
% 3.86/1.00  --inst_dismatching                      true
% 3.86/1.00  --inst_eager_unprocessed_to_passive     true
% 3.86/1.00  --inst_prop_sim_given                   true
% 3.86/1.00  --inst_prop_sim_new                     false
% 3.86/1.00  --inst_subs_new                         false
% 3.86/1.00  --inst_eq_res_simp                      false
% 3.86/1.00  --inst_subs_given                       false
% 3.86/1.00  --inst_orphan_elimination               true
% 3.86/1.00  --inst_learning_loop_flag               true
% 3.86/1.00  --inst_learning_start                   3000
% 3.86/1.00  --inst_learning_factor                  2
% 3.86/1.00  --inst_start_prop_sim_after_learn       3
% 3.86/1.00  --inst_sel_renew                        solver
% 3.86/1.00  --inst_lit_activity_flag                true
% 3.86/1.00  --inst_restr_to_given                   false
% 3.86/1.00  --inst_activity_threshold               500
% 3.86/1.00  --inst_out_proof                        true
% 3.86/1.00  
% 3.86/1.00  ------ Resolution Options
% 3.86/1.00  
% 3.86/1.00  --resolution_flag                       false
% 3.86/1.00  --res_lit_sel                           adaptive
% 3.86/1.00  --res_lit_sel_side                      none
% 3.86/1.00  --res_ordering                          kbo
% 3.86/1.00  --res_to_prop_solver                    active
% 3.86/1.00  --res_prop_simpl_new                    false
% 3.86/1.00  --res_prop_simpl_given                  true
% 3.86/1.00  --res_passive_queue_type                priority_queues
% 3.86/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.86/1.00  --res_passive_queues_freq               [15;5]
% 3.86/1.00  --res_forward_subs                      full
% 3.86/1.00  --res_backward_subs                     full
% 3.86/1.00  --res_forward_subs_resolution           true
% 3.86/1.00  --res_backward_subs_resolution          true
% 3.86/1.00  --res_orphan_elimination                true
% 3.86/1.00  --res_time_limit                        2.
% 3.86/1.00  --res_out_proof                         true
% 3.86/1.00  
% 3.86/1.00  ------ Superposition Options
% 3.86/1.00  
% 3.86/1.00  --superposition_flag                    true
% 3.86/1.00  --sup_passive_queue_type                priority_queues
% 3.86/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.86/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.86/1.00  --demod_completeness_check              fast
% 3.86/1.00  --demod_use_ground                      true
% 3.86/1.00  --sup_to_prop_solver                    passive
% 3.86/1.00  --sup_prop_simpl_new                    true
% 3.86/1.00  --sup_prop_simpl_given                  true
% 3.86/1.00  --sup_fun_splitting                     true
% 3.86/1.00  --sup_smt_interval                      50000
% 3.86/1.00  
% 3.86/1.00  ------ Superposition Simplification Setup
% 3.86/1.00  
% 3.86/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.86/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.86/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.86/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.86/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.86/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.86/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.86/1.00  --sup_immed_triv                        [TrivRules]
% 3.86/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/1.00  --sup_immed_bw_main                     []
% 3.86/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.86/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.86/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/1.00  --sup_input_bw                          []
% 3.86/1.00  
% 3.86/1.00  ------ Combination Options
% 3.86/1.00  
% 3.86/1.00  --comb_res_mult                         3
% 3.86/1.00  --comb_sup_mult                         2
% 3.86/1.00  --comb_inst_mult                        10
% 3.86/1.00  
% 3.86/1.00  ------ Debug Options
% 3.86/1.00  
% 3.86/1.00  --dbg_backtrace                         false
% 3.86/1.00  --dbg_dump_prop_clauses                 false
% 3.86/1.00  --dbg_dump_prop_clauses_file            -
% 3.86/1.00  --dbg_out_stat                          false
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  ------ Proving...
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  % SZS status Theorem for theBenchmark.p
% 3.86/1.00  
% 3.86/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.86/1.00  
% 3.86/1.00  fof(f20,conjecture,(
% 3.86/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f21,negated_conjecture,(
% 3.86/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.86/1.00    inference(negated_conjecture,[],[f20])).
% 3.86/1.00  
% 3.86/1.00  fof(f43,plain,(
% 3.86/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.86/1.00    inference(ennf_transformation,[],[f21])).
% 3.86/1.00  
% 3.86/1.00  fof(f44,plain,(
% 3.86/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.86/1.00    inference(flattening,[],[f43])).
% 3.86/1.00  
% 3.86/1.00  fof(f53,plain,(
% 3.86/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.86/1.00    introduced(choice_axiom,[])).
% 3.86/1.00  
% 3.86/1.00  fof(f54,plain,(
% 3.86/1.00    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.86/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f53])).
% 3.86/1.00  
% 3.86/1.00  fof(f96,plain,(
% 3.86/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.86/1.00    inference(cnf_transformation,[],[f54])).
% 3.86/1.00  
% 3.86/1.00  fof(f13,axiom,(
% 3.86/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f33,plain,(
% 3.86/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/1.00    inference(ennf_transformation,[],[f13])).
% 3.86/1.00  
% 3.86/1.00  fof(f34,plain,(
% 3.86/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/1.00    inference(flattening,[],[f33])).
% 3.86/1.00  
% 3.86/1.00  fof(f51,plain,(
% 3.86/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/1.00    inference(nnf_transformation,[],[f34])).
% 3.86/1.00  
% 3.86/1.00  fof(f77,plain,(
% 3.86/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/1.00    inference(cnf_transformation,[],[f51])).
% 3.86/1.00  
% 3.86/1.00  fof(f10,axiom,(
% 3.86/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f28,plain,(
% 3.86/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/1.00    inference(ennf_transformation,[],[f10])).
% 3.86/1.00  
% 3.86/1.00  fof(f71,plain,(
% 3.86/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/1.00    inference(cnf_transformation,[],[f28])).
% 3.86/1.00  
% 3.86/1.00  fof(f94,plain,(
% 3.86/1.00    v1_funct_2(sK1,sK0,sK0)),
% 3.86/1.00    inference(cnf_transformation,[],[f54])).
% 3.86/1.00  
% 3.86/1.00  fof(f18,axiom,(
% 3.86/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f41,plain,(
% 3.86/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.86/1.00    inference(ennf_transformation,[],[f18])).
% 3.86/1.00  
% 3.86/1.00  fof(f42,plain,(
% 3.86/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.86/1.00    inference(flattening,[],[f41])).
% 3.86/1.00  
% 3.86/1.00  fof(f91,plain,(
% 3.86/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f42])).
% 3.86/1.00  
% 3.86/1.00  fof(f93,plain,(
% 3.86/1.00    v1_funct_1(sK1)),
% 3.86/1.00    inference(cnf_transformation,[],[f54])).
% 3.86/1.00  
% 3.86/1.00  fof(f95,plain,(
% 3.86/1.00    v3_funct_2(sK1,sK0,sK0)),
% 3.86/1.00    inference(cnf_transformation,[],[f54])).
% 3.86/1.00  
% 3.86/1.00  fof(f15,axiom,(
% 3.86/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f37,plain,(
% 3.86/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.86/1.00    inference(ennf_transformation,[],[f15])).
% 3.86/1.00  
% 3.86/1.00  fof(f38,plain,(
% 3.86/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.86/1.00    inference(flattening,[],[f37])).
% 3.86/1.00  
% 3.86/1.00  fof(f88,plain,(
% 3.86/1.00    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f38])).
% 3.86/1.00  
% 3.86/1.00  fof(f17,axiom,(
% 3.86/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f39,plain,(
% 3.86/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.86/1.00    inference(ennf_transformation,[],[f17])).
% 3.86/1.00  
% 3.86/1.00  fof(f40,plain,(
% 3.86/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.86/1.00    inference(flattening,[],[f39])).
% 3.86/1.00  
% 3.86/1.00  fof(f90,plain,(
% 3.86/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f40])).
% 3.86/1.00  
% 3.86/1.00  fof(f85,plain,(
% 3.86/1.00    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f38])).
% 3.86/1.00  
% 3.86/1.00  fof(f12,axiom,(
% 3.86/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f31,plain,(
% 3.86/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/1.00    inference(ennf_transformation,[],[f12])).
% 3.86/1.00  
% 3.86/1.00  fof(f32,plain,(
% 3.86/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/1.00    inference(flattening,[],[f31])).
% 3.86/1.00  
% 3.86/1.00  fof(f75,plain,(
% 3.86/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/1.00    inference(cnf_transformation,[],[f32])).
% 3.86/1.00  
% 3.86/1.00  fof(f8,axiom,(
% 3.86/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f26,plain,(
% 3.86/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/1.00    inference(ennf_transformation,[],[f8])).
% 3.86/1.00  
% 3.86/1.00  fof(f69,plain,(
% 3.86/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/1.00    inference(cnf_transformation,[],[f26])).
% 3.86/1.00  
% 3.86/1.00  fof(f7,axiom,(
% 3.86/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f24,plain,(
% 3.86/1.00    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.86/1.00    inference(ennf_transformation,[],[f7])).
% 3.86/1.00  
% 3.86/1.00  fof(f25,plain,(
% 3.86/1.00    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.86/1.00    inference(flattening,[],[f24])).
% 3.86/1.00  
% 3.86/1.00  fof(f67,plain,(
% 3.86/1.00    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f25])).
% 3.86/1.00  
% 3.86/1.00  fof(f19,axiom,(
% 3.86/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f92,plain,(
% 3.86/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f19])).
% 3.86/1.00  
% 3.86/1.00  fof(f102,plain,(
% 3.86/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/1.00    inference(definition_unfolding,[],[f67,f92])).
% 3.86/1.00  
% 3.86/1.00  fof(f68,plain,(
% 3.86/1.00    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f25])).
% 3.86/1.00  
% 3.86/1.00  fof(f101,plain,(
% 3.86/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.86/1.00    inference(definition_unfolding,[],[f68,f92])).
% 3.86/1.00  
% 3.86/1.00  fof(f76,plain,(
% 3.86/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/1.00    inference(cnf_transformation,[],[f32])).
% 3.86/1.00  
% 3.86/1.00  fof(f9,axiom,(
% 3.86/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f23,plain,(
% 3.86/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.86/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.86/1.00  
% 3.86/1.00  fof(f27,plain,(
% 3.86/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/1.00    inference(ennf_transformation,[],[f23])).
% 3.86/1.00  
% 3.86/1.00  fof(f70,plain,(
% 3.86/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/1.00    inference(cnf_transformation,[],[f27])).
% 3.86/1.00  
% 3.86/1.00  fof(f14,axiom,(
% 3.86/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f35,plain,(
% 3.86/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.86/1.00    inference(ennf_transformation,[],[f14])).
% 3.86/1.00  
% 3.86/1.00  fof(f36,plain,(
% 3.86/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.86/1.00    inference(flattening,[],[f35])).
% 3.86/1.00  
% 3.86/1.00  fof(f52,plain,(
% 3.86/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.86/1.00    inference(nnf_transformation,[],[f36])).
% 3.86/1.00  
% 3.86/1.00  fof(f83,plain,(
% 3.86/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f52])).
% 3.86/1.00  
% 3.86/1.00  fof(f97,plain,(
% 3.86/1.00    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.86/1.00    inference(cnf_transformation,[],[f54])).
% 3.86/1.00  
% 3.86/1.00  fof(f11,axiom,(
% 3.86/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f29,plain,(
% 3.86/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.86/1.00    inference(ennf_transformation,[],[f11])).
% 3.86/1.00  
% 3.86/1.00  fof(f30,plain,(
% 3.86/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/1.00    inference(flattening,[],[f29])).
% 3.86/1.00  
% 3.86/1.00  fof(f50,plain,(
% 3.86/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.86/1.00    inference(nnf_transformation,[],[f30])).
% 3.86/1.00  
% 3.86/1.00  fof(f73,plain,(
% 3.86/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/1.00    inference(cnf_transformation,[],[f50])).
% 3.86/1.00  
% 3.86/1.00  fof(f107,plain,(
% 3.86/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.86/1.00    inference(equality_resolution,[],[f73])).
% 3.86/1.00  
% 3.86/1.00  fof(f16,axiom,(
% 3.86/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f22,plain,(
% 3.86/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.86/1.00    inference(pure_predicate_removal,[],[f16])).
% 3.86/1.00  
% 3.86/1.00  fof(f89,plain,(
% 3.86/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.86/1.00    inference(cnf_transformation,[],[f22])).
% 3.86/1.00  
% 3.86/1.00  fof(f6,axiom,(
% 3.86/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f66,plain,(
% 3.86/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.86/1.00    inference(cnf_transformation,[],[f6])).
% 3.86/1.00  
% 3.86/1.00  fof(f100,plain,(
% 3.86/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.86/1.00    inference(definition_unfolding,[],[f66,f92])).
% 3.86/1.00  
% 3.86/1.00  fof(f5,axiom,(
% 3.86/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f64,plain,(
% 3.86/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.86/1.00    inference(cnf_transformation,[],[f5])).
% 3.86/1.00  
% 3.86/1.00  fof(f99,plain,(
% 3.86/1.00    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.86/1.00    inference(definition_unfolding,[],[f64,f92])).
% 3.86/1.00  
% 3.86/1.00  fof(f4,axiom,(
% 3.86/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f49,plain,(
% 3.86/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.86/1.00    inference(nnf_transformation,[],[f4])).
% 3.86/1.00  
% 3.86/1.00  fof(f62,plain,(
% 3.86/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.86/1.00    inference(cnf_transformation,[],[f49])).
% 3.86/1.00  
% 3.86/1.00  fof(f3,axiom,(
% 3.86/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f47,plain,(
% 3.86/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.86/1.00    inference(nnf_transformation,[],[f3])).
% 3.86/1.00  
% 3.86/1.00  fof(f48,plain,(
% 3.86/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.86/1.00    inference(flattening,[],[f47])).
% 3.86/1.00  
% 3.86/1.00  fof(f60,plain,(
% 3.86/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.86/1.00    inference(cnf_transformation,[],[f48])).
% 3.86/1.00  
% 3.86/1.00  fof(f106,plain,(
% 3.86/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.86/1.00    inference(equality_resolution,[],[f60])).
% 3.86/1.00  
% 3.86/1.00  fof(f2,axiom,(
% 3.86/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f58,plain,(
% 3.86/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f2])).
% 3.86/1.00  
% 3.86/1.00  fof(f1,axiom,(
% 3.86/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/1.00  
% 3.86/1.00  fof(f45,plain,(
% 3.86/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/1.00    inference(nnf_transformation,[],[f1])).
% 3.86/1.00  
% 3.86/1.00  fof(f46,plain,(
% 3.86/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/1.00    inference(flattening,[],[f45])).
% 3.86/1.00  
% 3.86/1.00  fof(f57,plain,(
% 3.86/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f46])).
% 3.86/1.00  
% 3.86/1.00  fof(f63,plain,(
% 3.86/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.86/1.00    inference(cnf_transformation,[],[f49])).
% 3.86/1.00  
% 3.86/1.00  cnf(c_38,negated_conjecture,
% 3.86/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.86/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1762,plain,
% 3.86/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_27,plain,
% 3.86/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.86/1.00      | k1_xboole_0 = X2 ),
% 3.86/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1771,plain,
% 3.86/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.86/1.00      | k1_xboole_0 = X1
% 3.86/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.86/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_7704,plain,
% 3.86/1.00      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 3.86/1.00      | sK0 = k1_xboole_0
% 3.86/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1762,c_1771]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16,plain,
% 3.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.86/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1780,plain,
% 3.86/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.86/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_4279,plain,
% 3.86/1.00      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1762,c_1780]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_7707,plain,
% 3.86/1.00      ( k1_relat_1(sK1) = sK0
% 3.86/1.00      | sK0 = k1_xboole_0
% 3.86/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_7704,c_4279]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_40,negated_conjecture,
% 3.86/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.86/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_43,plain,
% 3.86/1.00      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8795,plain,
% 3.86/1.00      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_7707,c_43]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8796,plain,
% 3.86/1.00      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 3.86/1.00      inference(renaming,[status(thm)],[c_8795]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_36,plain,
% 3.86/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.86/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.86/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1764,plain,
% 3.86/1.00      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.86/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.86/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.86/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.86/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_10005,plain,
% 3.86/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.86/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1762,c_1764]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_41,negated_conjecture,
% 3.86/1.00      ( v1_funct_1(sK1) ),
% 3.86/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_42,plain,
% 3.86/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_39,negated_conjecture,
% 3.86/1.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.86/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_44,plain,
% 3.86/1.00      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_10221,plain,
% 3.86/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_10005,c_42,c_43,c_44]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_30,plain,
% 3.86/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.86/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.86/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.86/1.00      | ~ v1_funct_1(X0) ),
% 3.86/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1770,plain,
% 3.86/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.86/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.86/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.86/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_10231,plain,
% 3.86/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/1.00      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.86/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_10221,c_1770]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_45,plain,
% 3.86/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_11072,plain,
% 3.86/1.00      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_10231,c_42,c_43,c_44,c_45]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_35,plain,
% 3.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | ~ v1_funct_1(X3)
% 3.86/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.86/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1765,plain,
% 3.86/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.86/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.86/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.86/1.00      | v1_funct_1(X5) != iProver_top
% 3.86/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12045,plain,
% 3.86/1.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.86/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.86/1.00      | v1_funct_1(X2) != iProver_top
% 3.86/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_11072,c_1765]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_33,plain,
% 3.86/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.86/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.86/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1767,plain,
% 3.86/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.86/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.86/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top
% 3.86/1.00      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_4021,plain,
% 3.86/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/1.00      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1762,c_1767]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_4482,plain,
% 3.86/1.00      ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_4021,c_42,c_43,c_44]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_10225,plain,
% 3.86/1.00      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_10221,c_4482]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16329,plain,
% 3.86/1.00      ( v1_funct_1(X2) != iProver_top
% 3.86/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.86/1.00      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_12045,c_10225]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16330,plain,
% 3.86/1.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.86/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.86/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.86/1.00      inference(renaming,[status(thm)],[c_16329]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16338,plain,
% 3.86/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1762,c_16330]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_20,plain,
% 3.86/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | v2_funct_1(X0) ),
% 3.86/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1777,plain,
% 3.86/1.00      ( v3_funct_2(X0,X1,X2) != iProver_top
% 3.86/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top
% 3.86/1.00      | v2_funct_1(X0) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_7683,plain,
% 3.86/1.00      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top
% 3.86/1.00      | v2_funct_1(sK1) = iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1762,c_1777]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8081,plain,
% 3.86/1.00      ( v2_funct_1(sK1) = iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_7683,c_42,c_44]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_14,plain,
% 3.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | v1_relat_1(X0) ),
% 3.86/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1781,plain,
% 3.86/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.86/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_3141,plain,
% 3.86/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1762,c_1781]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_13,plain,
% 3.86/1.00      ( ~ v1_relat_1(X0)
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | ~ v2_funct_1(X0)
% 3.86/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.86/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1782,plain,
% 3.86/1.00      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.86/1.00      | v1_relat_1(X0) != iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top
% 3.86/1.00      | v2_funct_1(X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_5896,plain,
% 3.86/1.00      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top
% 3.86/1.00      | v2_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_3141,c_1782]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_6303,plain,
% 3.86/1.00      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.86/1.00      | v2_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_5896,c_42]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8086,plain,
% 3.86/1.00      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_8081,c_6303]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16342,plain,
% 3.86/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(light_normalisation,[status(thm)],[c_16338,c_8086]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16359,plain,
% 3.86/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_16342,c_42]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12044,plain,
% 3.86/1.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.86/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.86/1.00      | v1_funct_1(X2) != iProver_top
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1762,c_1765]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12064,plain,
% 3.86/1.00      ( v1_funct_1(X2) != iProver_top
% 3.86/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.86/1.00      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_12044,c_42]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12065,plain,
% 3.86/1.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.86/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.86/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.86/1.00      inference(renaming,[status(thm)],[c_12064]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12071,plain,
% 3.86/1.00      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 3.86/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.86/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.86/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.86/1.00      | v1_funct_1(X1) != iProver_top
% 3.86/1.00      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1770,c_12065]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12456,plain,
% 3.86/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 3.86/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/1.00      | v1_funct_1(k2_funct_2(sK0,sK1)) != iProver_top
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1762,c_12071]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12,plain,
% 3.86/1.00      ( ~ v1_relat_1(X0)
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | ~ v2_funct_1(X0)
% 3.86/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.86/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1783,plain,
% 3.86/1.00      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.86/1.00      | v1_relat_1(X0) != iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top
% 3.86/1.00      | v2_funct_1(X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_6871,plain,
% 3.86/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top
% 3.86/1.00      | v2_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_3141,c_1783]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_19,plain,
% 3.86/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.86/1.00      | v2_funct_2(X0,X2)
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | ~ v1_funct_1(X0) ),
% 3.86/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_15,plain,
% 3.86/1.00      ( v5_relat_1(X0,X1)
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.86/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_29,plain,
% 3.86/1.00      ( ~ v2_funct_2(X0,X1)
% 3.86/1.00      | ~ v5_relat_1(X0,X1)
% 3.86/1.00      | ~ v1_relat_1(X0)
% 3.86/1.00      | k2_relat_1(X0) = X1 ),
% 3.86/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_485,plain,
% 3.86/1.00      ( ~ v2_funct_2(X0,X1)
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.86/1.00      | ~ v1_relat_1(X0)
% 3.86/1.00      | k2_relat_1(X0) = X1 ),
% 3.86/1.00      inference(resolution,[status(thm)],[c_15,c_29]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_497,plain,
% 3.86/1.00      ( ~ v2_funct_2(X0,X1)
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.86/1.00      | k2_relat_1(X0) = X1 ),
% 3.86/1.00      inference(forward_subsumption_resolution,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_485,c_14]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_570,plain,
% 3.86/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | X3 != X0
% 3.86/1.00      | X5 != X2
% 3.86/1.00      | k2_relat_1(X3) = X5 ),
% 3.86/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_497]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_571,plain,
% 3.86/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.86/1.00      | ~ v1_funct_1(X0)
% 3.86/1.00      | k2_relat_1(X0) = X2 ),
% 3.86/1.00      inference(unflattening,[status(thm)],[c_570]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1758,plain,
% 3.86/1.00      ( k2_relat_1(X0) = X1
% 3.86/1.00      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.86/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.86/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.86/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_3026,plain,
% 3.86/1.00      ( k2_relat_1(sK1) = sK0
% 3.86/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1762,c_1758]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_3772,plain,
% 3.86/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.86/1.00      | k2_relat_1(sK1) = sK0 ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_3026,c_42,c_44]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_3773,plain,
% 3.86/1.00      ( k2_relat_1(sK1) = sK0
% 3.86/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top ),
% 3.86/1.00      inference(renaming,[status(thm)],[c_3772]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_3779,plain,
% 3.86/1.00      ( k2_relat_1(sK1) = sK0 ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1762,c_3773]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_6873,plain,
% 3.86/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top
% 3.86/1.00      | v2_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(light_normalisation,[status(thm)],[c_6871,c_3779]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_7088,plain,
% 3.86/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.86/1.00      | v2_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_6873,c_42]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8085,plain,
% 3.86/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_8081,c_7088]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12460,plain,
% 3.86/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.86/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.86/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 3.86/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.86/1.00      inference(light_normalisation,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_12456,c_8085,c_10221]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12074,plain,
% 3.86/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 3.86/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_11072,c_12065]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12077,plain,
% 3.86/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.86/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.86/1.00      inference(light_normalisation,[status(thm)],[c_12074,c_8085]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12610,plain,
% 3.86/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_12460,c_10225,c_12077]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_37,negated_conjecture,
% 3.86/1.00      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.86/1.00      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.86/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1763,plain,
% 3.86/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.86/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_10226,plain,
% 3.86/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.86/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_10221,c_1763]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12612,plain,
% 3.86/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 3.86/1.00      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_12610,c_10226]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_17,plain,
% 3.86/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.86/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.86/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1855,plain,
% 3.86/1.00      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 3.86/1.00      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2971,plain,
% 3.86/1.00      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
% 3.86/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_1855]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2972,plain,
% 3.86/1.00      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
% 3.86/1.00      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_2971]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_34,plain,
% 3.86/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.86/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_4105,plain,
% 3.86/1.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_34]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_4106,plain,
% 3.86/1.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_4105]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_12938,plain,
% 3.86/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_12612,c_2972,c_4106]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16361,plain,
% 3.86/1.00      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_16359,c_12938]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16740,plain,
% 3.86/1.00      ( sK0 = k1_xboole_0
% 3.86/1.00      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_8796,c_16361]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16743,plain,
% 3.86/1.00      ( sK0 = k1_xboole_0 ),
% 3.86/1.00      inference(global_propositional_subsumption,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_16740,c_2972,c_4106]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16745,plain,
% 3.86/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_16743,c_16361]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_11,plain,
% 3.86/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.86/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16816,plain,
% 3.86/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(light_normalisation,[status(thm)],[c_16745,c_11]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_10,plain,
% 3.86/1.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.86/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2350,plain,
% 3.86/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_11,c_10]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_8,plain,
% 3.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.86/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1784,plain,
% 3.86/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.86/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2867,plain,
% 3.86/1.00      ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1762,c_1784]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16798,plain,
% 3.86/1.00      ( r1_tarski(sK1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_16743,c_2867]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_5,plain,
% 3.86/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.86/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_16803,plain,
% 3.86/1.00      ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.86/1.00      inference(demodulation,[status(thm)],[c_16798,c_5]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_3,plain,
% 3.86/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.86/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1786,plain,
% 3.86/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_0,plain,
% 3.86/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.86/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1788,plain,
% 3.86/1.00      ( X0 = X1
% 3.86/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.86/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_5131,plain,
% 3.86/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_1786,c_1788]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_17177,plain,
% 3.86/1.00      ( sK1 = k1_xboole_0 ),
% 3.86/1.00      inference(superposition,[status(thm)],[c_16803,c_5131]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_17483,plain,
% 3.86/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.86/1.00      inference(light_normalisation,
% 3.86/1.00                [status(thm)],
% 3.86/1.00                [c_16816,c_11,c_2350,c_17177]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2120,plain,
% 3.86/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2121,plain,
% 3.86/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_2120]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_2123,plain,
% 3.86/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_2121]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_7,plain,
% 3.86/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.86/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1845,plain,
% 3.86/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.86/1.00      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1846,plain,
% 3.86/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.86/1.00      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_1845]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_1848,plain,
% 3.86/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.86/1.00      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_1846]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_102,plain,
% 3.86/1.00      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.86/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.86/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(c_104,plain,
% 3.86/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 3.86/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.86/1.00      inference(instantiation,[status(thm)],[c_102]) ).
% 3.86/1.00  
% 3.86/1.00  cnf(contradiction,plain,
% 3.86/1.00      ( $false ),
% 3.86/1.00      inference(minisat,[status(thm)],[c_17483,c_2123,c_1848,c_104]) ).
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
% 3.86/1.00  parsing_time:                           0.008
% 3.86/1.00  unif_index_cands_time:                  0.
% 3.86/1.00  unif_index_add_time:                    0.
% 3.86/1.00  orderings_time:                         0.
% 3.86/1.00  out_proof_time:                         0.017
% 3.86/1.00  total_time:                             0.497
% 3.86/1.00  num_of_symbols:                         54
% 3.86/1.00  num_of_terms:                           15667
% 3.86/1.00  
% 3.86/1.00  ------ Preprocessing
% 3.86/1.00  
% 3.86/1.00  num_of_splits:                          0
% 3.86/1.00  num_of_split_atoms:                     0
% 3.86/1.00  num_of_reused_defs:                     0
% 3.86/1.00  num_eq_ax_congr_red:                    20
% 3.86/1.00  num_of_sem_filtered_clauses:            1
% 3.86/1.00  num_of_subtypes:                        0
% 3.86/1.00  monotx_restored_types:                  0
% 3.86/1.00  sat_num_of_epr_types:                   0
% 3.86/1.00  sat_num_of_non_cyclic_types:            0
% 3.86/1.00  sat_guarded_non_collapsed_types:        0
% 3.86/1.00  num_pure_diseq_elim:                    0
% 3.86/1.00  simp_replaced_by:                       0
% 3.86/1.00  res_preprocessed:                       186
% 3.86/1.00  prep_upred:                             0
% 3.86/1.00  prep_unflattend:                        6
% 3.86/1.00  smt_new_axioms:                         0
% 3.86/1.00  pred_elim_cands:                        8
% 3.86/1.00  pred_elim:                              2
% 3.86/1.00  pred_elim_cl:                           3
% 3.86/1.00  pred_elim_cycles:                       6
% 3.86/1.00  merged_defs:                            8
% 3.86/1.00  merged_defs_ncl:                        0
% 3.86/1.00  bin_hyper_res:                          8
% 3.86/1.00  prep_cycles:                            4
% 3.86/1.00  pred_elim_time:                         0.004
% 3.86/1.00  splitting_time:                         0.
% 3.86/1.00  sem_filter_time:                        0.
% 3.86/1.00  monotx_time:                            0.
% 3.86/1.00  subtype_inf_time:                       0.
% 3.86/1.00  
% 3.86/1.00  ------ Problem properties
% 3.86/1.00  
% 3.86/1.00  clauses:                                37
% 3.86/1.00  conjectures:                            5
% 3.86/1.00  epr:                                    6
% 3.86/1.00  horn:                                   32
% 3.86/1.00  ground:                                 6
% 3.86/1.00  unary:                                  12
% 3.86/1.00  binary:                                 6
% 3.86/1.00  lits:                                   102
% 3.86/1.00  lits_eq:                                25
% 3.86/1.00  fd_pure:                                0
% 3.86/1.00  fd_pseudo:                              0
% 3.86/1.00  fd_cond:                                4
% 3.86/1.00  fd_pseudo_cond:                         3
% 3.86/1.00  ac_symbols:                             0
% 3.86/1.00  
% 3.86/1.00  ------ Propositional Solver
% 3.86/1.00  
% 3.86/1.00  prop_solver_calls:                      30
% 3.86/1.00  prop_fast_solver_calls:                 1844
% 3.86/1.00  smt_solver_calls:                       0
% 3.86/1.00  smt_fast_solver_calls:                  0
% 3.86/1.00  prop_num_of_clauses:                    7003
% 3.86/1.00  prop_preprocess_simplified:             16048
% 3.86/1.00  prop_fo_subsumed:                       75
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
% 3.86/1.00  inst_num_of_clauses:                    1921
% 3.86/1.00  inst_num_in_passive:                    512
% 3.86/1.00  inst_num_in_active:                     703
% 3.86/1.00  inst_num_in_unprocessed:                706
% 3.86/1.00  inst_num_of_loops:                      1040
% 3.86/1.00  inst_num_of_learning_restarts:          0
% 3.86/1.00  inst_num_moves_active_passive:          333
% 3.86/1.00  inst_lit_activity:                      0
% 3.86/1.00  inst_lit_activity_moves:                0
% 3.86/1.00  inst_num_tautologies:                   0
% 3.86/1.00  inst_num_prop_implied:                  0
% 3.86/1.00  inst_num_existing_simplified:           0
% 3.86/1.00  inst_num_eq_res_simplified:             0
% 3.86/1.00  inst_num_child_elim:                    0
% 3.86/1.00  inst_num_of_dismatching_blockings:      814
% 3.86/1.00  inst_num_of_non_proper_insts:           2929
% 3.86/1.00  inst_num_of_duplicates:                 0
% 3.86/1.00  inst_inst_num_from_inst_to_res:         0
% 3.86/1.00  inst_dismatching_checking_time:         0.
% 3.86/1.00  
% 3.86/1.00  ------ Resolution
% 3.86/1.00  
% 3.86/1.00  res_num_of_clauses:                     0
% 3.86/1.00  res_num_in_passive:                     0
% 3.86/1.00  res_num_in_active:                      0
% 3.86/1.00  res_num_of_loops:                       190
% 3.86/1.00  res_forward_subset_subsumed:            328
% 3.86/1.00  res_backward_subset_subsumed:           4
% 3.86/1.00  res_forward_subsumed:                   0
% 3.86/1.00  res_backward_subsumed:                  0
% 3.86/1.00  res_forward_subsumption_resolution:     2
% 3.86/1.00  res_backward_subsumption_resolution:    0
% 3.86/1.00  res_clause_to_clause_subsumption:       1233
% 3.86/1.00  res_orphan_elimination:                 0
% 3.86/1.00  res_tautology_del:                      79
% 3.86/1.00  res_num_eq_res_simplified:              0
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
% 3.86/1.00  sup_num_of_clauses:                     305
% 3.86/1.00  sup_num_in_active:                      123
% 3.86/1.00  sup_num_in_passive:                     182
% 3.86/1.00  sup_num_of_loops:                       206
% 3.86/1.00  sup_fw_superposition:                   363
% 3.86/1.00  sup_bw_superposition:                   105
% 3.86/1.00  sup_immediate_simplified:               126
% 3.86/1.00  sup_given_eliminated:                   6
% 3.86/1.00  comparisons_done:                       0
% 3.86/1.00  comparisons_avoided:                    0
% 3.86/1.00  
% 3.86/1.00  ------ Simplifications
% 3.86/1.00  
% 3.86/1.00  
% 3.86/1.00  sim_fw_subset_subsumed:                 25
% 3.86/1.00  sim_bw_subset_subsumed:                 16
% 3.86/1.00  sim_fw_subsumed:                        16
% 3.86/1.00  sim_bw_subsumed:                        14
% 3.86/1.00  sim_fw_subsumption_res:                 0
% 3.86/1.00  sim_bw_subsumption_res:                 0
% 3.86/1.00  sim_tautology_del:                      1
% 3.86/1.00  sim_eq_tautology_del:                   47
% 3.86/1.00  sim_eq_res_simp:                        1
% 3.86/1.00  sim_fw_demodulated:                     40
% 3.86/1.00  sim_bw_demodulated:                     72
% 3.86/1.00  sim_light_normalised:                   73
% 3.86/1.00  sim_joinable_taut:                      0
% 3.86/1.00  sim_joinable_simp:                      0
% 3.86/1.00  sim_ac_normalised:                      0
% 3.86/1.00  sim_smt_subsumption:                    0
% 3.86/1.00  
%------------------------------------------------------------------------------

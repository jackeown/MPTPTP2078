%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:44 EST 2020

% Result     : Theorem 1.43s
% Output     : CNFRefutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  167 (1764 expanded)
%              Number of clauses        :  101 ( 604 expanded)
%              Number of leaves         :   17 ( 331 expanded)
%              Depth                    :   24
%              Number of atoms          :  499 (9104 expanded)
%              Number of equality atoms :  228 (1867 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f32])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f38,plain,(
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

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f48,plain,
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

fof(f49,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f48])).

fof(f86,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f89,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f49])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f40])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_677,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_39])).

cnf(c_678,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_680,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_678,c_38])).

cnf(c_1571,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1575,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4024,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1571,c_1575])).

cnf(c_4223,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_680,c_4024])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2843,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1571,c_1576])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_37,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_403,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_37])).

cnf(c_404,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_406,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_404,c_40])).

cnf(c_1567,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_2857,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2843,c_1567])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1573,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5484,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2857,c_1573])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1574,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3151,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1571,c_1574])).

cnf(c_36,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3163,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3151,c_36])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_389,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_37])).

cnf(c_390,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_392,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_40])).

cnf(c_1568,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_2856,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2843,c_1568])).

cnf(c_3230,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3163,c_2856])).

cnf(c_5497,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5484,c_3230])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1873,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1874,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1873])).

cnf(c_1876,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2009,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1876])).

cnf(c_2010,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2009])).

cnf(c_5848,plain,
    ( v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5497,c_41,c_43,c_1874,c_2010])).

cnf(c_5849,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5848])).

cnf(c_5854,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4223,c_5849])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_688,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != X0
    | k1_relat_1(X0) != sK2
    | k2_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_35])).

cnf(c_689,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_701,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_689,c_20])).

cnf(c_1555,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_706,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_2152,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1555,c_41,c_43,c_706,c_1874,c_2010])).

cnf(c_2153,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2152])).

cnf(c_2946,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2856,c_2153])).

cnf(c_3086,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2946,c_2857])).

cnf(c_3229,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3163,c_3086])).

cnf(c_3233,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3229])).

cnf(c_4282,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4223,c_3233])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5883,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_5884,plain,
    ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5883])).

cnf(c_5971,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5854,c_41,c_43,c_2010,c_4282,c_5884])).

cnf(c_6002,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5971,c_1571])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_6007,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6002,c_6])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | X0 != X1
    | sK0(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_360])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_1569,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_6455,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6007,c_1569])).

cnf(c_33,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_707,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_35])).

cnf(c_708,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_720,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_708,c_20])).

cnf(c_1554,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_2947,plain,
    ( k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2856,c_1554])).

cnf(c_3587,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2947,c_41,c_43,c_1874,c_2010,c_3163])).

cnf(c_3588,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3587])).

cnf(c_3591,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3588,c_2857])).

cnf(c_5988,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5971,c_3591])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_6070,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5988,c_7])).

cnf(c_5974,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5971,c_5849])).

cnf(c_6089,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5974,c_7])).

cnf(c_6960,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6070,c_41,c_43,c_2010,c_5884,c_6089])).

cnf(c_7477,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6455,c_6960])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_7495,plain,
    ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7477,c_11])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4874,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4877,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4874])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7495,c_4877])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:41:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.43/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.43/1.02  
% 1.43/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.43/1.02  
% 1.43/1.02  ------  iProver source info
% 1.43/1.02  
% 1.43/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.43/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.43/1.02  git: non_committed_changes: false
% 1.43/1.02  git: last_make_outside_of_git: false
% 1.43/1.02  
% 1.43/1.02  ------ 
% 1.43/1.02  
% 1.43/1.02  ------ Input Options
% 1.43/1.02  
% 1.43/1.02  --out_options                           all
% 1.43/1.02  --tptp_safe_out                         true
% 1.43/1.02  --problem_path                          ""
% 1.43/1.02  --include_path                          ""
% 1.43/1.02  --clausifier                            res/vclausify_rel
% 1.43/1.02  --clausifier_options                    --mode clausify
% 1.43/1.02  --stdin                                 false
% 1.43/1.02  --stats_out                             all
% 1.43/1.02  
% 1.43/1.02  ------ General Options
% 1.43/1.02  
% 1.43/1.02  --fof                                   false
% 1.43/1.02  --time_out_real                         305.
% 1.43/1.02  --time_out_virtual                      -1.
% 1.43/1.02  --symbol_type_check                     false
% 1.43/1.02  --clausify_out                          false
% 1.43/1.02  --sig_cnt_out                           false
% 1.43/1.02  --trig_cnt_out                          false
% 1.43/1.02  --trig_cnt_out_tolerance                1.
% 1.43/1.02  --trig_cnt_out_sk_spl                   false
% 1.43/1.02  --abstr_cl_out                          false
% 1.43/1.02  
% 1.43/1.02  ------ Global Options
% 1.43/1.02  
% 1.43/1.02  --schedule                              default
% 1.43/1.02  --add_important_lit                     false
% 1.43/1.02  --prop_solver_per_cl                    1000
% 1.43/1.02  --min_unsat_core                        false
% 1.43/1.02  --soft_assumptions                      false
% 1.43/1.02  --soft_lemma_size                       3
% 1.43/1.02  --prop_impl_unit_size                   0
% 1.43/1.02  --prop_impl_unit                        []
% 1.43/1.02  --share_sel_clauses                     true
% 1.43/1.02  --reset_solvers                         false
% 1.43/1.02  --bc_imp_inh                            [conj_cone]
% 1.43/1.02  --conj_cone_tolerance                   3.
% 1.43/1.02  --extra_neg_conj                        none
% 1.43/1.02  --large_theory_mode                     true
% 1.43/1.02  --prolific_symb_bound                   200
% 1.43/1.02  --lt_threshold                          2000
% 1.43/1.02  --clause_weak_htbl                      true
% 1.43/1.02  --gc_record_bc_elim                     false
% 1.43/1.02  
% 1.43/1.02  ------ Preprocessing Options
% 1.43/1.02  
% 1.43/1.02  --preprocessing_flag                    true
% 1.43/1.02  --time_out_prep_mult                    0.1
% 1.43/1.02  --splitting_mode                        input
% 1.43/1.02  --splitting_grd                         true
% 1.43/1.02  --splitting_cvd                         false
% 1.43/1.02  --splitting_cvd_svl                     false
% 1.43/1.02  --splitting_nvd                         32
% 1.43/1.02  --sub_typing                            true
% 1.43/1.02  --prep_gs_sim                           true
% 1.43/1.02  --prep_unflatten                        true
% 1.43/1.02  --prep_res_sim                          true
% 1.43/1.02  --prep_upred                            true
% 1.43/1.02  --prep_sem_filter                       exhaustive
% 1.43/1.02  --prep_sem_filter_out                   false
% 1.43/1.02  --pred_elim                             true
% 1.43/1.02  --res_sim_input                         true
% 1.43/1.02  --eq_ax_congr_red                       true
% 1.43/1.02  --pure_diseq_elim                       true
% 1.43/1.02  --brand_transform                       false
% 1.43/1.02  --non_eq_to_eq                          false
% 1.43/1.02  --prep_def_merge                        true
% 1.43/1.02  --prep_def_merge_prop_impl              false
% 1.43/1.02  --prep_def_merge_mbd                    true
% 1.43/1.02  --prep_def_merge_tr_red                 false
% 1.43/1.02  --prep_def_merge_tr_cl                  false
% 1.43/1.02  --smt_preprocessing                     true
% 1.43/1.02  --smt_ac_axioms                         fast
% 1.43/1.02  --preprocessed_out                      false
% 1.43/1.02  --preprocessed_stats                    false
% 1.43/1.02  
% 1.43/1.02  ------ Abstraction refinement Options
% 1.43/1.02  
% 1.43/1.02  --abstr_ref                             []
% 1.43/1.02  --abstr_ref_prep                        false
% 1.43/1.02  --abstr_ref_until_sat                   false
% 1.43/1.02  --abstr_ref_sig_restrict                funpre
% 1.43/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.43/1.02  --abstr_ref_under                       []
% 1.43/1.02  
% 1.43/1.02  ------ SAT Options
% 1.43/1.02  
% 1.43/1.02  --sat_mode                              false
% 1.43/1.02  --sat_fm_restart_options                ""
% 1.43/1.02  --sat_gr_def                            false
% 1.43/1.02  --sat_epr_types                         true
% 1.43/1.02  --sat_non_cyclic_types                  false
% 1.43/1.02  --sat_finite_models                     false
% 1.43/1.02  --sat_fm_lemmas                         false
% 1.43/1.02  --sat_fm_prep                           false
% 1.43/1.02  --sat_fm_uc_incr                        true
% 1.43/1.02  --sat_out_model                         small
% 1.43/1.02  --sat_out_clauses                       false
% 1.43/1.02  
% 1.43/1.02  ------ QBF Options
% 1.43/1.02  
% 1.43/1.02  --qbf_mode                              false
% 1.43/1.02  --qbf_elim_univ                         false
% 1.43/1.02  --qbf_dom_inst                          none
% 1.43/1.02  --qbf_dom_pre_inst                      false
% 1.43/1.02  --qbf_sk_in                             false
% 1.43/1.02  --qbf_pred_elim                         true
% 1.43/1.02  --qbf_split                             512
% 1.43/1.02  
% 1.43/1.02  ------ BMC1 Options
% 1.43/1.02  
% 1.43/1.02  --bmc1_incremental                      false
% 1.43/1.02  --bmc1_axioms                           reachable_all
% 1.43/1.02  --bmc1_min_bound                        0
% 1.43/1.02  --bmc1_max_bound                        -1
% 1.43/1.02  --bmc1_max_bound_default                -1
% 1.43/1.02  --bmc1_symbol_reachability              true
% 1.43/1.02  --bmc1_property_lemmas                  false
% 1.43/1.02  --bmc1_k_induction                      false
% 1.43/1.02  --bmc1_non_equiv_states                 false
% 1.43/1.02  --bmc1_deadlock                         false
% 1.43/1.02  --bmc1_ucm                              false
% 1.43/1.02  --bmc1_add_unsat_core                   none
% 1.43/1.02  --bmc1_unsat_core_children              false
% 1.43/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.43/1.02  --bmc1_out_stat                         full
% 1.43/1.02  --bmc1_ground_init                      false
% 1.43/1.02  --bmc1_pre_inst_next_state              false
% 1.43/1.02  --bmc1_pre_inst_state                   false
% 1.43/1.02  --bmc1_pre_inst_reach_state             false
% 1.43/1.02  --bmc1_out_unsat_core                   false
% 1.43/1.02  --bmc1_aig_witness_out                  false
% 1.43/1.02  --bmc1_verbose                          false
% 1.43/1.02  --bmc1_dump_clauses_tptp                false
% 1.43/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.43/1.02  --bmc1_dump_file                        -
% 1.43/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.43/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.43/1.02  --bmc1_ucm_extend_mode                  1
% 1.43/1.02  --bmc1_ucm_init_mode                    2
% 1.43/1.02  --bmc1_ucm_cone_mode                    none
% 1.43/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.43/1.02  --bmc1_ucm_relax_model                  4
% 1.43/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.43/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.43/1.02  --bmc1_ucm_layered_model                none
% 1.43/1.02  --bmc1_ucm_max_lemma_size               10
% 1.43/1.02  
% 1.43/1.02  ------ AIG Options
% 1.43/1.02  
% 1.43/1.02  --aig_mode                              false
% 1.43/1.02  
% 1.43/1.02  ------ Instantiation Options
% 1.43/1.02  
% 1.43/1.02  --instantiation_flag                    true
% 1.43/1.02  --inst_sos_flag                         false
% 1.43/1.02  --inst_sos_phase                        true
% 1.43/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.43/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.43/1.02  --inst_lit_sel_side                     num_symb
% 1.43/1.02  --inst_solver_per_active                1400
% 1.43/1.02  --inst_solver_calls_frac                1.
% 1.43/1.02  --inst_passive_queue_type               priority_queues
% 1.43/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.43/1.02  --inst_passive_queues_freq              [25;2]
% 1.43/1.02  --inst_dismatching                      true
% 1.43/1.02  --inst_eager_unprocessed_to_passive     true
% 1.43/1.02  --inst_prop_sim_given                   true
% 1.43/1.02  --inst_prop_sim_new                     false
% 1.43/1.02  --inst_subs_new                         false
% 1.43/1.02  --inst_eq_res_simp                      false
% 1.43/1.02  --inst_subs_given                       false
% 1.43/1.02  --inst_orphan_elimination               true
% 1.43/1.02  --inst_learning_loop_flag               true
% 1.43/1.02  --inst_learning_start                   3000
% 1.43/1.02  --inst_learning_factor                  2
% 1.43/1.02  --inst_start_prop_sim_after_learn       3
% 1.43/1.02  --inst_sel_renew                        solver
% 1.43/1.02  --inst_lit_activity_flag                true
% 1.43/1.02  --inst_restr_to_given                   false
% 1.43/1.02  --inst_activity_threshold               500
% 1.43/1.02  --inst_out_proof                        true
% 1.43/1.02  
% 1.43/1.02  ------ Resolution Options
% 1.43/1.02  
% 1.43/1.02  --resolution_flag                       true
% 1.43/1.02  --res_lit_sel                           adaptive
% 1.43/1.02  --res_lit_sel_side                      none
% 1.43/1.02  --res_ordering                          kbo
% 1.43/1.02  --res_to_prop_solver                    active
% 1.43/1.02  --res_prop_simpl_new                    false
% 1.43/1.02  --res_prop_simpl_given                  true
% 1.43/1.02  --res_passive_queue_type                priority_queues
% 1.43/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.43/1.02  --res_passive_queues_freq               [15;5]
% 1.43/1.02  --res_forward_subs                      full
% 1.43/1.02  --res_backward_subs                     full
% 1.43/1.02  --res_forward_subs_resolution           true
% 1.43/1.02  --res_backward_subs_resolution          true
% 1.43/1.02  --res_orphan_elimination                true
% 1.43/1.02  --res_time_limit                        2.
% 1.43/1.02  --res_out_proof                         true
% 1.43/1.02  
% 1.43/1.02  ------ Superposition Options
% 1.43/1.02  
% 1.43/1.02  --superposition_flag                    true
% 1.43/1.02  --sup_passive_queue_type                priority_queues
% 1.43/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.43/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.43/1.02  --demod_completeness_check              fast
% 1.43/1.02  --demod_use_ground                      true
% 1.43/1.02  --sup_to_prop_solver                    passive
% 1.43/1.02  --sup_prop_simpl_new                    true
% 1.43/1.02  --sup_prop_simpl_given                  true
% 1.43/1.02  --sup_fun_splitting                     false
% 1.43/1.02  --sup_smt_interval                      50000
% 1.43/1.02  
% 1.43/1.02  ------ Superposition Simplification Setup
% 1.43/1.02  
% 1.43/1.02  --sup_indices_passive                   []
% 1.43/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.43/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/1.02  --sup_full_bw                           [BwDemod]
% 1.43/1.02  --sup_immed_triv                        [TrivRules]
% 1.43/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.43/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/1.02  --sup_immed_bw_main                     []
% 1.43/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.43/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/1.02  
% 1.43/1.02  ------ Combination Options
% 1.43/1.02  
% 1.43/1.02  --comb_res_mult                         3
% 1.43/1.02  --comb_sup_mult                         2
% 1.43/1.02  --comb_inst_mult                        10
% 1.43/1.02  
% 1.43/1.02  ------ Debug Options
% 1.43/1.02  
% 1.43/1.02  --dbg_backtrace                         false
% 1.43/1.02  --dbg_dump_prop_clauses                 false
% 1.43/1.02  --dbg_dump_prop_clauses_file            -
% 1.43/1.02  --dbg_out_stat                          false
% 1.43/1.02  ------ Parsing...
% 1.43/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.43/1.02  
% 1.43/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.43/1.02  
% 1.43/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.43/1.02  
% 1.43/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.43/1.02  ------ Proving...
% 1.43/1.02  ------ Problem Properties 
% 1.43/1.02  
% 1.43/1.02  
% 1.43/1.02  clauses                                 40
% 1.43/1.02  conjectures                             3
% 1.43/1.02  EPR                                     6
% 1.43/1.02  Horn                                    33
% 1.43/1.02  unary                                   13
% 1.43/1.02  binary                                  7
% 1.43/1.02  lits                                    108
% 1.43/1.02  lits eq                                 48
% 1.43/1.02  fd_pure                                 0
% 1.43/1.02  fd_pseudo                               0
% 1.43/1.02  fd_cond                                 5
% 1.43/1.02  fd_pseudo_cond                          1
% 1.43/1.02  AC symbols                              0
% 1.43/1.02  
% 1.43/1.02  ------ Schedule dynamic 5 is on 
% 1.43/1.02  
% 1.43/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.43/1.02  
% 1.43/1.02  
% 1.43/1.02  ------ 
% 1.43/1.02  Current options:
% 1.43/1.02  ------ 
% 1.43/1.02  
% 1.43/1.02  ------ Input Options
% 1.43/1.02  
% 1.43/1.02  --out_options                           all
% 1.43/1.02  --tptp_safe_out                         true
% 1.43/1.02  --problem_path                          ""
% 1.43/1.02  --include_path                          ""
% 1.43/1.02  --clausifier                            res/vclausify_rel
% 1.43/1.02  --clausifier_options                    --mode clausify
% 1.43/1.02  --stdin                                 false
% 1.43/1.02  --stats_out                             all
% 1.43/1.02  
% 1.43/1.02  ------ General Options
% 1.43/1.02  
% 1.43/1.02  --fof                                   false
% 1.43/1.02  --time_out_real                         305.
% 1.43/1.02  --time_out_virtual                      -1.
% 1.43/1.02  --symbol_type_check                     false
% 1.43/1.02  --clausify_out                          false
% 1.43/1.02  --sig_cnt_out                           false
% 1.43/1.02  --trig_cnt_out                          false
% 1.43/1.02  --trig_cnt_out_tolerance                1.
% 1.43/1.02  --trig_cnt_out_sk_spl                   false
% 1.43/1.02  --abstr_cl_out                          false
% 1.43/1.02  
% 1.43/1.02  ------ Global Options
% 1.43/1.02  
% 1.43/1.02  --schedule                              default
% 1.43/1.02  --add_important_lit                     false
% 1.43/1.02  --prop_solver_per_cl                    1000
% 1.43/1.02  --min_unsat_core                        false
% 1.43/1.02  --soft_assumptions                      false
% 1.43/1.02  --soft_lemma_size                       3
% 1.43/1.02  --prop_impl_unit_size                   0
% 1.43/1.02  --prop_impl_unit                        []
% 1.43/1.02  --share_sel_clauses                     true
% 1.43/1.02  --reset_solvers                         false
% 1.43/1.02  --bc_imp_inh                            [conj_cone]
% 1.43/1.02  --conj_cone_tolerance                   3.
% 1.43/1.02  --extra_neg_conj                        none
% 1.43/1.02  --large_theory_mode                     true
% 1.43/1.02  --prolific_symb_bound                   200
% 1.43/1.02  --lt_threshold                          2000
% 1.43/1.02  --clause_weak_htbl                      true
% 1.43/1.02  --gc_record_bc_elim                     false
% 1.43/1.02  
% 1.43/1.02  ------ Preprocessing Options
% 1.43/1.02  
% 1.43/1.02  --preprocessing_flag                    true
% 1.43/1.02  --time_out_prep_mult                    0.1
% 1.43/1.02  --splitting_mode                        input
% 1.43/1.02  --splitting_grd                         true
% 1.43/1.02  --splitting_cvd                         false
% 1.43/1.02  --splitting_cvd_svl                     false
% 1.43/1.02  --splitting_nvd                         32
% 1.43/1.02  --sub_typing                            true
% 1.43/1.02  --prep_gs_sim                           true
% 1.43/1.02  --prep_unflatten                        true
% 1.43/1.02  --prep_res_sim                          true
% 1.43/1.02  --prep_upred                            true
% 1.43/1.02  --prep_sem_filter                       exhaustive
% 1.43/1.02  --prep_sem_filter_out                   false
% 1.43/1.02  --pred_elim                             true
% 1.43/1.02  --res_sim_input                         true
% 1.43/1.02  --eq_ax_congr_red                       true
% 1.43/1.02  --pure_diseq_elim                       true
% 1.43/1.02  --brand_transform                       false
% 1.43/1.02  --non_eq_to_eq                          false
% 1.43/1.02  --prep_def_merge                        true
% 1.43/1.02  --prep_def_merge_prop_impl              false
% 1.43/1.02  --prep_def_merge_mbd                    true
% 1.43/1.02  --prep_def_merge_tr_red                 false
% 1.43/1.02  --prep_def_merge_tr_cl                  false
% 1.43/1.02  --smt_preprocessing                     true
% 1.43/1.02  --smt_ac_axioms                         fast
% 1.43/1.02  --preprocessed_out                      false
% 1.43/1.02  --preprocessed_stats                    false
% 1.43/1.02  
% 1.43/1.02  ------ Abstraction refinement Options
% 1.43/1.02  
% 1.43/1.02  --abstr_ref                             []
% 1.43/1.02  --abstr_ref_prep                        false
% 1.43/1.02  --abstr_ref_until_sat                   false
% 1.43/1.02  --abstr_ref_sig_restrict                funpre
% 1.43/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.43/1.02  --abstr_ref_under                       []
% 1.43/1.02  
% 1.43/1.02  ------ SAT Options
% 1.43/1.02  
% 1.43/1.02  --sat_mode                              false
% 1.43/1.02  --sat_fm_restart_options                ""
% 1.43/1.02  --sat_gr_def                            false
% 1.43/1.02  --sat_epr_types                         true
% 1.43/1.02  --sat_non_cyclic_types                  false
% 1.43/1.02  --sat_finite_models                     false
% 1.43/1.02  --sat_fm_lemmas                         false
% 1.43/1.02  --sat_fm_prep                           false
% 1.43/1.02  --sat_fm_uc_incr                        true
% 1.43/1.02  --sat_out_model                         small
% 1.43/1.02  --sat_out_clauses                       false
% 1.43/1.02  
% 1.43/1.02  ------ QBF Options
% 1.43/1.02  
% 1.43/1.02  --qbf_mode                              false
% 1.43/1.02  --qbf_elim_univ                         false
% 1.43/1.02  --qbf_dom_inst                          none
% 1.43/1.02  --qbf_dom_pre_inst                      false
% 1.43/1.02  --qbf_sk_in                             false
% 1.43/1.02  --qbf_pred_elim                         true
% 1.43/1.02  --qbf_split                             512
% 1.43/1.02  
% 1.43/1.02  ------ BMC1 Options
% 1.43/1.02  
% 1.43/1.02  --bmc1_incremental                      false
% 1.43/1.02  --bmc1_axioms                           reachable_all
% 1.43/1.02  --bmc1_min_bound                        0
% 1.43/1.02  --bmc1_max_bound                        -1
% 1.43/1.02  --bmc1_max_bound_default                -1
% 1.43/1.02  --bmc1_symbol_reachability              true
% 1.43/1.02  --bmc1_property_lemmas                  false
% 1.43/1.02  --bmc1_k_induction                      false
% 1.43/1.02  --bmc1_non_equiv_states                 false
% 1.43/1.02  --bmc1_deadlock                         false
% 1.43/1.02  --bmc1_ucm                              false
% 1.43/1.02  --bmc1_add_unsat_core                   none
% 1.43/1.02  --bmc1_unsat_core_children              false
% 1.43/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.43/1.02  --bmc1_out_stat                         full
% 1.43/1.02  --bmc1_ground_init                      false
% 1.43/1.02  --bmc1_pre_inst_next_state              false
% 1.43/1.02  --bmc1_pre_inst_state                   false
% 1.43/1.02  --bmc1_pre_inst_reach_state             false
% 1.43/1.02  --bmc1_out_unsat_core                   false
% 1.43/1.02  --bmc1_aig_witness_out                  false
% 1.43/1.02  --bmc1_verbose                          false
% 1.43/1.02  --bmc1_dump_clauses_tptp                false
% 1.43/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.43/1.02  --bmc1_dump_file                        -
% 1.43/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.43/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.43/1.02  --bmc1_ucm_extend_mode                  1
% 1.43/1.02  --bmc1_ucm_init_mode                    2
% 1.43/1.02  --bmc1_ucm_cone_mode                    none
% 1.43/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.43/1.02  --bmc1_ucm_relax_model                  4
% 1.43/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.43/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.43/1.02  --bmc1_ucm_layered_model                none
% 1.43/1.02  --bmc1_ucm_max_lemma_size               10
% 1.43/1.02  
% 1.43/1.02  ------ AIG Options
% 1.43/1.02  
% 1.43/1.02  --aig_mode                              false
% 1.43/1.02  
% 1.43/1.02  ------ Instantiation Options
% 1.43/1.02  
% 1.43/1.02  --instantiation_flag                    true
% 1.43/1.02  --inst_sos_flag                         false
% 1.43/1.02  --inst_sos_phase                        true
% 1.43/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.43/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.43/1.02  --inst_lit_sel_side                     none
% 1.43/1.02  --inst_solver_per_active                1400
% 1.43/1.02  --inst_solver_calls_frac                1.
% 1.43/1.02  --inst_passive_queue_type               priority_queues
% 1.43/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.43/1.02  --inst_passive_queues_freq              [25;2]
% 1.43/1.02  --inst_dismatching                      true
% 1.43/1.02  --inst_eager_unprocessed_to_passive     true
% 1.43/1.02  --inst_prop_sim_given                   true
% 1.43/1.02  --inst_prop_sim_new                     false
% 1.43/1.02  --inst_subs_new                         false
% 1.43/1.02  --inst_eq_res_simp                      false
% 1.43/1.02  --inst_subs_given                       false
% 1.43/1.02  --inst_orphan_elimination               true
% 1.43/1.02  --inst_learning_loop_flag               true
% 1.43/1.02  --inst_learning_start                   3000
% 1.43/1.02  --inst_learning_factor                  2
% 1.43/1.02  --inst_start_prop_sim_after_learn       3
% 1.43/1.02  --inst_sel_renew                        solver
% 1.43/1.02  --inst_lit_activity_flag                true
% 1.43/1.02  --inst_restr_to_given                   false
% 1.43/1.02  --inst_activity_threshold               500
% 1.43/1.02  --inst_out_proof                        true
% 1.43/1.02  
% 1.43/1.02  ------ Resolution Options
% 1.43/1.02  
% 1.43/1.02  --resolution_flag                       false
% 1.43/1.02  --res_lit_sel                           adaptive
% 1.43/1.02  --res_lit_sel_side                      none
% 1.43/1.02  --res_ordering                          kbo
% 1.43/1.02  --res_to_prop_solver                    active
% 1.43/1.02  --res_prop_simpl_new                    false
% 1.43/1.02  --res_prop_simpl_given                  true
% 1.43/1.02  --res_passive_queue_type                priority_queues
% 1.43/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.43/1.02  --res_passive_queues_freq               [15;5]
% 1.43/1.02  --res_forward_subs                      full
% 1.43/1.02  --res_backward_subs                     full
% 1.43/1.02  --res_forward_subs_resolution           true
% 1.43/1.02  --res_backward_subs_resolution          true
% 1.43/1.02  --res_orphan_elimination                true
% 1.43/1.02  --res_time_limit                        2.
% 1.43/1.02  --res_out_proof                         true
% 1.43/1.02  
% 1.43/1.02  ------ Superposition Options
% 1.43/1.02  
% 1.43/1.02  --superposition_flag                    true
% 1.43/1.02  --sup_passive_queue_type                priority_queues
% 1.43/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.43/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.43/1.02  --demod_completeness_check              fast
% 1.43/1.02  --demod_use_ground                      true
% 1.43/1.02  --sup_to_prop_solver                    passive
% 1.43/1.02  --sup_prop_simpl_new                    true
% 1.43/1.02  --sup_prop_simpl_given                  true
% 1.43/1.02  --sup_fun_splitting                     false
% 1.43/1.02  --sup_smt_interval                      50000
% 1.43/1.02  
% 1.43/1.02  ------ Superposition Simplification Setup
% 1.43/1.02  
% 1.43/1.02  --sup_indices_passive                   []
% 1.43/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.43/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/1.02  --sup_full_bw                           [BwDemod]
% 1.43/1.02  --sup_immed_triv                        [TrivRules]
% 1.43/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.43/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/1.02  --sup_immed_bw_main                     []
% 1.43/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.43/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/1.02  
% 1.43/1.02  ------ Combination Options
% 1.43/1.02  
% 1.43/1.02  --comb_res_mult                         3
% 1.43/1.02  --comb_sup_mult                         2
% 1.43/1.02  --comb_inst_mult                        10
% 1.43/1.02  
% 1.43/1.02  ------ Debug Options
% 1.43/1.02  
% 1.43/1.02  --dbg_backtrace                         false
% 1.43/1.02  --dbg_dump_prop_clauses                 false
% 1.43/1.02  --dbg_dump_prop_clauses_file            -
% 1.43/1.02  --dbg_out_stat                          false
% 1.43/1.02  
% 1.43/1.02  
% 1.43/1.02  
% 1.43/1.02  
% 1.43/1.02  ------ Proving...
% 1.43/1.02  
% 1.43/1.02  
% 1.43/1.02  % SZS status Theorem for theBenchmark.p
% 1.43/1.02  
% 1.43/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.43/1.02  
% 1.43/1.02  fof(f16,axiom,(
% 1.43/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f32,plain,(
% 1.43/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/1.02    inference(ennf_transformation,[],[f16])).
% 1.43/1.02  
% 1.43/1.02  fof(f33,plain,(
% 1.43/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/1.02    inference(flattening,[],[f32])).
% 1.43/1.02  
% 1.43/1.02  fof(f47,plain,(
% 1.43/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/1.02    inference(nnf_transformation,[],[f33])).
% 1.43/1.02  
% 1.43/1.02  fof(f73,plain,(
% 1.43/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/1.02    inference(cnf_transformation,[],[f47])).
% 1.43/1.02  
% 1.43/1.02  fof(f19,conjecture,(
% 1.43/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f20,negated_conjecture,(
% 1.43/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.43/1.02    inference(negated_conjecture,[],[f19])).
% 1.43/1.02  
% 1.43/1.02  fof(f38,plain,(
% 1.43/1.02    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.43/1.02    inference(ennf_transformation,[],[f20])).
% 1.43/1.02  
% 1.43/1.02  fof(f39,plain,(
% 1.43/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.43/1.02    inference(flattening,[],[f38])).
% 1.43/1.02  
% 1.43/1.02  fof(f48,plain,(
% 1.43/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.43/1.02    introduced(choice_axiom,[])).
% 1.43/1.02  
% 1.43/1.02  fof(f49,plain,(
% 1.43/1.02    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.43/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f48])).
% 1.43/1.02  
% 1.43/1.02  fof(f86,plain,(
% 1.43/1.02    v1_funct_2(sK3,sK1,sK2)),
% 1.43/1.02    inference(cnf_transformation,[],[f49])).
% 1.43/1.02  
% 1.43/1.02  fof(f87,plain,(
% 1.43/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.43/1.02    inference(cnf_transformation,[],[f49])).
% 1.43/1.02  
% 1.43/1.02  fof(f14,axiom,(
% 1.43/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f30,plain,(
% 1.43/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/1.02    inference(ennf_transformation,[],[f14])).
% 1.43/1.02  
% 1.43/1.02  fof(f71,plain,(
% 1.43/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/1.02    inference(cnf_transformation,[],[f30])).
% 1.43/1.02  
% 1.43/1.02  fof(f13,axiom,(
% 1.43/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f29,plain,(
% 1.43/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/1.02    inference(ennf_transformation,[],[f13])).
% 1.43/1.02  
% 1.43/1.02  fof(f70,plain,(
% 1.43/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/1.02    inference(cnf_transformation,[],[f29])).
% 1.43/1.02  
% 1.43/1.02  fof(f10,axiom,(
% 1.43/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f27,plain,(
% 1.43/1.02    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.43/1.02    inference(ennf_transformation,[],[f10])).
% 1.43/1.02  
% 1.43/1.02  fof(f28,plain,(
% 1.43/1.02    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.43/1.02    inference(flattening,[],[f27])).
% 1.43/1.02  
% 1.43/1.02  fof(f66,plain,(
% 1.43/1.02    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/1.02    inference(cnf_transformation,[],[f28])).
% 1.43/1.02  
% 1.43/1.02  fof(f88,plain,(
% 1.43/1.02    v2_funct_1(sK3)),
% 1.43/1.02    inference(cnf_transformation,[],[f49])).
% 1.43/1.02  
% 1.43/1.02  fof(f85,plain,(
% 1.43/1.02    v1_funct_1(sK3)),
% 1.43/1.02    inference(cnf_transformation,[],[f49])).
% 1.43/1.02  
% 1.43/1.02  fof(f17,axiom,(
% 1.43/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f34,plain,(
% 1.43/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.43/1.02    inference(ennf_transformation,[],[f17])).
% 1.43/1.02  
% 1.43/1.02  fof(f35,plain,(
% 1.43/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.43/1.02    inference(flattening,[],[f34])).
% 1.43/1.02  
% 1.43/1.02  fof(f81,plain,(
% 1.43/1.02    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/1.02    inference(cnf_transformation,[],[f35])).
% 1.43/1.02  
% 1.43/1.02  fof(f15,axiom,(
% 1.43/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f31,plain,(
% 1.43/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/1.02    inference(ennf_transformation,[],[f15])).
% 1.43/1.02  
% 1.43/1.02  fof(f72,plain,(
% 1.43/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/1.02    inference(cnf_transformation,[],[f31])).
% 1.43/1.02  
% 1.43/1.02  fof(f89,plain,(
% 1.43/1.02    k2_relset_1(sK1,sK2,sK3) = sK2),
% 1.43/1.02    inference(cnf_transformation,[],[f49])).
% 1.43/1.02  
% 1.43/1.02  fof(f65,plain,(
% 1.43/1.02    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/1.02    inference(cnf_transformation,[],[f28])).
% 1.43/1.02  
% 1.43/1.02  fof(f9,axiom,(
% 1.43/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f25,plain,(
% 1.43/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.43/1.02    inference(ennf_transformation,[],[f9])).
% 1.43/1.02  
% 1.43/1.02  fof(f26,plain,(
% 1.43/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.43/1.02    inference(flattening,[],[f25])).
% 1.43/1.02  
% 1.43/1.02  fof(f64,plain,(
% 1.43/1.02    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/1.02    inference(cnf_transformation,[],[f26])).
% 1.43/1.02  
% 1.43/1.02  fof(f80,plain,(
% 1.43/1.02    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/1.02    inference(cnf_transformation,[],[f35])).
% 1.43/1.02  
% 1.43/1.02  fof(f90,plain,(
% 1.43/1.02    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.43/1.02    inference(cnf_transformation,[],[f49])).
% 1.43/1.02  
% 1.43/1.02  fof(f63,plain,(
% 1.43/1.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/1.02    inference(cnf_transformation,[],[f26])).
% 1.43/1.02  
% 1.43/1.02  fof(f5,axiom,(
% 1.43/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f44,plain,(
% 1.43/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.43/1.02    inference(nnf_transformation,[],[f5])).
% 1.43/1.02  
% 1.43/1.02  fof(f45,plain,(
% 1.43/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.43/1.02    inference(flattening,[],[f44])).
% 1.43/1.02  
% 1.43/1.02  fof(f58,plain,(
% 1.43/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.43/1.02    inference(cnf_transformation,[],[f45])).
% 1.43/1.02  
% 1.43/1.02  fof(f93,plain,(
% 1.43/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.43/1.02    inference(equality_resolution,[],[f58])).
% 1.43/1.02  
% 1.43/1.02  fof(f2,axiom,(
% 1.43/1.02    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f23,plain,(
% 1.43/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.43/1.02    inference(ennf_transformation,[],[f2])).
% 1.43/1.02  
% 1.43/1.02  fof(f40,plain,(
% 1.43/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.43/1.02    introduced(choice_axiom,[])).
% 1.43/1.02  
% 1.43/1.02  fof(f41,plain,(
% 1.43/1.02    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.43/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f40])).
% 1.43/1.02  
% 1.43/1.02  fof(f51,plain,(
% 1.43/1.02    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.43/1.02    inference(cnf_transformation,[],[f41])).
% 1.43/1.02  
% 1.43/1.02  fof(f1,axiom,(
% 1.43/1.02    v1_xboole_0(k1_xboole_0)),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f50,plain,(
% 1.43/1.02    v1_xboole_0(k1_xboole_0)),
% 1.43/1.02    inference(cnf_transformation,[],[f1])).
% 1.43/1.02  
% 1.43/1.02  fof(f6,axiom,(
% 1.43/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f24,plain,(
% 1.43/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.43/1.02    inference(ennf_transformation,[],[f6])).
% 1.43/1.02  
% 1.43/1.02  fof(f59,plain,(
% 1.43/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.43/1.02    inference(cnf_transformation,[],[f24])).
% 1.43/1.02  
% 1.43/1.02  fof(f18,axiom,(
% 1.43/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f36,plain,(
% 1.43/1.02    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.43/1.02    inference(ennf_transformation,[],[f18])).
% 1.43/1.02  
% 1.43/1.02  fof(f37,plain,(
% 1.43/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.43/1.02    inference(flattening,[],[f36])).
% 1.43/1.02  
% 1.43/1.02  fof(f83,plain,(
% 1.43/1.02    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.43/1.02    inference(cnf_transformation,[],[f37])).
% 1.43/1.02  
% 1.43/1.02  fof(f57,plain,(
% 1.43/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.43/1.02    inference(cnf_transformation,[],[f45])).
% 1.43/1.02  
% 1.43/1.02  fof(f94,plain,(
% 1.43/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.43/1.02    inference(equality_resolution,[],[f57])).
% 1.43/1.02  
% 1.43/1.02  fof(f7,axiom,(
% 1.43/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f60,plain,(
% 1.43/1.02    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.43/1.02    inference(cnf_transformation,[],[f7])).
% 1.43/1.02  
% 1.43/1.02  fof(f4,axiom,(
% 1.43/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.43/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/1.02  
% 1.43/1.02  fof(f55,plain,(
% 1.43/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.43/1.02    inference(cnf_transformation,[],[f4])).
% 1.43/1.02  
% 1.43/1.02  cnf(c_28,plain,
% 1.43/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.43/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.43/1.02      | k1_relset_1(X1,X2,X0) = X1
% 1.43/1.02      | k1_xboole_0 = X2 ),
% 1.43/1.02      inference(cnf_transformation,[],[f73]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_39,negated_conjecture,
% 1.43/1.02      ( v1_funct_2(sK3,sK1,sK2) ),
% 1.43/1.02      inference(cnf_transformation,[],[f86]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_677,plain,
% 1.43/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.43/1.02      | k1_relset_1(X1,X2,X0) = X1
% 1.43/1.02      | sK1 != X1
% 1.43/1.02      | sK2 != X2
% 1.43/1.02      | sK3 != X0
% 1.43/1.02      | k1_xboole_0 = X2 ),
% 1.43/1.02      inference(resolution_lifted,[status(thm)],[c_28,c_39]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_678,plain,
% 1.43/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.43/1.02      | k1_relset_1(sK1,sK2,sK3) = sK1
% 1.43/1.02      | k1_xboole_0 = sK2 ),
% 1.43/1.02      inference(unflattening,[status(thm)],[c_677]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_38,negated_conjecture,
% 1.43/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.43/1.02      inference(cnf_transformation,[],[f87]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_680,plain,
% 1.43/1.02      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 1.43/1.02      inference(global_propositional_subsumption,
% 1.43/1.02                [status(thm)],
% 1.43/1.02                [c_678,c_38]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1571,plain,
% 1.43/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_21,plain,
% 1.43/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.43/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.43/1.02      inference(cnf_transformation,[],[f71]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1575,plain,
% 1.43/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.43/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_4024,plain,
% 1.43/1.02      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 1.43/1.02      inference(superposition,[status(thm)],[c_1571,c_1575]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_4223,plain,
% 1.43/1.02      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 1.43/1.02      inference(superposition,[status(thm)],[c_680,c_4024]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_20,plain,
% 1.43/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.43/1.02      | v1_relat_1(X0) ),
% 1.43/1.02      inference(cnf_transformation,[],[f70]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1576,plain,
% 1.43/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.43/1.02      | v1_relat_1(X0) = iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_2843,plain,
% 1.43/1.02      ( v1_relat_1(sK3) = iProver_top ),
% 1.43/1.02      inference(superposition,[status(thm)],[c_1571,c_1576]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_15,plain,
% 1.43/1.02      ( ~ v2_funct_1(X0)
% 1.43/1.02      | ~ v1_relat_1(X0)
% 1.43/1.02      | ~ v1_funct_1(X0)
% 1.43/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 1.43/1.02      inference(cnf_transformation,[],[f66]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_37,negated_conjecture,
% 1.43/1.02      ( v2_funct_1(sK3) ),
% 1.43/1.02      inference(cnf_transformation,[],[f88]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_403,plain,
% 1.43/1.02      ( ~ v1_relat_1(X0)
% 1.43/1.02      | ~ v1_funct_1(X0)
% 1.43/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 1.43/1.02      | sK3 != X0 ),
% 1.43/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_37]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_404,plain,
% 1.43/1.02      ( ~ v1_relat_1(sK3)
% 1.43/1.02      | ~ v1_funct_1(sK3)
% 1.43/1.02      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 1.43/1.02      inference(unflattening,[status(thm)],[c_403]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_40,negated_conjecture,
% 1.43/1.02      ( v1_funct_1(sK3) ),
% 1.43/1.02      inference(cnf_transformation,[],[f85]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_406,plain,
% 1.43/1.02      ( ~ v1_relat_1(sK3)
% 1.43/1.02      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 1.43/1.02      inference(global_propositional_subsumption,
% 1.43/1.02                [status(thm)],
% 1.43/1.02                [c_404,c_40]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1567,plain,
% 1.43/1.02      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 1.43/1.02      | v1_relat_1(sK3) != iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_2857,plain,
% 1.43/1.02      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 1.43/1.02      inference(superposition,[status(thm)],[c_2843,c_1567]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_29,plain,
% 1.43/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 1.43/1.02      | ~ v1_relat_1(X0)
% 1.43/1.02      | ~ v1_funct_1(X0) ),
% 1.43/1.02      inference(cnf_transformation,[],[f81]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1573,plain,
% 1.43/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 1.43/1.02      | v1_relat_1(X0) != iProver_top
% 1.43/1.02      | v1_funct_1(X0) != iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_5484,plain,
% 1.43/1.02      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 1.43/1.02      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 1.43/1.02      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 1.43/1.02      inference(superposition,[status(thm)],[c_2857,c_1573]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_22,plain,
% 1.43/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.43/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.43/1.02      inference(cnf_transformation,[],[f72]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1574,plain,
% 1.43/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.43/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_3151,plain,
% 1.43/1.02      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 1.43/1.02      inference(superposition,[status(thm)],[c_1571,c_1574]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_36,negated_conjecture,
% 1.43/1.02      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 1.43/1.02      inference(cnf_transformation,[],[f89]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_3163,plain,
% 1.43/1.02      ( k2_relat_1(sK3) = sK2 ),
% 1.43/1.02      inference(light_normalisation,[status(thm)],[c_3151,c_36]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_16,plain,
% 1.43/1.02      ( ~ v2_funct_1(X0)
% 1.43/1.02      | ~ v1_relat_1(X0)
% 1.43/1.02      | ~ v1_funct_1(X0)
% 1.43/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 1.43/1.02      inference(cnf_transformation,[],[f65]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_389,plain,
% 1.43/1.02      ( ~ v1_relat_1(X0)
% 1.43/1.02      | ~ v1_funct_1(X0)
% 1.43/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 1.43/1.02      | sK3 != X0 ),
% 1.43/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_37]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_390,plain,
% 1.43/1.02      ( ~ v1_relat_1(sK3)
% 1.43/1.02      | ~ v1_funct_1(sK3)
% 1.43/1.02      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 1.43/1.02      inference(unflattening,[status(thm)],[c_389]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_392,plain,
% 1.43/1.02      ( ~ v1_relat_1(sK3)
% 1.43/1.02      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 1.43/1.02      inference(global_propositional_subsumption,
% 1.43/1.02                [status(thm)],
% 1.43/1.02                [c_390,c_40]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1568,plain,
% 1.43/1.02      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 1.43/1.02      | v1_relat_1(sK3) != iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_2856,plain,
% 1.43/1.02      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 1.43/1.02      inference(superposition,[status(thm)],[c_2843,c_1568]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_3230,plain,
% 1.43/1.02      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 1.43/1.02      inference(demodulation,[status(thm)],[c_3163,c_2856]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_5497,plain,
% 1.43/1.02      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 1.43/1.02      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 1.43/1.02      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 1.43/1.02      inference(light_normalisation,[status(thm)],[c_5484,c_3230]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_41,plain,
% 1.43/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_43,plain,
% 1.43/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_13,plain,
% 1.43/1.02      ( ~ v1_relat_1(X0)
% 1.43/1.02      | ~ v1_funct_1(X0)
% 1.43/1.02      | v1_funct_1(k2_funct_1(X0)) ),
% 1.43/1.02      inference(cnf_transformation,[],[f64]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1873,plain,
% 1.43/1.02      ( ~ v1_relat_1(sK3)
% 1.43/1.02      | v1_funct_1(k2_funct_1(sK3))
% 1.43/1.02      | ~ v1_funct_1(sK3) ),
% 1.43/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1874,plain,
% 1.43/1.02      ( v1_relat_1(sK3) != iProver_top
% 1.43/1.02      | v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 1.43/1.02      | v1_funct_1(sK3) != iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_1873]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1876,plain,
% 1.43/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.43/1.02      | v1_relat_1(sK3) ),
% 1.43/1.02      inference(instantiation,[status(thm)],[c_20]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_2009,plain,
% 1.43/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.43/1.02      | v1_relat_1(sK3) ),
% 1.43/1.02      inference(instantiation,[status(thm)],[c_1876]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_2010,plain,
% 1.43/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 1.43/1.02      | v1_relat_1(sK3) = iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_2009]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_5848,plain,
% 1.43/1.02      ( v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 1.43/1.02      inference(global_propositional_subsumption,
% 1.43/1.02                [status(thm)],
% 1.43/1.02                [c_5497,c_41,c_43,c_1874,c_2010]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_5849,plain,
% 1.43/1.02      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 1.43/1.02      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 1.43/1.02      inference(renaming,[status(thm)],[c_5848]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_5854,plain,
% 1.43/1.02      ( sK2 = k1_xboole_0
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
% 1.43/1.02      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 1.43/1.02      inference(superposition,[status(thm)],[c_4223,c_5849]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_30,plain,
% 1.43/1.02      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 1.43/1.02      | ~ v1_relat_1(X0)
% 1.43/1.02      | ~ v1_funct_1(X0) ),
% 1.43/1.02      inference(cnf_transformation,[],[f80]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_35,negated_conjecture,
% 1.43/1.02      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 1.43/1.02      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.43/1.02      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 1.43/1.02      inference(cnf_transformation,[],[f90]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_688,plain,
% 1.43/1.02      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.43/1.02      | ~ v1_relat_1(X0)
% 1.43/1.02      | ~ v1_funct_1(X0)
% 1.43/1.02      | ~ v1_funct_1(k2_funct_1(sK3))
% 1.43/1.02      | k2_funct_1(sK3) != X0
% 1.43/1.02      | k1_relat_1(X0) != sK2
% 1.43/1.02      | k2_relat_1(X0) != sK1 ),
% 1.43/1.02      inference(resolution_lifted,[status(thm)],[c_30,c_35]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_689,plain,
% 1.43/1.02      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.43/1.02      | ~ v1_relat_1(k2_funct_1(sK3))
% 1.43/1.02      | ~ v1_funct_1(k2_funct_1(sK3))
% 1.43/1.02      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 1.43/1.02      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 1.43/1.02      inference(unflattening,[status(thm)],[c_688]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_701,plain,
% 1.43/1.02      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.43/1.02      | ~ v1_funct_1(k2_funct_1(sK3))
% 1.43/1.02      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 1.43/1.02      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 1.43/1.02      inference(forward_subsumption_resolution,
% 1.43/1.02                [status(thm)],
% 1.43/1.02                [c_689,c_20]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1555,plain,
% 1.43/1.02      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 1.43/1.02      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.43/1.02      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_706,plain,
% 1.43/1.02      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 1.43/1.02      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.43/1.02      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_2152,plain,
% 1.43/1.02      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.43/1.02      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 1.43/1.02      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 1.43/1.02      inference(global_propositional_subsumption,
% 1.43/1.02                [status(thm)],
% 1.43/1.02                [c_1555,c_41,c_43,c_706,c_1874,c_2010]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_2153,plain,
% 1.43/1.02      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 1.43/1.02      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 1.43/1.02      inference(renaming,[status(thm)],[c_2152]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_2946,plain,
% 1.43/1.02      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 1.43/1.02      | k2_relat_1(sK3) != sK2
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 1.43/1.02      inference(demodulation,[status(thm)],[c_2856,c_2153]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_3086,plain,
% 1.43/1.02      ( k1_relat_1(sK3) != sK1
% 1.43/1.02      | k2_relat_1(sK3) != sK2
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 1.43/1.02      inference(light_normalisation,[status(thm)],[c_2946,c_2857]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_3229,plain,
% 1.43/1.02      ( k1_relat_1(sK3) != sK1
% 1.43/1.02      | sK2 != sK2
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 1.43/1.02      inference(demodulation,[status(thm)],[c_3163,c_3086]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_3233,plain,
% 1.43/1.02      ( k1_relat_1(sK3) != sK1
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 1.43/1.02      inference(equality_resolution_simp,[status(thm)],[c_3229]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_4282,plain,
% 1.43/1.02      ( sK2 = k1_xboole_0
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 1.43/1.02      inference(superposition,[status(thm)],[c_4223,c_3233]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_14,plain,
% 1.43/1.02      ( ~ v1_relat_1(X0)
% 1.43/1.02      | v1_relat_1(k2_funct_1(X0))
% 1.43/1.02      | ~ v1_funct_1(X0) ),
% 1.43/1.02      inference(cnf_transformation,[],[f63]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_5883,plain,
% 1.43/1.02      ( v1_relat_1(k2_funct_1(sK3))
% 1.43/1.02      | ~ v1_relat_1(sK3)
% 1.43/1.02      | ~ v1_funct_1(sK3) ),
% 1.43/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_5884,plain,
% 1.43/1.02      ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 1.43/1.02      | v1_relat_1(sK3) != iProver_top
% 1.43/1.02      | v1_funct_1(sK3) != iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_5883]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_5971,plain,
% 1.43/1.02      ( sK2 = k1_xboole_0 ),
% 1.43/1.02      inference(global_propositional_subsumption,
% 1.43/1.02                [status(thm)],
% 1.43/1.02                [c_5854,c_41,c_43,c_2010,c_4282,c_5884]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_6002,plain,
% 1.43/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 1.43/1.02      inference(demodulation,[status(thm)],[c_5971,c_1571]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_6,plain,
% 1.43/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.43/1.02      inference(cnf_transformation,[],[f93]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_6007,plain,
% 1.43/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.43/1.02      inference(demodulation,[status(thm)],[c_6002,c_6]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1,plain,
% 1.43/1.02      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.43/1.02      inference(cnf_transformation,[],[f51]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_0,plain,
% 1.43/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 1.43/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_9,plain,
% 1.43/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.43/1.02      | ~ r2_hidden(X2,X0)
% 1.43/1.02      | ~ v1_xboole_0(X1) ),
% 1.43/1.02      inference(cnf_transformation,[],[f59]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_359,plain,
% 1.43/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.43/1.02      | ~ r2_hidden(X2,X0)
% 1.43/1.02      | k1_xboole_0 != X1 ),
% 1.43/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_360,plain,
% 1.43/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~ r2_hidden(X1,X0) ),
% 1.43/1.02      inference(unflattening,[status(thm)],[c_359]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_374,plain,
% 1.43/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 1.43/1.02      | X0 != X1
% 1.43/1.02      | sK0(X1) != X2
% 1.43/1.02      | k1_xboole_0 = X1 ),
% 1.43/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_360]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_375,plain,
% 1.43/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 1.43/1.02      inference(unflattening,[status(thm)],[c_374]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1569,plain,
% 1.43/1.02      ( k1_xboole_0 = X0
% 1.43/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_6455,plain,
% 1.43/1.02      ( sK3 = k1_xboole_0 ),
% 1.43/1.02      inference(superposition,[status(thm)],[c_6007,c_1569]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_33,plain,
% 1.43/1.02      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 1.43/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 1.43/1.02      | ~ v1_relat_1(X0)
% 1.43/1.02      | ~ v1_funct_1(X0) ),
% 1.43/1.02      inference(cnf_transformation,[],[f83]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_707,plain,
% 1.43/1.02      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.43/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 1.43/1.02      | ~ v1_relat_1(X0)
% 1.43/1.02      | ~ v1_funct_1(X0)
% 1.43/1.02      | ~ v1_funct_1(k2_funct_1(sK3))
% 1.43/1.02      | k2_funct_1(sK3) != X0
% 1.43/1.02      | k1_relat_1(X0) != sK2
% 1.43/1.02      | sK1 != X1 ),
% 1.43/1.02      inference(resolution_lifted,[status(thm)],[c_33,c_35]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_708,plain,
% 1.43/1.02      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.43/1.02      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 1.43/1.02      | ~ v1_relat_1(k2_funct_1(sK3))
% 1.43/1.02      | ~ v1_funct_1(k2_funct_1(sK3))
% 1.43/1.02      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 1.43/1.02      inference(unflattening,[status(thm)],[c_707]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_720,plain,
% 1.43/1.02      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 1.43/1.02      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 1.43/1.02      | ~ v1_funct_1(k2_funct_1(sK3))
% 1.43/1.02      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 1.43/1.02      inference(forward_subsumption_resolution,
% 1.43/1.02                [status(thm)],
% 1.43/1.02                [c_708,c_20]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_1554,plain,
% 1.43/1.02      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.43/1.02      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 1.43/1.02      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_2947,plain,
% 1.43/1.02      ( k2_relat_1(sK3) != sK2
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.43/1.02      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 1.43/1.02      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 1.43/1.02      inference(demodulation,[status(thm)],[c_2856,c_1554]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_3587,plain,
% 1.43/1.02      ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 1.43/1.02      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 1.43/1.02      inference(global_propositional_subsumption,
% 1.43/1.02                [status(thm)],
% 1.43/1.02                [c_2947,c_41,c_43,c_1874,c_2010,c_3163]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_3588,plain,
% 1.43/1.02      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.43/1.02      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top ),
% 1.43/1.02      inference(renaming,[status(thm)],[c_3587]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_3591,plain,
% 1.43/1.02      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 1.43/1.02      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 1.43/1.02      inference(light_normalisation,[status(thm)],[c_3588,c_2857]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_5988,plain,
% 1.43/1.02      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 1.43/1.02      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 1.43/1.02      inference(demodulation,[status(thm)],[c_5971,c_3591]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_7,plain,
% 1.43/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.43/1.02      inference(cnf_transformation,[],[f94]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_6070,plain,
% 1.43/1.02      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.43/1.02      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 1.43/1.02      inference(demodulation,[status(thm)],[c_5988,c_7]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_5974,plain,
% 1.43/1.02      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top
% 1.43/1.02      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 1.43/1.02      inference(demodulation,[status(thm)],[c_5971,c_5849]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_6089,plain,
% 1.43/1.02      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.43/1.02      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 1.43/1.02      inference(demodulation,[status(thm)],[c_5974,c_7]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_6960,plain,
% 1.43/1.02      ( r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 1.43/1.02      inference(global_propositional_subsumption,
% 1.43/1.02                [status(thm)],
% 1.43/1.02                [c_6070,c_41,c_43,c_2010,c_5884,c_6089]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_7477,plain,
% 1.43/1.02      ( r1_tarski(k1_relat_1(k1_xboole_0),sK1) != iProver_top ),
% 1.43/1.02      inference(demodulation,[status(thm)],[c_6455,c_6960]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_11,plain,
% 1.43/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.43/1.02      inference(cnf_transformation,[],[f60]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_7495,plain,
% 1.43/1.02      ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 1.43/1.02      inference(light_normalisation,[status(thm)],[c_7477,c_11]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_5,plain,
% 1.43/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 1.43/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_4874,plain,
% 1.43/1.02      ( r1_tarski(k1_xboole_0,sK1) ),
% 1.43/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(c_4877,plain,
% 1.43/1.02      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 1.43/1.02      inference(predicate_to_equality,[status(thm)],[c_4874]) ).
% 1.43/1.02  
% 1.43/1.02  cnf(contradiction,plain,
% 1.43/1.02      ( $false ),
% 1.43/1.02      inference(minisat,[status(thm)],[c_7495,c_4877]) ).
% 1.43/1.02  
% 1.43/1.02  
% 1.43/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.43/1.02  
% 1.43/1.02  ------                               Statistics
% 1.43/1.02  
% 1.43/1.02  ------ General
% 1.43/1.02  
% 1.43/1.02  abstr_ref_over_cycles:                  0
% 1.43/1.02  abstr_ref_under_cycles:                 0
% 1.43/1.02  gc_basic_clause_elim:                   0
% 1.43/1.02  forced_gc_time:                         0
% 1.43/1.02  parsing_time:                           0.015
% 1.43/1.02  unif_index_cands_time:                  0.
% 1.43/1.02  unif_index_add_time:                    0.
% 1.43/1.02  orderings_time:                         0.
% 1.43/1.02  out_proof_time:                         0.01
% 1.43/1.02  total_time:                             0.236
% 1.43/1.02  num_of_symbols:                         52
% 1.43/1.02  num_of_terms:                           7296
% 1.43/1.02  
% 1.43/1.02  ------ Preprocessing
% 1.43/1.02  
% 1.43/1.02  num_of_splits:                          0
% 1.43/1.02  num_of_split_atoms:                     0
% 1.43/1.02  num_of_reused_defs:                     0
% 1.43/1.02  num_eq_ax_congr_red:                    5
% 1.43/1.02  num_of_sem_filtered_clauses:            1
% 1.43/1.02  num_of_subtypes:                        0
% 1.43/1.02  monotx_restored_types:                  0
% 1.43/1.02  sat_num_of_epr_types:                   0
% 1.43/1.02  sat_num_of_non_cyclic_types:            0
% 1.43/1.02  sat_guarded_non_collapsed_types:        0
% 1.43/1.02  num_pure_diseq_elim:                    0
% 1.43/1.02  simp_replaced_by:                       0
% 1.43/1.02  res_preprocessed:                       187
% 1.43/1.02  prep_upred:                             0
% 1.43/1.02  prep_unflattend:                        56
% 1.43/1.02  smt_new_axioms:                         0
% 1.43/1.02  pred_elim_cands:                        4
% 1.43/1.02  pred_elim:                              4
% 1.43/1.02  pred_elim_cl:                           -2
% 1.43/1.02  pred_elim_cycles:                       6
% 1.43/1.02  merged_defs:                            0
% 1.43/1.02  merged_defs_ncl:                        0
% 1.43/1.02  bin_hyper_res:                          0
% 1.43/1.02  prep_cycles:                            4
% 1.43/1.02  pred_elim_time:                         0.012
% 1.43/1.02  splitting_time:                         0.
% 1.43/1.02  sem_filter_time:                        0.
% 1.43/1.02  monotx_time:                            0.001
% 1.43/1.02  subtype_inf_time:                       0.
% 1.43/1.02  
% 1.43/1.02  ------ Problem properties
% 1.43/1.02  
% 1.43/1.02  clauses:                                40
% 1.43/1.02  conjectures:                            3
% 1.43/1.02  epr:                                    6
% 1.43/1.02  horn:                                   33
% 1.43/1.02  ground:                                 19
% 1.43/1.02  unary:                                  13
% 1.43/1.02  binary:                                 7
% 1.43/1.02  lits:                                   108
% 1.43/1.02  lits_eq:                                48
% 1.43/1.02  fd_pure:                                0
% 1.43/1.02  fd_pseudo:                              0
% 1.43/1.02  fd_cond:                                5
% 1.43/1.02  fd_pseudo_cond:                         1
% 1.43/1.02  ac_symbols:                             0
% 1.43/1.02  
% 1.43/1.02  ------ Propositional Solver
% 1.43/1.02  
% 1.43/1.02  prop_solver_calls:                      28
% 1.43/1.02  prop_fast_solver_calls:                 1354
% 1.43/1.02  smt_solver_calls:                       0
% 1.43/1.02  smt_fast_solver_calls:                  0
% 1.43/1.02  prop_num_of_clauses:                    2894
% 1.43/1.02  prop_preprocess_simplified:             9359
% 1.43/1.02  prop_fo_subsumed:                       35
% 1.43/1.02  prop_solver_time:                       0.
% 1.43/1.02  smt_solver_time:                        0.
% 1.43/1.02  smt_fast_solver_time:                   0.
% 1.43/1.02  prop_fast_solver_time:                  0.
% 1.43/1.02  prop_unsat_core_time:                   0.
% 1.43/1.02  
% 1.43/1.02  ------ QBF
% 1.43/1.02  
% 1.43/1.02  qbf_q_res:                              0
% 1.43/1.02  qbf_num_tautologies:                    0
% 1.43/1.02  qbf_prep_cycles:                        0
% 1.43/1.02  
% 1.43/1.02  ------ BMC1
% 1.43/1.02  
% 1.43/1.02  bmc1_current_bound:                     -1
% 1.43/1.02  bmc1_last_solved_bound:                 -1
% 1.43/1.02  bmc1_unsat_core_size:                   -1
% 1.43/1.02  bmc1_unsat_core_parents_size:           -1
% 1.43/1.02  bmc1_merge_next_fun:                    0
% 1.43/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.43/1.02  
% 1.43/1.02  ------ Instantiation
% 1.43/1.02  
% 1.43/1.02  inst_num_of_clauses:                    1093
% 1.43/1.02  inst_num_in_passive:                    597
% 1.43/1.02  inst_num_in_active:                     366
% 1.43/1.02  inst_num_in_unprocessed:                130
% 1.43/1.02  inst_num_of_loops:                      470
% 1.43/1.02  inst_num_of_learning_restarts:          0
% 1.43/1.02  inst_num_moves_active_passive:          102
% 1.43/1.02  inst_lit_activity:                      0
% 1.43/1.02  inst_lit_activity_moves:                0
% 1.43/1.02  inst_num_tautologies:                   0
% 1.43/1.02  inst_num_prop_implied:                  0
% 1.43/1.02  inst_num_existing_simplified:           0
% 1.43/1.02  inst_num_eq_res_simplified:             0
% 1.43/1.02  inst_num_child_elim:                    0
% 1.43/1.02  inst_num_of_dismatching_blockings:      120
% 1.43/1.02  inst_num_of_non_proper_insts:           820
% 1.43/1.02  inst_num_of_duplicates:                 0
% 1.43/1.02  inst_inst_num_from_inst_to_res:         0
% 1.43/1.02  inst_dismatching_checking_time:         0.
% 1.43/1.02  
% 1.43/1.02  ------ Resolution
% 1.43/1.02  
% 1.43/1.02  res_num_of_clauses:                     0
% 1.43/1.02  res_num_in_passive:                     0
% 1.43/1.02  res_num_in_active:                      0
% 1.43/1.02  res_num_of_loops:                       191
% 1.43/1.02  res_forward_subset_subsumed:            49
% 1.43/1.02  res_backward_subset_subsumed:           2
% 1.43/1.02  res_forward_subsumed:                   0
% 1.43/1.02  res_backward_subsumed:                  0
% 1.43/1.02  res_forward_subsumption_resolution:     6
% 1.43/1.02  res_backward_subsumption_resolution:    0
% 1.43/1.02  res_clause_to_clause_subsumption:       289
% 1.43/1.02  res_orphan_elimination:                 0
% 1.43/1.02  res_tautology_del:                      73
% 1.43/1.02  res_num_eq_res_simplified:              0
% 1.43/1.02  res_num_sel_changes:                    0
% 1.43/1.02  res_moves_from_active_to_pass:          0
% 1.43/1.02  
% 1.43/1.02  ------ Superposition
% 1.43/1.02  
% 1.43/1.02  sup_time_total:                         0.
% 1.43/1.02  sup_time_generating:                    0.
% 1.43/1.02  sup_time_sim_full:                      0.
% 1.43/1.02  sup_time_sim_immed:                     0.
% 1.43/1.02  
% 1.43/1.02  sup_num_of_clauses:                     63
% 1.43/1.02  sup_num_in_active:                      35
% 1.43/1.02  sup_num_in_passive:                     28
% 1.43/1.02  sup_num_of_loops:                       92
% 1.43/1.02  sup_fw_superposition:                   51
% 1.43/1.02  sup_bw_superposition:                   56
% 1.43/1.02  sup_immediate_simplified:               67
% 1.43/1.02  sup_given_eliminated:                   2
% 1.43/1.02  comparisons_done:                       0
% 1.43/1.02  comparisons_avoided:                    8
% 1.43/1.02  
% 1.43/1.02  ------ Simplifications
% 1.43/1.02  
% 1.43/1.02  
% 1.43/1.02  sim_fw_subset_subsumed:                 15
% 1.43/1.02  sim_bw_subset_subsumed:                 15
% 1.43/1.02  sim_fw_subsumed:                        5
% 1.43/1.02  sim_bw_subsumed:                        1
% 1.43/1.02  sim_fw_subsumption_res:                 2
% 1.43/1.02  sim_bw_subsumption_res:                 0
% 1.43/1.02  sim_tautology_del:                      7
% 1.43/1.02  sim_eq_tautology_del:                   19
% 1.43/1.02  sim_eq_res_simp:                        3
% 1.43/1.02  sim_fw_demodulated:                     20
% 1.43/1.02  sim_bw_demodulated:                     58
% 1.43/1.02  sim_light_normalised:                   48
% 1.43/1.02  sim_joinable_taut:                      0
% 1.43/1.02  sim_joinable_simp:                      0
% 1.43/1.02  sim_ac_normalised:                      0
% 1.43/1.02  sim_smt_subsumption:                    0
% 1.43/1.02  
%------------------------------------------------------------------------------

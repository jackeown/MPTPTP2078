%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:49 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  206 (11886 expanded)
%              Number of clauses        :  136 (4755 expanded)
%              Number of leaves         :   16 (2129 expanded)
%              Depth                    :   32
%              Number of atoms          :  601 (53820 expanded)
%              Number of equality atoms :  301 (10626 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f12])).

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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f30])).

fof(f39,plain,
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

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f39])).

fof(f70,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f56,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f45])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_618,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_620,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_31])).

cnf(c_1604,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1607,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3063,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1604,c_1607])).

cnf(c_3239,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_620,c_3063])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1611,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2359,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1604,c_1611])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_234,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_235,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_234])).

cnf(c_292,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_235])).

cnf(c_1602,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_4848,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2359,c_1602])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1966,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2226,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1966])).

cnf(c_2227,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2226])).

cnf(c_1934,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_2456,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_2458,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2456])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2566,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2567,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2566])).

cnf(c_4867,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4848,c_36,c_2227,c_2458,c_2567])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_407,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_408,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_410,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_33])).

cnf(c_1600,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_4872,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4867,c_1600])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1606,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2579,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1604,c_1606])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2591,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2579,c_29])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_393,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_30])).

cnf(c_394,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_396,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_33])).

cnf(c_1601,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_2679,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2591,c_1601])).

cnf(c_2682,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2679,c_36,c_2227,c_2458,c_2567])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1605,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3629,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_1605])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1858,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1859,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1858])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1861,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1862,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1861])).

cnf(c_4058,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3629,c_34,c_36,c_1859,c_1862,c_2227,c_2458,c_2567])).

cnf(c_4063,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4058,c_1611])).

cnf(c_5006,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4872,c_4063])).

cnf(c_6818,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3239,c_5006])).

cnf(c_1612,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4064,plain,
    ( k1_relset_1(sK1,k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4058,c_1607])).

cnf(c_4072,plain,
    ( k1_relset_1(sK1,k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4064,c_2682])).

cnf(c_5008,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4872,c_4072])).

cnf(c_5954,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3239,c_5008])).

cnf(c_22,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_602,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_1591,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_6103,plain,
    ( sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5954,c_1591])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_628,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK1
    | k2_funct_1(sK2) != X0
    | k2_relat_1(X0) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_629,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_1590,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_2685,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2682,c_1590])).

cnf(c_2765,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2685])).

cnf(c_962,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2026,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_2767,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2765,c_34,c_36,c_1859,c_1862,c_2026,c_2227,c_2458,c_2567,c_2685])).

cnf(c_5010,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4872,c_2767])).

cnf(c_6106,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6103,c_3239,c_5010])).

cnf(c_6107,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6106])).

cnf(c_6112,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_6107])).

cnf(c_6926,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6818,c_6112])).

cnf(c_6929,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6926,c_5006])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_7043,plain,
    ( r1_tarski(k2_funct_1(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6929,c_4])).

cnf(c_3065,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1607])).

cnf(c_3167,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_3065])).

cnf(c_7578,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_7043,c_3167])).

cnf(c_6946,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6926,c_2682])).

cnf(c_7592,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7578,c_6946])).

cnf(c_6956,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6926,c_1604])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_6961,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6956,c_3])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_10])).

cnf(c_1599,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_3037,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1599])).

cnf(c_7321,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6961,c_3037])).

cnf(c_6947,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6926,c_2591])).

cnf(c_7338,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7321,c_6947])).

cnf(c_7890,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7338,c_36,c_2227,c_2458,c_2567])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1614,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3723,plain,
    ( k2_zfmisc_1(sK0,sK1) = sK2
    | r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2359,c_1614])).

cnf(c_6940,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) = sK2
    | r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6926,c_3723])).

cnf(c_7022,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6940,c_3])).

cnf(c_7898,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7890,c_7022])).

cnf(c_8641,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7592,c_7898])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_546,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_1594,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_1773,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1594,c_4])).

cnf(c_6951,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6926,c_1773])).

cnf(c_6987,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6951])).

cnf(c_6992,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6987,c_4])).

cnf(c_7132,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6946,c_1605])).

cnf(c_7136,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7132,c_4872])).

cnf(c_7137,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7136,c_4])).

cnf(c_8182,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6992,c_34,c_36,c_1859,c_1862,c_2227,c_2458,c_2567,c_7137])).

cnf(c_8184,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8182,c_7898])).

cnf(c_8643,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8641,c_8184])).

cnf(c_102,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_101,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8643,c_102,c_101])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.45/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
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
% 3.45/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/1.00  ------ Proving...
% 3.45/1.00  ------ Problem Properties 
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  clauses                                 31
% 3.45/1.00  conjectures                             3
% 3.45/1.00  EPR                                     4
% 3.45/1.00  Horn                                    26
% 3.45/1.00  unary                                   7
% 3.45/1.00  binary                                  7
% 3.45/1.00  lits                                    88
% 3.45/1.00  lits eq                                 36
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
% 3.45/1.01  --bmc1_symbol_reachability              true
% 3.45/1.01  --bmc1_property_lemmas                  false
% 3.45/1.01  --bmc1_k_induction                      false
% 3.45/1.01  --bmc1_non_equiv_states                 false
% 3.45/1.01  --bmc1_deadlock                         false
% 3.45/1.01  --bmc1_ucm                              false
% 3.45/1.01  --bmc1_add_unsat_core                   none
% 3.45/1.01  --bmc1_unsat_core_children              false
% 3.45/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/1.01  --bmc1_out_stat                         full
% 3.45/1.01  --bmc1_ground_init                      false
% 3.45/1.01  --bmc1_pre_inst_next_state              false
% 3.45/1.01  --bmc1_pre_inst_state                   false
% 3.45/1.01  --bmc1_pre_inst_reach_state             false
% 3.45/1.01  --bmc1_out_unsat_core                   false
% 3.45/1.01  --bmc1_aig_witness_out                  false
% 3.45/1.01  --bmc1_verbose                          false
% 3.45/1.01  --bmc1_dump_clauses_tptp                false
% 3.45/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.45/1.01  --bmc1_dump_file                        -
% 3.45/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.45/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.45/1.01  --bmc1_ucm_extend_mode                  1
% 3.45/1.01  --bmc1_ucm_init_mode                    2
% 3.45/1.01  --bmc1_ucm_cone_mode                    none
% 3.45/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.45/1.01  --bmc1_ucm_relax_model                  4
% 3.45/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.45/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/1.01  --bmc1_ucm_layered_model                none
% 3.45/1.01  --bmc1_ucm_max_lemma_size               10
% 3.45/1.01  
% 3.45/1.01  ------ AIG Options
% 3.45/1.01  
% 3.45/1.01  --aig_mode                              false
% 3.45/1.01  
% 3.45/1.01  ------ Instantiation Options
% 3.45/1.01  
% 3.45/1.01  --instantiation_flag                    true
% 3.45/1.01  --inst_sos_flag                         false
% 3.45/1.01  --inst_sos_phase                        true
% 3.45/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/1.01  --inst_lit_sel_side                     none
% 3.45/1.01  --inst_solver_per_active                1400
% 3.45/1.01  --inst_solver_calls_frac                1.
% 3.45/1.01  --inst_passive_queue_type               priority_queues
% 3.45/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/1.01  --inst_passive_queues_freq              [25;2]
% 3.45/1.01  --inst_dismatching                      true
% 3.45/1.01  --inst_eager_unprocessed_to_passive     true
% 3.45/1.01  --inst_prop_sim_given                   true
% 3.45/1.01  --inst_prop_sim_new                     false
% 3.45/1.01  --inst_subs_new                         false
% 3.45/1.01  --inst_eq_res_simp                      false
% 3.45/1.01  --inst_subs_given                       false
% 3.45/1.01  --inst_orphan_elimination               true
% 3.45/1.01  --inst_learning_loop_flag               true
% 3.45/1.01  --inst_learning_start                   3000
% 3.45/1.01  --inst_learning_factor                  2
% 3.45/1.01  --inst_start_prop_sim_after_learn       3
% 3.45/1.01  --inst_sel_renew                        solver
% 3.45/1.01  --inst_lit_activity_flag                true
% 3.45/1.01  --inst_restr_to_given                   false
% 3.45/1.01  --inst_activity_threshold               500
% 3.45/1.01  --inst_out_proof                        true
% 3.45/1.01  
% 3.45/1.01  ------ Resolution Options
% 3.45/1.01  
% 3.45/1.01  --resolution_flag                       false
% 3.45/1.01  --res_lit_sel                           adaptive
% 3.45/1.01  --res_lit_sel_side                      none
% 3.45/1.01  --res_ordering                          kbo
% 3.45/1.01  --res_to_prop_solver                    active
% 3.45/1.01  --res_prop_simpl_new                    false
% 3.45/1.01  --res_prop_simpl_given                  true
% 3.45/1.01  --res_passive_queue_type                priority_queues
% 3.45/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/1.01  --res_passive_queues_freq               [15;5]
% 3.45/1.01  --res_forward_subs                      full
% 3.45/1.01  --res_backward_subs                     full
% 3.45/1.01  --res_forward_subs_resolution           true
% 3.45/1.01  --res_backward_subs_resolution          true
% 3.45/1.01  --res_orphan_elimination                true
% 3.45/1.01  --res_time_limit                        2.
% 3.45/1.01  --res_out_proof                         true
% 3.45/1.01  
% 3.45/1.01  ------ Superposition Options
% 3.45/1.01  
% 3.45/1.01  --superposition_flag                    true
% 3.45/1.01  --sup_passive_queue_type                priority_queues
% 3.45/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.45/1.01  --demod_completeness_check              fast
% 3.45/1.01  --demod_use_ground                      true
% 3.45/1.01  --sup_to_prop_solver                    passive
% 3.45/1.01  --sup_prop_simpl_new                    true
% 3.45/1.01  --sup_prop_simpl_given                  true
% 3.45/1.01  --sup_fun_splitting                     false
% 3.45/1.01  --sup_smt_interval                      50000
% 3.45/1.01  
% 3.45/1.01  ------ Superposition Simplification Setup
% 3.45/1.01  
% 3.45/1.01  --sup_indices_passive                   []
% 3.45/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.01  --sup_full_bw                           [BwDemod]
% 3.45/1.01  --sup_immed_triv                        [TrivRules]
% 3.45/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.01  --sup_immed_bw_main                     []
% 3.45/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/1.01  
% 3.45/1.01  ------ Combination Options
% 3.45/1.01  
% 3.45/1.01  --comb_res_mult                         3
% 3.45/1.01  --comb_sup_mult                         2
% 3.45/1.01  --comb_inst_mult                        10
% 3.45/1.01  
% 3.45/1.01  ------ Debug Options
% 3.45/1.01  
% 3.45/1.01  --dbg_backtrace                         false
% 3.45/1.01  --dbg_dump_prop_clauses                 false
% 3.45/1.01  --dbg_dump_prop_clauses_file            -
% 3.45/1.01  --dbg_out_stat                          false
% 3.45/1.01  
% 3.45/1.01  
% 3.45/1.01  
% 3.45/1.01  
% 3.45/1.01  ------ Proving...
% 3.45/1.01  
% 3.45/1.01  
% 3.45/1.01  % SZS status Theorem for theBenchmark.p
% 3.45/1.01  
% 3.45/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/1.01  
% 3.45/1.01  fof(f12,axiom,(
% 3.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f26,plain,(
% 3.45/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.01    inference(ennf_transformation,[],[f12])).
% 3.45/1.01  
% 3.45/1.01  fof(f27,plain,(
% 3.45/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.01    inference(flattening,[],[f26])).
% 3.45/1.01  
% 3.45/1.01  fof(f38,plain,(
% 3.45/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.01    inference(nnf_transformation,[],[f27])).
% 3.45/1.01  
% 3.45/1.01  fof(f60,plain,(
% 3.45/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.01    inference(cnf_transformation,[],[f38])).
% 3.45/1.01  
% 3.45/1.01  fof(f14,conjecture,(
% 3.45/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f15,negated_conjecture,(
% 3.45/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.45/1.01    inference(negated_conjecture,[],[f14])).
% 3.45/1.01  
% 3.45/1.01  fof(f30,plain,(
% 3.45/1.01    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.45/1.01    inference(ennf_transformation,[],[f15])).
% 3.45/1.01  
% 3.45/1.01  fof(f31,plain,(
% 3.45/1.01    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.45/1.01    inference(flattening,[],[f30])).
% 3.45/1.01  
% 3.45/1.01  fof(f39,plain,(
% 3.45/1.01    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.45/1.01    introduced(choice_axiom,[])).
% 3.45/1.01  
% 3.45/1.01  fof(f40,plain,(
% 3.45/1.01    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.45/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f39])).
% 3.45/1.01  
% 3.45/1.01  fof(f70,plain,(
% 3.45/1.01    v1_funct_2(sK2,sK0,sK1)),
% 3.45/1.01    inference(cnf_transformation,[],[f40])).
% 3.45/1.01  
% 3.45/1.01  fof(f71,plain,(
% 3.45/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.45/1.01    inference(cnf_transformation,[],[f40])).
% 3.45/1.01  
% 3.45/1.01  fof(f10,axiom,(
% 3.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f24,plain,(
% 3.45/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.01    inference(ennf_transformation,[],[f10])).
% 3.45/1.01  
% 3.45/1.01  fof(f58,plain,(
% 3.45/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.01    inference(cnf_transformation,[],[f24])).
% 3.45/1.01  
% 3.45/1.01  fof(f3,axiom,(
% 3.45/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f36,plain,(
% 3.45/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.45/1.01    inference(nnf_transformation,[],[f3])).
% 3.45/1.01  
% 3.45/1.01  fof(f47,plain,(
% 3.45/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.45/1.01    inference(cnf_transformation,[],[f36])).
% 3.45/1.01  
% 3.45/1.01  fof(f4,axiom,(
% 3.45/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f17,plain,(
% 3.45/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.45/1.01    inference(ennf_transformation,[],[f4])).
% 3.45/1.01  
% 3.45/1.01  fof(f49,plain,(
% 3.45/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.45/1.01    inference(cnf_transformation,[],[f17])).
% 3.45/1.01  
% 3.45/1.01  fof(f48,plain,(
% 3.45/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.45/1.01    inference(cnf_transformation,[],[f36])).
% 3.45/1.01  
% 3.45/1.01  fof(f6,axiom,(
% 3.45/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f52,plain,(
% 3.45/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.45/1.01    inference(cnf_transformation,[],[f6])).
% 3.45/1.01  
% 3.45/1.01  fof(f8,axiom,(
% 3.45/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f21,plain,(
% 3.45/1.01    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.45/1.01    inference(ennf_transformation,[],[f8])).
% 3.45/1.01  
% 3.45/1.01  fof(f22,plain,(
% 3.45/1.01    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/1.01    inference(flattening,[],[f21])).
% 3.45/1.01  
% 3.45/1.01  fof(f56,plain,(
% 3.45/1.01    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/1.01    inference(cnf_transformation,[],[f22])).
% 3.45/1.01  
% 3.45/1.01  fof(f72,plain,(
% 3.45/1.01    v2_funct_1(sK2)),
% 3.45/1.01    inference(cnf_transformation,[],[f40])).
% 3.45/1.01  
% 3.45/1.01  fof(f69,plain,(
% 3.45/1.01    v1_funct_1(sK2)),
% 3.45/1.01    inference(cnf_transformation,[],[f40])).
% 3.45/1.01  
% 3.45/1.01  fof(f11,axiom,(
% 3.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f25,plain,(
% 3.45/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.01    inference(ennf_transformation,[],[f11])).
% 3.45/1.01  
% 3.45/1.01  fof(f59,plain,(
% 3.45/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.01    inference(cnf_transformation,[],[f25])).
% 3.45/1.01  
% 3.45/1.01  fof(f73,plain,(
% 3.45/1.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.45/1.01    inference(cnf_transformation,[],[f40])).
% 3.45/1.01  
% 3.45/1.01  fof(f55,plain,(
% 3.45/1.01    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/1.01    inference(cnf_transformation,[],[f22])).
% 3.45/1.01  
% 3.45/1.01  fof(f13,axiom,(
% 3.45/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f28,plain,(
% 3.45/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.45/1.01    inference(ennf_transformation,[],[f13])).
% 3.45/1.01  
% 3.45/1.01  fof(f29,plain,(
% 3.45/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/1.01    inference(flattening,[],[f28])).
% 3.45/1.01  
% 3.45/1.01  fof(f68,plain,(
% 3.45/1.01    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/1.01    inference(cnf_transformation,[],[f29])).
% 3.45/1.01  
% 3.45/1.01  fof(f7,axiom,(
% 3.45/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f19,plain,(
% 3.45/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.45/1.01    inference(ennf_transformation,[],[f7])).
% 3.45/1.01  
% 3.45/1.01  fof(f20,plain,(
% 3.45/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/1.01    inference(flattening,[],[f19])).
% 3.45/1.01  
% 3.45/1.01  fof(f54,plain,(
% 3.45/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/1.01    inference(cnf_transformation,[],[f20])).
% 3.45/1.01  
% 3.45/1.01  fof(f53,plain,(
% 3.45/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/1.01    inference(cnf_transformation,[],[f20])).
% 3.45/1.01  
% 3.45/1.01  fof(f62,plain,(
% 3.45/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.01    inference(cnf_transformation,[],[f38])).
% 3.45/1.01  
% 3.45/1.01  fof(f74,plain,(
% 3.45/1.01    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.45/1.01    inference(cnf_transformation,[],[f40])).
% 3.45/1.01  
% 3.45/1.01  fof(f67,plain,(
% 3.45/1.01    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/1.01    inference(cnf_transformation,[],[f29])).
% 3.45/1.01  
% 3.45/1.01  fof(f2,axiom,(
% 3.45/1.01    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f34,plain,(
% 3.45/1.01    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.45/1.01    inference(nnf_transformation,[],[f2])).
% 3.45/1.01  
% 3.45/1.01  fof(f35,plain,(
% 3.45/1.01    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.45/1.01    inference(flattening,[],[f34])).
% 3.45/1.01  
% 3.45/1.01  fof(f45,plain,(
% 3.45/1.01    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.45/1.01    inference(cnf_transformation,[],[f35])).
% 3.45/1.01  
% 3.45/1.01  fof(f78,plain,(
% 3.45/1.01    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.45/1.01    inference(equality_resolution,[],[f45])).
% 3.45/1.01  
% 3.45/1.01  fof(f46,plain,(
% 3.45/1.01    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.45/1.01    inference(cnf_transformation,[],[f35])).
% 3.45/1.01  
% 3.45/1.01  fof(f77,plain,(
% 3.45/1.01    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.45/1.01    inference(equality_resolution,[],[f46])).
% 3.45/1.01  
% 3.45/1.01  fof(f9,axiom,(
% 3.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f16,plain,(
% 3.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.45/1.01    inference(pure_predicate_removal,[],[f9])).
% 3.45/1.01  
% 3.45/1.01  fof(f23,plain,(
% 3.45/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.01    inference(ennf_transformation,[],[f16])).
% 3.45/1.01  
% 3.45/1.01  fof(f57,plain,(
% 3.45/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.01    inference(cnf_transformation,[],[f23])).
% 3.45/1.01  
% 3.45/1.01  fof(f5,axiom,(
% 3.45/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f18,plain,(
% 3.45/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.45/1.01    inference(ennf_transformation,[],[f5])).
% 3.45/1.01  
% 3.45/1.01  fof(f37,plain,(
% 3.45/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.45/1.01    inference(nnf_transformation,[],[f18])).
% 3.45/1.01  
% 3.45/1.01  fof(f50,plain,(
% 3.45/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.45/1.01    inference(cnf_transformation,[],[f37])).
% 3.45/1.01  
% 3.45/1.01  fof(f1,axiom,(
% 3.45/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/1.01  
% 3.45/1.01  fof(f32,plain,(
% 3.45/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/1.01    inference(nnf_transformation,[],[f1])).
% 3.45/1.01  
% 3.45/1.01  fof(f33,plain,(
% 3.45/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/1.01    inference(flattening,[],[f32])).
% 3.45/1.01  
% 3.45/1.01  fof(f43,plain,(
% 3.45/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.45/1.01    inference(cnf_transformation,[],[f33])).
% 3.45/1.01  
% 3.45/1.01  fof(f63,plain,(
% 3.45/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.01    inference(cnf_transformation,[],[f38])).
% 3.45/1.01  
% 3.45/1.01  fof(f82,plain,(
% 3.45/1.01    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.45/1.01    inference(equality_resolution,[],[f63])).
% 3.45/1.01  
% 3.45/1.01  fof(f44,plain,(
% 3.45/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 3.45/1.01    inference(cnf_transformation,[],[f35])).
% 3.45/1.01  
% 3.45/1.01  cnf(c_24,plain,
% 3.45/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.45/1.01      | k1_xboole_0 = X2 ),
% 3.45/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_32,negated_conjecture,
% 3.45/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.45/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_617,plain,
% 3.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.45/1.01      | sK0 != X1
% 3.45/1.01      | sK1 != X2
% 3.45/1.01      | sK2 != X0
% 3.45/1.01      | k1_xboole_0 = X2 ),
% 3.45/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_618,plain,
% 3.45/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.45/1.01      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.45/1.01      | k1_xboole_0 = sK1 ),
% 3.45/1.01      inference(unflattening,[status(thm)],[c_617]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_31,negated_conjecture,
% 3.45/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.45/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_620,plain,
% 3.45/1.01      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_618,c_31]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1604,plain,
% 3.45/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_17,plain,
% 3.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.45/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1607,plain,
% 3.45/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.45/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_3063,plain,
% 3.45/1.01      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_1604,c_1607]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_3239,plain,
% 3.45/1.01      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_620,c_3063]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7,plain,
% 3.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.45/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1611,plain,
% 3.45/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.45/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2359,plain,
% 3.45/1.01      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_1604,c_1611]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_8,plain,
% 3.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.45/1.01      | ~ v1_relat_1(X1)
% 3.45/1.01      | v1_relat_1(X0) ),
% 3.45/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6,plain,
% 3.45/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.45/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_234,plain,
% 3.45/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.45/1.01      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_235,plain,
% 3.45/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.45/1.01      inference(renaming,[status(thm)],[c_234]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_292,plain,
% 3.45/1.01      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.45/1.01      inference(bin_hyper_res,[status(thm)],[c_8,c_235]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1602,plain,
% 3.45/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.45/1.01      | v1_relat_1(X1) != iProver_top
% 3.45/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_4848,plain,
% 3.45/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.45/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_2359,c_1602]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_36,plain,
% 3.45/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1966,plain,
% 3.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.01      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2226,plain,
% 3.45/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.45/1.01      | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_1966]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2227,plain,
% 3.45/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.45/1.01      | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_2226]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1934,plain,
% 3.45/1.01      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.45/1.01      | v1_relat_1(X0)
% 3.45/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_292]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2456,plain,
% 3.45/1.01      ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
% 3.45/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.45/1.01      | v1_relat_1(sK2) ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_1934]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2458,plain,
% 3.45/1.01      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.45/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.45/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_2456]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_11,plain,
% 3.45/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.45/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2566,plain,
% 3.45/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2567,plain,
% 3.45/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_2566]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_4867,plain,
% 3.45/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_4848,c_36,c_2227,c_2458,c_2567]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_14,plain,
% 3.45/1.01      ( ~ v2_funct_1(X0)
% 3.45/1.01      | ~ v1_funct_1(X0)
% 3.45/1.01      | ~ v1_relat_1(X0)
% 3.45/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.45/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_30,negated_conjecture,
% 3.45/1.01      ( v2_funct_1(sK2) ),
% 3.45/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_407,plain,
% 3.45/1.01      ( ~ v1_funct_1(X0)
% 3.45/1.01      | ~ v1_relat_1(X0)
% 3.45/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.45/1.01      | sK2 != X0 ),
% 3.45/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_408,plain,
% 3.45/1.01      ( ~ v1_funct_1(sK2)
% 3.45/1.01      | ~ v1_relat_1(sK2)
% 3.45/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.45/1.01      inference(unflattening,[status(thm)],[c_407]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_33,negated_conjecture,
% 3.45/1.01      ( v1_funct_1(sK2) ),
% 3.45/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_410,plain,
% 3.45/1.01      ( ~ v1_relat_1(sK2)
% 3.45/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_408,c_33]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1600,plain,
% 3.45/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.45/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_4872,plain,
% 3.45/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_4867,c_1600]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_18,plain,
% 3.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.45/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1606,plain,
% 3.45/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.45/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2579,plain,
% 3.45/1.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_1604,c_1606]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_29,negated_conjecture,
% 3.45/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.45/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2591,plain,
% 3.45/1.01      ( k2_relat_1(sK2) = sK1 ),
% 3.45/1.01      inference(light_normalisation,[status(thm)],[c_2579,c_29]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_15,plain,
% 3.45/1.01      ( ~ v2_funct_1(X0)
% 3.45/1.01      | ~ v1_funct_1(X0)
% 3.45/1.01      | ~ v1_relat_1(X0)
% 3.45/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.45/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_393,plain,
% 3.45/1.01      ( ~ v1_funct_1(X0)
% 3.45/1.01      | ~ v1_relat_1(X0)
% 3.45/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.45/1.01      | sK2 != X0 ),
% 3.45/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_30]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_394,plain,
% 3.45/1.01      ( ~ v1_funct_1(sK2)
% 3.45/1.01      | ~ v1_relat_1(sK2)
% 3.45/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.45/1.01      inference(unflattening,[status(thm)],[c_393]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_396,plain,
% 3.45/1.01      ( ~ v1_relat_1(sK2)
% 3.45/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_394,c_33]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1601,plain,
% 3.45/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.45/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2679,plain,
% 3.45/1.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.45/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_2591,c_1601]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2682,plain,
% 3.45/1.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_2679,c_36,c_2227,c_2458,c_2567]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_25,plain,
% 3.45/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.45/1.01      | ~ v1_funct_1(X0)
% 3.45/1.01      | ~ v1_relat_1(X0) ),
% 3.45/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1605,plain,
% 3.45/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.45/1.01      | v1_funct_1(X0) != iProver_top
% 3.45/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_3629,plain,
% 3.45/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.45/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_2682,c_1605]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_34,plain,
% 3.45/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_12,plain,
% 3.45/1.01      ( ~ v1_funct_1(X0)
% 3.45/1.01      | v1_funct_1(k2_funct_1(X0))
% 3.45/1.01      | ~ v1_relat_1(X0) ),
% 3.45/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1858,plain,
% 3.45/1.01      ( v1_funct_1(k2_funct_1(sK2))
% 3.45/1.01      | ~ v1_funct_1(sK2)
% 3.45/1.01      | ~ v1_relat_1(sK2) ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1859,plain,
% 3.45/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.45/1.01      | v1_funct_1(sK2) != iProver_top
% 3.45/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_1858]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_13,plain,
% 3.45/1.01      ( ~ v1_funct_1(X0)
% 3.45/1.01      | ~ v1_relat_1(X0)
% 3.45/1.01      | v1_relat_1(k2_funct_1(X0)) ),
% 3.45/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1861,plain,
% 3.45/1.01      ( ~ v1_funct_1(sK2)
% 3.45/1.01      | v1_relat_1(k2_funct_1(sK2))
% 3.45/1.01      | ~ v1_relat_1(sK2) ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1862,plain,
% 3.45/1.01      ( v1_funct_1(sK2) != iProver_top
% 3.45/1.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.45/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_1861]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_4058,plain,
% 3.45/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_3629,c_34,c_36,c_1859,c_1862,c_2227,c_2458,c_2567]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_4063,plain,
% 3.45/1.01      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))) = iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_4058,c_1611]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_5006,plain,
% 3.45/1.01      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_4872,c_4063]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6818,plain,
% 3.45/1.01      ( sK1 = k1_xboole_0
% 3.45/1.01      | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_3239,c_5006]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1612,plain,
% 3.45/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.45/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_4064,plain,
% 3.45/1.01      ( k1_relset_1(sK1,k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_4058,c_1607]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_4072,plain,
% 3.45/1.01      ( k1_relset_1(sK1,k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = sK1 ),
% 3.45/1.01      inference(light_normalisation,[status(thm)],[c_4064,c_2682]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_5008,plain,
% 3.45/1.01      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_4872,c_4072]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_5954,plain,
% 3.45/1.01      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1 | sK1 = k1_xboole_0 ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_3239,c_5008]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_22,plain,
% 3.45/1.01      ( v1_funct_2(X0,X1,X2)
% 3.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.01      | k1_relset_1(X1,X2,X0) != X1
% 3.45/1.01      | k1_xboole_0 = X2 ),
% 3.45/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_28,negated_conjecture,
% 3.45/1.01      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.45/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.45/1.01      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.45/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_601,plain,
% 3.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.45/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.45/1.01      | k1_relset_1(X1,X2,X0) != X1
% 3.45/1.01      | k2_funct_1(sK2) != X0
% 3.45/1.01      | sK0 != X2
% 3.45/1.01      | sK1 != X1
% 3.45/1.01      | k1_xboole_0 = X2 ),
% 3.45/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_602,plain,
% 3.45/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.45/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.45/1.01      | k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 3.45/1.01      | k1_xboole_0 = sK0 ),
% 3.45/1.01      inference(unflattening,[status(thm)],[c_601]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1591,plain,
% 3.45/1.01      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
% 3.45/1.01      | k1_xboole_0 = sK0
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6103,plain,
% 3.45/1.01      ( sK0 = k1_xboole_0
% 3.45/1.01      | sK1 = k1_xboole_0
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_5954,c_1591]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_26,plain,
% 3.45/1.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.45/1.01      | ~ v1_funct_1(X0)
% 3.45/1.01      | ~ v1_relat_1(X0) ),
% 3.45/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_628,plain,
% 3.45/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.45/1.01      | ~ v1_funct_1(X0)
% 3.45/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.45/1.01      | ~ v1_relat_1(X0)
% 3.45/1.01      | k1_relat_1(X0) != sK1
% 3.45/1.01      | k2_funct_1(sK2) != X0
% 3.45/1.01      | k2_relat_1(X0) != sK0 ),
% 3.45/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_28]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_629,plain,
% 3.45/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.45/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.45/1.01      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.45/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.45/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.45/1.01      inference(unflattening,[status(thm)],[c_628]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1590,plain,
% 3.45/1.01      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.45/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.45/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2685,plain,
% 3.45/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.45/1.01      | sK1 != sK1
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.45/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_2682,c_1590]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2765,plain,
% 3.45/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.45/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(equality_resolution_simp,[status(thm)],[c_2685]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_962,plain,( X0 = X0 ),theory(equality) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2026,plain,
% 3.45/1.01      ( sK1 = sK1 ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_962]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_2767,plain,
% 3.45/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_2765,c_34,c_36,c_1859,c_1862,c_2026,c_2227,c_2458,
% 3.45/1.01                 c_2567,c_2685]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_5010,plain,
% 3.45/1.01      ( k1_relat_1(sK2) != sK0
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_4872,c_2767]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6106,plain,
% 3.45/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.45/1.01      | sK1 = k1_xboole_0 ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_6103,c_3239,c_5010]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6107,plain,
% 3.45/1.01      ( sK1 = k1_xboole_0
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.45/1.01      inference(renaming,[status(thm)],[c_6106]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6112,plain,
% 3.45/1.01      ( sK1 = k1_xboole_0
% 3.45/1.01      | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_1612,c_6107]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6926,plain,
% 3.45/1.01      ( sK1 = k1_xboole_0 ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_6818,c_6112]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6929,plain,
% 3.45/1.01      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))) = iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_6926,c_5006]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_4,plain,
% 3.45/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.45/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7043,plain,
% 3.45/1.01      ( r1_tarski(k2_funct_1(sK2),k1_xboole_0) = iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_6929,c_4]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_3065,plain,
% 3.45/1.01      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.45/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_4,c_1607]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_3167,plain,
% 3.45/1.01      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.45/1.01      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_1612,c_3065]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7578,plain,
% 3.45/1.01      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_7043,c_3167]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6946,plain,
% 3.45/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_6926,c_2682]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7592,plain,
% 3.45/1.01      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0 ),
% 3.45/1.01      inference(light_normalisation,[status(thm)],[c_7578,c_6946]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6956,plain,
% 3.45/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_6926,c_1604]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_3,plain,
% 3.45/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.45/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6961,plain,
% 3.45/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_6956,c_3]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_16,plain,
% 3.45/1.01      ( v5_relat_1(X0,X1)
% 3.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.45/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_10,plain,
% 3.45/1.01      ( ~ v5_relat_1(X0,X1)
% 3.45/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 3.45/1.01      | ~ v1_relat_1(X0) ),
% 3.45/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_427,plain,
% 3.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 3.45/1.01      | ~ v1_relat_1(X0) ),
% 3.45/1.01      inference(resolution,[status(thm)],[c_16,c_10]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1599,plain,
% 3.45/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.45/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.45/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_3037,plain,
% 3.45/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.45/1.01      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.45/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_4,c_1599]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7321,plain,
% 3.45/1.01      ( r1_tarski(k2_relat_1(sK2),X0) = iProver_top
% 3.45/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_6961,c_3037]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6947,plain,
% 3.45/1.01      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_6926,c_2591]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7338,plain,
% 3.45/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top
% 3.45/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.45/1.01      inference(light_normalisation,[status(thm)],[c_7321,c_6947]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7890,plain,
% 3.45/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_7338,c_36,c_2227,c_2458,c_2567]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_0,plain,
% 3.45/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.45/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1614,plain,
% 3.45/1.01      ( X0 = X1
% 3.45/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.45/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_3723,plain,
% 3.45/1.01      ( k2_zfmisc_1(sK0,sK1) = sK2
% 3.45/1.01      | r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_2359,c_1614]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6940,plain,
% 3.45/1.01      ( k2_zfmisc_1(sK0,k1_xboole_0) = sK2
% 3.45/1.01      | r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) != iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_6926,c_3723]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7022,plain,
% 3.45/1.01      ( sK2 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_6940,c_3]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7898,plain,
% 3.45/1.01      ( sK2 = k1_xboole_0 ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_7890,c_7022]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_8641,plain,
% 3.45/1.01      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.45/1.01      inference(light_normalisation,[status(thm)],[c_7592,c_7898]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_21,plain,
% 3.45/1.01      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.45/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.45/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_545,plain,
% 3.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.45/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.45/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.45/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.45/1.01      | k2_funct_1(sK2) != X0
% 3.45/1.01      | sK0 != X1
% 3.45/1.01      | sK1 != k1_xboole_0 ),
% 3.45/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_546,plain,
% 3.45/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.45/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 3.45/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.45/1.01      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.45/1.01      | sK1 != k1_xboole_0 ),
% 3.45/1.01      inference(unflattening,[status(thm)],[c_545]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1594,plain,
% 3.45/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.45/1.01      | sK1 != k1_xboole_0
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_1773,plain,
% 3.45/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.45/1.01      | sK1 != k1_xboole_0
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_1594,c_4]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6951,plain,
% 3.45/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.45/1.01      | k1_xboole_0 != k1_xboole_0
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_6926,c_1773]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6987,plain,
% 3.45/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(equality_resolution_simp,[status(thm)],[c_6951]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_6992,plain,
% 3.45/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.45/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_6987,c_4]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7132,plain,
% 3.45/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.45/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(superposition,[status(thm)],[c_6946,c_1605]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7136,plain,
% 3.45/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.45/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(light_normalisation,[status(thm)],[c_7132,c_4872]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_7137,plain,
% 3.45/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.45/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.45/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_7136,c_4]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_8182,plain,
% 3.45/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.45/1.01      inference(global_propositional_subsumption,
% 3.45/1.01                [status(thm)],
% 3.45/1.01                [c_6992,c_34,c_36,c_1859,c_1862,c_2227,c_2458,c_2567,
% 3.45/1.01                 c_7137]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_8184,plain,
% 3.45/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.45/1.01      inference(light_normalisation,[status(thm)],[c_8182,c_7898]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_8643,plain,
% 3.45/1.01      ( k1_xboole_0 != k1_xboole_0 ),
% 3.45/1.01      inference(demodulation,[status(thm)],[c_8641,c_8184]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_102,plain,
% 3.45/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_5,plain,
% 3.45/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.45/1.01      | k1_xboole_0 = X1
% 3.45/1.01      | k1_xboole_0 = X0 ),
% 3.45/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(c_101,plain,
% 3.45/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.45/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.45/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.45/1.01  
% 3.45/1.01  cnf(contradiction,plain,
% 3.45/1.01      ( $false ),
% 3.45/1.01      inference(minisat,[status(thm)],[c_8643,c_102,c_101]) ).
% 3.45/1.01  
% 3.45/1.01  
% 3.45/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/1.01  
% 3.45/1.01  ------                               Statistics
% 3.45/1.01  
% 3.45/1.01  ------ General
% 3.45/1.01  
% 3.45/1.01  abstr_ref_over_cycles:                  0
% 3.45/1.01  abstr_ref_under_cycles:                 0
% 3.45/1.01  gc_basic_clause_elim:                   0
% 3.45/1.01  forced_gc_time:                         0
% 3.45/1.01  parsing_time:                           0.01
% 3.45/1.01  unif_index_cands_time:                  0.
% 3.45/1.01  unif_index_add_time:                    0.
% 3.45/1.01  orderings_time:                         0.
% 3.45/1.01  out_proof_time:                         0.012
% 3.45/1.01  total_time:                             0.289
% 3.45/1.01  num_of_symbols:                         49
% 3.45/1.01  num_of_terms:                           7289
% 3.45/1.01  
% 3.45/1.01  ------ Preprocessing
% 3.45/1.01  
% 3.45/1.01  num_of_splits:                          0
% 3.45/1.01  num_of_split_atoms:                     0
% 3.45/1.01  num_of_reused_defs:                     0
% 3.45/1.01  num_eq_ax_congr_red:                    7
% 3.45/1.01  num_of_sem_filtered_clauses:            1
% 3.45/1.01  num_of_subtypes:                        0
% 3.45/1.01  monotx_restored_types:                  0
% 3.45/1.01  sat_num_of_epr_types:                   0
% 3.45/1.01  sat_num_of_non_cyclic_types:            0
% 3.45/1.01  sat_guarded_non_collapsed_types:        0
% 3.45/1.01  num_pure_diseq_elim:                    0
% 3.45/1.01  simp_replaced_by:                       0
% 3.45/1.01  res_preprocessed:                       152
% 3.45/1.01  prep_upred:                             0
% 3.45/1.01  prep_unflattend:                        43
% 3.45/1.01  smt_new_axioms:                         0
% 3.45/1.01  pred_elim_cands:                        4
% 3.45/1.01  pred_elim:                              3
% 3.45/1.01  pred_elim_cl:                           1
% 3.45/1.01  pred_elim_cycles:                       5
% 3.45/1.01  merged_defs:                            8
% 3.45/1.01  merged_defs_ncl:                        0
% 3.45/1.01  bin_hyper_res:                          9
% 3.45/1.01  prep_cycles:                            4
% 3.45/1.01  pred_elim_time:                         0.008
% 3.45/1.01  splitting_time:                         0.
% 3.45/1.01  sem_filter_time:                        0.
% 3.45/1.01  monotx_time:                            0.
% 3.45/1.01  subtype_inf_time:                       0.
% 3.45/1.01  
% 3.45/1.01  ------ Problem properties
% 3.45/1.01  
% 3.45/1.01  clauses:                                31
% 3.45/1.01  conjectures:                            3
% 3.45/1.01  epr:                                    4
% 3.45/1.01  horn:                                   26
% 3.45/1.01  ground:                                 13
% 3.45/1.01  unary:                                  7
% 3.45/1.01  binary:                                 7
% 3.45/1.01  lits:                                   88
% 3.45/1.01  lits_eq:                                36
% 3.45/1.01  fd_pure:                                0
% 3.45/1.01  fd_pseudo:                              0
% 3.45/1.01  fd_cond:                                2
% 3.45/1.01  fd_pseudo_cond:                         1
% 3.45/1.01  ac_symbols:                             0
% 3.45/1.01  
% 3.45/1.01  ------ Propositional Solver
% 3.45/1.01  
% 3.45/1.01  prop_solver_calls:                      29
% 3.45/1.01  prop_fast_solver_calls:                 1196
% 3.45/1.01  smt_solver_calls:                       0
% 3.45/1.01  smt_fast_solver_calls:                  0
% 3.45/1.01  prop_num_of_clauses:                    2960
% 3.45/1.01  prop_preprocess_simplified:             8166
% 3.45/1.01  prop_fo_subsumed:                       34
% 3.45/1.01  prop_solver_time:                       0.
% 3.45/1.01  smt_solver_time:                        0.
% 3.45/1.01  smt_fast_solver_time:                   0.
% 3.45/1.01  prop_fast_solver_time:                  0.
% 3.45/1.01  prop_unsat_core_time:                   0.
% 3.45/1.01  
% 3.45/1.01  ------ QBF
% 3.45/1.01  
% 3.45/1.01  qbf_q_res:                              0
% 3.45/1.01  qbf_num_tautologies:                    0
% 3.45/1.01  qbf_prep_cycles:                        0
% 3.45/1.01  
% 3.45/1.01  ------ BMC1
% 3.45/1.01  
% 3.45/1.01  bmc1_current_bound:                     -1
% 3.45/1.01  bmc1_last_solved_bound:                 -1
% 3.45/1.01  bmc1_unsat_core_size:                   -1
% 3.45/1.01  bmc1_unsat_core_parents_size:           -1
% 3.45/1.01  bmc1_merge_next_fun:                    0
% 3.45/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.45/1.01  
% 3.45/1.01  ------ Instantiation
% 3.45/1.01  
% 3.45/1.01  inst_num_of_clauses:                    1001
% 3.45/1.01  inst_num_in_passive:                    243
% 3.45/1.01  inst_num_in_active:                     535
% 3.45/1.01  inst_num_in_unprocessed:                228
% 3.45/1.01  inst_num_of_loops:                      600
% 3.45/1.01  inst_num_of_learning_restarts:          0
% 3.45/1.01  inst_num_moves_active_passive:          62
% 3.45/1.01  inst_lit_activity:                      0
% 3.45/1.01  inst_lit_activity_moves:                0
% 3.45/1.01  inst_num_tautologies:                   0
% 3.45/1.01  inst_num_prop_implied:                  0
% 3.45/1.01  inst_num_existing_simplified:           0
% 3.45/1.01  inst_num_eq_res_simplified:             0
% 3.45/1.01  inst_num_child_elim:                    0
% 3.45/1.01  inst_num_of_dismatching_blockings:      441
% 3.45/1.01  inst_num_of_non_proper_insts:           1429
% 3.45/1.01  inst_num_of_duplicates:                 0
% 3.45/1.01  inst_inst_num_from_inst_to_res:         0
% 3.45/1.01  inst_dismatching_checking_time:         0.
% 3.45/1.01  
% 3.45/1.01  ------ Resolution
% 3.45/1.01  
% 3.45/1.01  res_num_of_clauses:                     0
% 3.45/1.01  res_num_in_passive:                     0
% 3.45/1.01  res_num_in_active:                      0
% 3.45/1.01  res_num_of_loops:                       156
% 3.45/1.01  res_forward_subset_subsumed:            69
% 3.45/1.01  res_backward_subset_subsumed:           12
% 3.45/1.01  res_forward_subsumed:                   0
% 3.45/1.01  res_backward_subsumed:                  0
% 3.45/1.01  res_forward_subsumption_resolution:     0
% 3.45/1.01  res_backward_subsumption_resolution:    0
% 3.45/1.01  res_clause_to_clause_subsumption:       406
% 3.45/1.01  res_orphan_elimination:                 0
% 3.45/1.01  res_tautology_del:                      127
% 3.45/1.01  res_num_eq_res_simplified:              0
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
% 3.45/1.01  sup_num_of_clauses:                     110
% 3.45/1.01  sup_num_in_active:                      53
% 3.45/1.01  sup_num_in_passive:                     57
% 3.45/1.01  sup_num_of_loops:                       118
% 3.45/1.01  sup_fw_superposition:                   83
% 3.45/1.01  sup_bw_superposition:                   122
% 3.45/1.01  sup_immediate_simplified:               90
% 3.45/1.01  sup_given_eliminated:                   0
% 3.45/1.01  comparisons_done:                       0
% 3.45/1.01  comparisons_avoided:                    13
% 3.45/1.01  
% 3.45/1.01  ------ Simplifications
% 3.45/1.01  
% 3.45/1.01  
% 3.45/1.01  sim_fw_subset_subsumed:                 22
% 3.45/1.01  sim_bw_subset_subsumed:                 5
% 3.45/1.01  sim_fw_subsumed:                        17
% 3.45/1.01  sim_bw_subsumed:                        2
% 3.45/1.01  sim_fw_subsumption_res:                 5
% 3.45/1.01  sim_bw_subsumption_res:                 0
% 3.45/1.01  sim_tautology_del:                      4
% 3.45/1.01  sim_eq_tautology_del:                   18
% 3.45/1.01  sim_eq_res_simp:                        4
% 3.45/1.01  sim_fw_demodulated:                     31
% 3.45/1.01  sim_bw_demodulated:                     62
% 3.45/1.01  sim_light_normalised:                   40
% 3.45/1.01  sim_joinable_taut:                      0
% 3.45/1.01  sim_joinable_simp:                      0
% 3.45/1.01  sim_ac_normalised:                      0
% 3.45/1.01  sim_smt_subsumption:                    0
% 3.45/1.01  
%------------------------------------------------------------------------------

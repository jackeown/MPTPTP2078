%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:48 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  214 (6262 expanded)
%              Number of clauses        :  149 (2334 expanded)
%              Number of leaves         :   23 (1172 expanded)
%              Depth                    :   26
%              Number of atoms          :  600 (30644 expanded)
%              Number of equality atoms :  296 (6119 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

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
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f43,plain,
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

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43])).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f57,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f42,plain,(
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

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1356,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1365,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3746,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_1365])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1659,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1775,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1659])).

cnf(c_1776,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1884,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1885,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1884])).

cnf(c_4018,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3746,c_38,c_1776,c_1885])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_412,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_32])).

cnf(c_413,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_415,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_35])).

cnf(c_1352,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_4023,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4018,c_1352])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1358,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2334,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1356,c_1358])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2335,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2334,c_31])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_398,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_399,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_401,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_35])).

cnf(c_1353,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_2337,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2335,c_1353])).

cnf(c_2455,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2337,c_38,c_1776,c_1885])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_352,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_28])).

cnf(c_353,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_688,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_353,c_30])).

cnf(c_689,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_1340,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_2459,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2455,c_1340])).

cnf(c_2460,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2459])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1656,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1657,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1656])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2264,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2265,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2264])).

cnf(c_2556,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2460,c_36,c_38,c_1657,c_1776,c_1885,c_2265])).

cnf(c_4176,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4023,c_2556])).

cnf(c_8,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_799,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1750,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_808,plain,
    ( X0 != X1
    | k2_funct_1(X0) = k2_funct_1(X1) ),
    theory(equality)).

cnf(c_1783,plain,
    ( k2_funct_1(sK2) = k2_funct_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_2024,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_800,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1781,plain,
    ( X0 != X1
    | k2_funct_1(sK2) != X1
    | k2_funct_1(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_2030,plain,
    ( X0 != k2_funct_1(sK2)
    | k2_funct_1(sK2) = X0
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1781])).

cnf(c_2032,plain,
    ( k2_funct_1(sK2) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2030])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2740,plain,
    ( ~ v1_xboole_0(k2_funct_1(sK2))
    | k1_xboole_0 = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_801,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2978,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X1))
    | k2_relat_1(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_2980,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2978])).

cnf(c_2484,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != X0
    | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_3866,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_relat_1(X0)
    | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_2484])).

cnf(c_3868,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_relat_1(k1_xboole_0)
    | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3866])).

cnf(c_806,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_3867,plain,
    ( k2_funct_1(sK2) != X0
    | k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_3869,plain,
    ( k2_funct_1(sK2) != k1_xboole_0
    | k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3867])).

cnf(c_4381,plain,
    ( ~ v1_xboole_0(k2_relat_1(X0))
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4383,plain,
    ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4381])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_659,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_661,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_659,c_33])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1359,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2776,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1356,c_1359])).

cnf(c_2948,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_661,c_2776])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1357,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4188,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4023,c_1357])).

cnf(c_4216,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4188,c_2455])).

cnf(c_4635,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4216,c_36,c_38,c_1657,c_1776,c_1885,c_2265])).

cnf(c_4643,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4635,c_1359])).

cnf(c_4649,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4643,c_2455])).

cnf(c_4703,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2948,c_4649])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_669,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_670,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_1341,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_671,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_1972,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1341,c_36,c_38,c_671,c_1657,c_1776,c_1885])).

cnf(c_1973,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1972])).

cnf(c_2458,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2455,c_1973])).

cnf(c_2469,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2458])).

cnf(c_2549,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2469,c_36,c_38,c_1776,c_1885,c_2265])).

cnf(c_2550,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2549])).

cnf(c_4177,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4023,c_2550])).

cnf(c_4640,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2948,c_4635])).

cnf(c_4782,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4703,c_2948,c_4177,c_4640])).

cnf(c_4787,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4782,c_4635])).

cnf(c_1370,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1367,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1369,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2279,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_1369])).

cnf(c_2588,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1370,c_2279])).

cnf(c_4868,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4787,c_2588])).

cnf(c_4891,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4868])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4949,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4951,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k2_funct_1(sK2))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4949])).

cnf(c_6665,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4176,c_36,c_38,c_8,c_0,c_1657,c_1750,c_1776,c_1885,c_2024,c_2032,c_2265,c_2460,c_2740,c_2980,c_3868,c_3869,c_4383,c_4891,c_4951])).

cnf(c_3961,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2335,c_1357])).

cnf(c_4080,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3961,c_36,c_38,c_1776,c_1885])).

cnf(c_1366,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4086,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK2),sK1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4080,c_1366])).

cnf(c_4626,plain,
    ( v1_xboole_0(k1_relat_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_4086])).

cnf(c_108,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3788,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_3789,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3788])).

cnf(c_3791,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3789])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1368,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3857,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_1366])).

cnf(c_4068,plain,
    ( v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_3857])).

cnf(c_5039,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4626,c_108,c_2948,c_3791,c_4068,c_4177,c_4640])).

cnf(c_5046,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5039,c_1369])).

cnf(c_4641,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,k1_relat_1(sK2))) != iProver_top
    | v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4635,c_1366])).

cnf(c_4950,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4949])).

cnf(c_4952,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_funct_1(sK2)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4950])).

cnf(c_5950,plain,
    ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4641,c_108,c_4868,c_4952])).

cnf(c_5954,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5950,c_5046])).

cnf(c_5959,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5954,c_1369])).

cnf(c_6669,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6665,c_4782,c_5046,c_5959])).

cnf(c_6670,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6669,c_2588])).

cnf(c_4805,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4782,c_1356])).

cnf(c_2286,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_1369])).

cnf(c_3206,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1370,c_2286])).

cnf(c_4810,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4805,c_3206])).

cnf(c_5459,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4810,c_5046])).

cnf(c_6672,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6670,c_5459])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:08:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.09/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.00  
% 3.09/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.09/1.00  
% 3.09/1.00  ------  iProver source info
% 3.09/1.00  
% 3.09/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.09/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.09/1.00  git: non_committed_changes: false
% 3.09/1.00  git: last_make_outside_of_git: false
% 3.09/1.00  
% 3.09/1.00  ------ 
% 3.09/1.00  
% 3.09/1.00  ------ Input Options
% 3.09/1.00  
% 3.09/1.00  --out_options                           all
% 3.09/1.00  --tptp_safe_out                         true
% 3.09/1.00  --problem_path                          ""
% 3.09/1.00  --include_path                          ""
% 3.09/1.00  --clausifier                            res/vclausify_rel
% 3.09/1.00  --clausifier_options                    --mode clausify
% 3.09/1.00  --stdin                                 false
% 3.09/1.00  --stats_out                             all
% 3.09/1.00  
% 3.09/1.00  ------ General Options
% 3.09/1.00  
% 3.09/1.00  --fof                                   false
% 3.09/1.00  --time_out_real                         305.
% 3.09/1.00  --time_out_virtual                      -1.
% 3.09/1.00  --symbol_type_check                     false
% 3.09/1.00  --clausify_out                          false
% 3.09/1.00  --sig_cnt_out                           false
% 3.09/1.00  --trig_cnt_out                          false
% 3.09/1.00  --trig_cnt_out_tolerance                1.
% 3.09/1.00  --trig_cnt_out_sk_spl                   false
% 3.09/1.00  --abstr_cl_out                          false
% 3.09/1.00  
% 3.09/1.00  ------ Global Options
% 3.09/1.00  
% 3.09/1.00  --schedule                              default
% 3.09/1.00  --add_important_lit                     false
% 3.09/1.00  --prop_solver_per_cl                    1000
% 3.09/1.00  --min_unsat_core                        false
% 3.09/1.00  --soft_assumptions                      false
% 3.09/1.00  --soft_lemma_size                       3
% 3.09/1.00  --prop_impl_unit_size                   0
% 3.09/1.00  --prop_impl_unit                        []
% 3.09/1.00  --share_sel_clauses                     true
% 3.09/1.00  --reset_solvers                         false
% 3.09/1.00  --bc_imp_inh                            [conj_cone]
% 3.09/1.00  --conj_cone_tolerance                   3.
% 3.09/1.00  --extra_neg_conj                        none
% 3.09/1.00  --large_theory_mode                     true
% 3.09/1.00  --prolific_symb_bound                   200
% 3.09/1.00  --lt_threshold                          2000
% 3.09/1.00  --clause_weak_htbl                      true
% 3.09/1.00  --gc_record_bc_elim                     false
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing Options
% 3.09/1.00  
% 3.09/1.00  --preprocessing_flag                    true
% 3.09/1.00  --time_out_prep_mult                    0.1
% 3.09/1.00  --splitting_mode                        input
% 3.09/1.00  --splitting_grd                         true
% 3.09/1.00  --splitting_cvd                         false
% 3.09/1.00  --splitting_cvd_svl                     false
% 3.09/1.00  --splitting_nvd                         32
% 3.09/1.00  --sub_typing                            true
% 3.09/1.00  --prep_gs_sim                           true
% 3.09/1.00  --prep_unflatten                        true
% 3.09/1.00  --prep_res_sim                          true
% 3.09/1.00  --prep_upred                            true
% 3.09/1.00  --prep_sem_filter                       exhaustive
% 3.09/1.00  --prep_sem_filter_out                   false
% 3.09/1.00  --pred_elim                             true
% 3.09/1.00  --res_sim_input                         true
% 3.09/1.00  --eq_ax_congr_red                       true
% 3.09/1.00  --pure_diseq_elim                       true
% 3.09/1.00  --brand_transform                       false
% 3.09/1.00  --non_eq_to_eq                          false
% 3.09/1.00  --prep_def_merge                        true
% 3.09/1.00  --prep_def_merge_prop_impl              false
% 3.09/1.00  --prep_def_merge_mbd                    true
% 3.09/1.00  --prep_def_merge_tr_red                 false
% 3.09/1.00  --prep_def_merge_tr_cl                  false
% 3.09/1.00  --smt_preprocessing                     true
% 3.09/1.00  --smt_ac_axioms                         fast
% 3.09/1.00  --preprocessed_out                      false
% 3.09/1.00  --preprocessed_stats                    false
% 3.09/1.00  
% 3.09/1.00  ------ Abstraction refinement Options
% 3.09/1.00  
% 3.09/1.00  --abstr_ref                             []
% 3.09/1.00  --abstr_ref_prep                        false
% 3.09/1.00  --abstr_ref_until_sat                   false
% 3.09/1.00  --abstr_ref_sig_restrict                funpre
% 3.09/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/1.00  --abstr_ref_under                       []
% 3.09/1.00  
% 3.09/1.00  ------ SAT Options
% 3.09/1.00  
% 3.09/1.00  --sat_mode                              false
% 3.09/1.00  --sat_fm_restart_options                ""
% 3.09/1.00  --sat_gr_def                            false
% 3.09/1.00  --sat_epr_types                         true
% 3.09/1.00  --sat_non_cyclic_types                  false
% 3.09/1.00  --sat_finite_models                     false
% 3.09/1.00  --sat_fm_lemmas                         false
% 3.09/1.00  --sat_fm_prep                           false
% 3.09/1.00  --sat_fm_uc_incr                        true
% 3.09/1.00  --sat_out_model                         small
% 3.09/1.00  --sat_out_clauses                       false
% 3.09/1.00  
% 3.09/1.00  ------ QBF Options
% 3.09/1.00  
% 3.09/1.00  --qbf_mode                              false
% 3.09/1.00  --qbf_elim_univ                         false
% 3.09/1.00  --qbf_dom_inst                          none
% 3.09/1.00  --qbf_dom_pre_inst                      false
% 3.09/1.00  --qbf_sk_in                             false
% 3.09/1.00  --qbf_pred_elim                         true
% 3.09/1.00  --qbf_split                             512
% 3.09/1.00  
% 3.09/1.00  ------ BMC1 Options
% 3.09/1.00  
% 3.09/1.00  --bmc1_incremental                      false
% 3.09/1.00  --bmc1_axioms                           reachable_all
% 3.09/1.00  --bmc1_min_bound                        0
% 3.09/1.00  --bmc1_max_bound                        -1
% 3.09/1.00  --bmc1_max_bound_default                -1
% 3.09/1.00  --bmc1_symbol_reachability              true
% 3.09/1.00  --bmc1_property_lemmas                  false
% 3.09/1.00  --bmc1_k_induction                      false
% 3.09/1.00  --bmc1_non_equiv_states                 false
% 3.09/1.00  --bmc1_deadlock                         false
% 3.09/1.00  --bmc1_ucm                              false
% 3.09/1.00  --bmc1_add_unsat_core                   none
% 3.09/1.00  --bmc1_unsat_core_children              false
% 3.09/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/1.00  --bmc1_out_stat                         full
% 3.09/1.00  --bmc1_ground_init                      false
% 3.09/1.00  --bmc1_pre_inst_next_state              false
% 3.09/1.00  --bmc1_pre_inst_state                   false
% 3.09/1.00  --bmc1_pre_inst_reach_state             false
% 3.09/1.00  --bmc1_out_unsat_core                   false
% 3.09/1.00  --bmc1_aig_witness_out                  false
% 3.09/1.00  --bmc1_verbose                          false
% 3.09/1.00  --bmc1_dump_clauses_tptp                false
% 3.09/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.09/1.00  --bmc1_dump_file                        -
% 3.09/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.09/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.09/1.00  --bmc1_ucm_extend_mode                  1
% 3.09/1.00  --bmc1_ucm_init_mode                    2
% 3.09/1.00  --bmc1_ucm_cone_mode                    none
% 3.09/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.09/1.00  --bmc1_ucm_relax_model                  4
% 3.09/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.09/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/1.00  --bmc1_ucm_layered_model                none
% 3.09/1.01  --bmc1_ucm_max_lemma_size               10
% 3.09/1.01  
% 3.09/1.01  ------ AIG Options
% 3.09/1.01  
% 3.09/1.01  --aig_mode                              false
% 3.09/1.01  
% 3.09/1.01  ------ Instantiation Options
% 3.09/1.01  
% 3.09/1.01  --instantiation_flag                    true
% 3.09/1.01  --inst_sos_flag                         false
% 3.09/1.01  --inst_sos_phase                        true
% 3.09/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/1.01  --inst_lit_sel_side                     num_symb
% 3.09/1.01  --inst_solver_per_active                1400
% 3.09/1.01  --inst_solver_calls_frac                1.
% 3.09/1.01  --inst_passive_queue_type               priority_queues
% 3.09/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/1.01  --inst_passive_queues_freq              [25;2]
% 3.09/1.01  --inst_dismatching                      true
% 3.09/1.01  --inst_eager_unprocessed_to_passive     true
% 3.09/1.01  --inst_prop_sim_given                   true
% 3.09/1.01  --inst_prop_sim_new                     false
% 3.09/1.01  --inst_subs_new                         false
% 3.09/1.01  --inst_eq_res_simp                      false
% 3.09/1.01  --inst_subs_given                       false
% 3.09/1.01  --inst_orphan_elimination               true
% 3.09/1.01  --inst_learning_loop_flag               true
% 3.09/1.01  --inst_learning_start                   3000
% 3.09/1.01  --inst_learning_factor                  2
% 3.09/1.01  --inst_start_prop_sim_after_learn       3
% 3.09/1.01  --inst_sel_renew                        solver
% 3.09/1.01  --inst_lit_activity_flag                true
% 3.09/1.01  --inst_restr_to_given                   false
% 3.09/1.01  --inst_activity_threshold               500
% 3.09/1.01  --inst_out_proof                        true
% 3.09/1.01  
% 3.09/1.01  ------ Resolution Options
% 3.09/1.01  
% 3.09/1.01  --resolution_flag                       true
% 3.09/1.01  --res_lit_sel                           adaptive
% 3.09/1.01  --res_lit_sel_side                      none
% 3.09/1.01  --res_ordering                          kbo
% 3.09/1.01  --res_to_prop_solver                    active
% 3.09/1.01  --res_prop_simpl_new                    false
% 3.09/1.01  --res_prop_simpl_given                  true
% 3.09/1.01  --res_passive_queue_type                priority_queues
% 3.09/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/1.01  --res_passive_queues_freq               [15;5]
% 3.09/1.01  --res_forward_subs                      full
% 3.09/1.01  --res_backward_subs                     full
% 3.09/1.01  --res_forward_subs_resolution           true
% 3.09/1.01  --res_backward_subs_resolution          true
% 3.09/1.01  --res_orphan_elimination                true
% 3.09/1.01  --res_time_limit                        2.
% 3.09/1.01  --res_out_proof                         true
% 3.09/1.01  
% 3.09/1.01  ------ Superposition Options
% 3.09/1.01  
% 3.09/1.01  --superposition_flag                    true
% 3.09/1.01  --sup_passive_queue_type                priority_queues
% 3.09/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.09/1.01  --demod_completeness_check              fast
% 3.09/1.01  --demod_use_ground                      true
% 3.09/1.01  --sup_to_prop_solver                    passive
% 3.09/1.01  --sup_prop_simpl_new                    true
% 3.09/1.01  --sup_prop_simpl_given                  true
% 3.09/1.01  --sup_fun_splitting                     false
% 3.09/1.01  --sup_smt_interval                      50000
% 3.09/1.01  
% 3.09/1.01  ------ Superposition Simplification Setup
% 3.09/1.01  
% 3.09/1.01  --sup_indices_passive                   []
% 3.09/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.01  --sup_full_bw                           [BwDemod]
% 3.09/1.01  --sup_immed_triv                        [TrivRules]
% 3.09/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.01  --sup_immed_bw_main                     []
% 3.09/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.01  
% 3.09/1.01  ------ Combination Options
% 3.09/1.01  
% 3.09/1.01  --comb_res_mult                         3
% 3.09/1.01  --comb_sup_mult                         2
% 3.09/1.01  --comb_inst_mult                        10
% 3.09/1.01  
% 3.09/1.01  ------ Debug Options
% 3.09/1.01  
% 3.09/1.01  --dbg_backtrace                         false
% 3.09/1.01  --dbg_dump_prop_clauses                 false
% 3.09/1.01  --dbg_dump_prop_clauses_file            -
% 3.09/1.01  --dbg_out_stat                          false
% 3.09/1.01  ------ Parsing...
% 3.09/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.09/1.01  
% 3.09/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.09/1.01  
% 3.09/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.09/1.01  
% 3.09/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.09/1.01  ------ Proving...
% 3.09/1.01  ------ Problem Properties 
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  clauses                                 36
% 3.09/1.01  conjectures                             3
% 3.09/1.01  EPR                                     5
% 3.09/1.01  Horn                                    31
% 3.09/1.01  unary                                   9
% 3.09/1.01  binary                                  8
% 3.09/1.01  lits                                    105
% 3.09/1.01  lits eq                                 42
% 3.09/1.01  fd_pure                                 0
% 3.09/1.01  fd_pseudo                               0
% 3.09/1.01  fd_cond                                 3
% 3.09/1.01  fd_pseudo_cond                          0
% 3.09/1.01  AC symbols                              0
% 3.09/1.01  
% 3.09/1.01  ------ Schedule dynamic 5 is on 
% 3.09/1.01  
% 3.09/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  ------ 
% 3.09/1.01  Current options:
% 3.09/1.01  ------ 
% 3.09/1.01  
% 3.09/1.01  ------ Input Options
% 3.09/1.01  
% 3.09/1.01  --out_options                           all
% 3.09/1.01  --tptp_safe_out                         true
% 3.09/1.01  --problem_path                          ""
% 3.09/1.01  --include_path                          ""
% 3.09/1.01  --clausifier                            res/vclausify_rel
% 3.09/1.01  --clausifier_options                    --mode clausify
% 3.09/1.01  --stdin                                 false
% 3.09/1.01  --stats_out                             all
% 3.09/1.01  
% 3.09/1.01  ------ General Options
% 3.09/1.01  
% 3.09/1.01  --fof                                   false
% 3.09/1.01  --time_out_real                         305.
% 3.09/1.01  --time_out_virtual                      -1.
% 3.09/1.01  --symbol_type_check                     false
% 3.09/1.01  --clausify_out                          false
% 3.09/1.01  --sig_cnt_out                           false
% 3.09/1.01  --trig_cnt_out                          false
% 3.09/1.01  --trig_cnt_out_tolerance                1.
% 3.09/1.01  --trig_cnt_out_sk_spl                   false
% 3.09/1.01  --abstr_cl_out                          false
% 3.09/1.01  
% 3.09/1.01  ------ Global Options
% 3.09/1.01  
% 3.09/1.01  --schedule                              default
% 3.09/1.01  --add_important_lit                     false
% 3.09/1.01  --prop_solver_per_cl                    1000
% 3.09/1.01  --min_unsat_core                        false
% 3.09/1.01  --soft_assumptions                      false
% 3.09/1.01  --soft_lemma_size                       3
% 3.09/1.01  --prop_impl_unit_size                   0
% 3.09/1.01  --prop_impl_unit                        []
% 3.09/1.01  --share_sel_clauses                     true
% 3.09/1.01  --reset_solvers                         false
% 3.09/1.01  --bc_imp_inh                            [conj_cone]
% 3.09/1.01  --conj_cone_tolerance                   3.
% 3.09/1.01  --extra_neg_conj                        none
% 3.09/1.01  --large_theory_mode                     true
% 3.09/1.01  --prolific_symb_bound                   200
% 3.09/1.01  --lt_threshold                          2000
% 3.09/1.01  --clause_weak_htbl                      true
% 3.09/1.01  --gc_record_bc_elim                     false
% 3.09/1.01  
% 3.09/1.01  ------ Preprocessing Options
% 3.09/1.01  
% 3.09/1.01  --preprocessing_flag                    true
% 3.09/1.01  --time_out_prep_mult                    0.1
% 3.09/1.01  --splitting_mode                        input
% 3.09/1.01  --splitting_grd                         true
% 3.09/1.01  --splitting_cvd                         false
% 3.09/1.01  --splitting_cvd_svl                     false
% 3.09/1.01  --splitting_nvd                         32
% 3.09/1.01  --sub_typing                            true
% 3.09/1.01  --prep_gs_sim                           true
% 3.09/1.01  --prep_unflatten                        true
% 3.09/1.01  --prep_res_sim                          true
% 3.09/1.01  --prep_upred                            true
% 3.09/1.01  --prep_sem_filter                       exhaustive
% 3.09/1.01  --prep_sem_filter_out                   false
% 3.09/1.01  --pred_elim                             true
% 3.09/1.01  --res_sim_input                         true
% 3.09/1.01  --eq_ax_congr_red                       true
% 3.09/1.01  --pure_diseq_elim                       true
% 3.09/1.01  --brand_transform                       false
% 3.09/1.01  --non_eq_to_eq                          false
% 3.09/1.01  --prep_def_merge                        true
% 3.09/1.01  --prep_def_merge_prop_impl              false
% 3.09/1.01  --prep_def_merge_mbd                    true
% 3.09/1.01  --prep_def_merge_tr_red                 false
% 3.09/1.01  --prep_def_merge_tr_cl                  false
% 3.09/1.01  --smt_preprocessing                     true
% 3.09/1.01  --smt_ac_axioms                         fast
% 3.09/1.01  --preprocessed_out                      false
% 3.09/1.01  --preprocessed_stats                    false
% 3.09/1.01  
% 3.09/1.01  ------ Abstraction refinement Options
% 3.09/1.01  
% 3.09/1.01  --abstr_ref                             []
% 3.09/1.01  --abstr_ref_prep                        false
% 3.09/1.01  --abstr_ref_until_sat                   false
% 3.09/1.01  --abstr_ref_sig_restrict                funpre
% 3.09/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/1.01  --abstr_ref_under                       []
% 3.09/1.01  
% 3.09/1.01  ------ SAT Options
% 3.09/1.01  
% 3.09/1.01  --sat_mode                              false
% 3.09/1.01  --sat_fm_restart_options                ""
% 3.09/1.01  --sat_gr_def                            false
% 3.09/1.01  --sat_epr_types                         true
% 3.09/1.01  --sat_non_cyclic_types                  false
% 3.09/1.01  --sat_finite_models                     false
% 3.09/1.01  --sat_fm_lemmas                         false
% 3.09/1.01  --sat_fm_prep                           false
% 3.09/1.01  --sat_fm_uc_incr                        true
% 3.09/1.01  --sat_out_model                         small
% 3.09/1.01  --sat_out_clauses                       false
% 3.09/1.01  
% 3.09/1.01  ------ QBF Options
% 3.09/1.01  
% 3.09/1.01  --qbf_mode                              false
% 3.09/1.01  --qbf_elim_univ                         false
% 3.09/1.01  --qbf_dom_inst                          none
% 3.09/1.01  --qbf_dom_pre_inst                      false
% 3.09/1.01  --qbf_sk_in                             false
% 3.09/1.01  --qbf_pred_elim                         true
% 3.09/1.01  --qbf_split                             512
% 3.09/1.01  
% 3.09/1.01  ------ BMC1 Options
% 3.09/1.01  
% 3.09/1.01  --bmc1_incremental                      false
% 3.09/1.01  --bmc1_axioms                           reachable_all
% 3.09/1.01  --bmc1_min_bound                        0
% 3.09/1.01  --bmc1_max_bound                        -1
% 3.09/1.01  --bmc1_max_bound_default                -1
% 3.09/1.01  --bmc1_symbol_reachability              true
% 3.09/1.01  --bmc1_property_lemmas                  false
% 3.09/1.01  --bmc1_k_induction                      false
% 3.09/1.01  --bmc1_non_equiv_states                 false
% 3.09/1.01  --bmc1_deadlock                         false
% 3.09/1.01  --bmc1_ucm                              false
% 3.09/1.01  --bmc1_add_unsat_core                   none
% 3.09/1.01  --bmc1_unsat_core_children              false
% 3.09/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/1.01  --bmc1_out_stat                         full
% 3.09/1.01  --bmc1_ground_init                      false
% 3.09/1.01  --bmc1_pre_inst_next_state              false
% 3.09/1.01  --bmc1_pre_inst_state                   false
% 3.09/1.01  --bmc1_pre_inst_reach_state             false
% 3.09/1.01  --bmc1_out_unsat_core                   false
% 3.09/1.01  --bmc1_aig_witness_out                  false
% 3.09/1.01  --bmc1_verbose                          false
% 3.09/1.01  --bmc1_dump_clauses_tptp                false
% 3.09/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.09/1.01  --bmc1_dump_file                        -
% 3.09/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.09/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.09/1.01  --bmc1_ucm_extend_mode                  1
% 3.09/1.01  --bmc1_ucm_init_mode                    2
% 3.09/1.01  --bmc1_ucm_cone_mode                    none
% 3.09/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.09/1.01  --bmc1_ucm_relax_model                  4
% 3.09/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.09/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/1.01  --bmc1_ucm_layered_model                none
% 3.09/1.01  --bmc1_ucm_max_lemma_size               10
% 3.09/1.01  
% 3.09/1.01  ------ AIG Options
% 3.09/1.01  
% 3.09/1.01  --aig_mode                              false
% 3.09/1.01  
% 3.09/1.01  ------ Instantiation Options
% 3.09/1.01  
% 3.09/1.01  --instantiation_flag                    true
% 3.09/1.01  --inst_sos_flag                         false
% 3.09/1.01  --inst_sos_phase                        true
% 3.09/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/1.01  --inst_lit_sel_side                     none
% 3.09/1.01  --inst_solver_per_active                1400
% 3.09/1.01  --inst_solver_calls_frac                1.
% 3.09/1.01  --inst_passive_queue_type               priority_queues
% 3.09/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/1.01  --inst_passive_queues_freq              [25;2]
% 3.09/1.01  --inst_dismatching                      true
% 3.09/1.01  --inst_eager_unprocessed_to_passive     true
% 3.09/1.01  --inst_prop_sim_given                   true
% 3.09/1.01  --inst_prop_sim_new                     false
% 3.09/1.01  --inst_subs_new                         false
% 3.09/1.01  --inst_eq_res_simp                      false
% 3.09/1.01  --inst_subs_given                       false
% 3.09/1.01  --inst_orphan_elimination               true
% 3.09/1.01  --inst_learning_loop_flag               true
% 3.09/1.01  --inst_learning_start                   3000
% 3.09/1.01  --inst_learning_factor                  2
% 3.09/1.01  --inst_start_prop_sim_after_learn       3
% 3.09/1.01  --inst_sel_renew                        solver
% 3.09/1.01  --inst_lit_activity_flag                true
% 3.09/1.01  --inst_restr_to_given                   false
% 3.09/1.01  --inst_activity_threshold               500
% 3.09/1.01  --inst_out_proof                        true
% 3.09/1.01  
% 3.09/1.01  ------ Resolution Options
% 3.09/1.01  
% 3.09/1.01  --resolution_flag                       false
% 3.09/1.01  --res_lit_sel                           adaptive
% 3.09/1.01  --res_lit_sel_side                      none
% 3.09/1.01  --res_ordering                          kbo
% 3.09/1.01  --res_to_prop_solver                    active
% 3.09/1.01  --res_prop_simpl_new                    false
% 3.09/1.01  --res_prop_simpl_given                  true
% 3.09/1.01  --res_passive_queue_type                priority_queues
% 3.09/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/1.01  --res_passive_queues_freq               [15;5]
% 3.09/1.01  --res_forward_subs                      full
% 3.09/1.01  --res_backward_subs                     full
% 3.09/1.01  --res_forward_subs_resolution           true
% 3.09/1.01  --res_backward_subs_resolution          true
% 3.09/1.01  --res_orphan_elimination                true
% 3.09/1.01  --res_time_limit                        2.
% 3.09/1.01  --res_out_proof                         true
% 3.09/1.01  
% 3.09/1.01  ------ Superposition Options
% 3.09/1.01  
% 3.09/1.01  --superposition_flag                    true
% 3.09/1.01  --sup_passive_queue_type                priority_queues
% 3.09/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.09/1.01  --demod_completeness_check              fast
% 3.09/1.01  --demod_use_ground                      true
% 3.09/1.01  --sup_to_prop_solver                    passive
% 3.09/1.01  --sup_prop_simpl_new                    true
% 3.09/1.01  --sup_prop_simpl_given                  true
% 3.09/1.01  --sup_fun_splitting                     false
% 3.09/1.01  --sup_smt_interval                      50000
% 3.09/1.01  
% 3.09/1.01  ------ Superposition Simplification Setup
% 3.09/1.01  
% 3.09/1.01  --sup_indices_passive                   []
% 3.09/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.01  --sup_full_bw                           [BwDemod]
% 3.09/1.01  --sup_immed_triv                        [TrivRules]
% 3.09/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.01  --sup_immed_bw_main                     []
% 3.09/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.01  
% 3.09/1.01  ------ Combination Options
% 3.09/1.01  
% 3.09/1.01  --comb_res_mult                         3
% 3.09/1.01  --comb_sup_mult                         2
% 3.09/1.01  --comb_inst_mult                        10
% 3.09/1.01  
% 3.09/1.01  ------ Debug Options
% 3.09/1.01  
% 3.09/1.01  --dbg_backtrace                         false
% 3.09/1.01  --dbg_dump_prop_clauses                 false
% 3.09/1.01  --dbg_dump_prop_clauses_file            -
% 3.09/1.01  --dbg_out_stat                          false
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  ------ Proving...
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  % SZS status Theorem for theBenchmark.p
% 3.09/1.01  
% 3.09/1.01   Resolution empty clause
% 3.09/1.01  
% 3.09/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.09/1.01  
% 3.09/1.01  fof(f18,conjecture,(
% 3.09/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f19,negated_conjecture,(
% 3.09/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.09/1.01    inference(negated_conjecture,[],[f18])).
% 3.09/1.01  
% 3.09/1.01  fof(f39,plain,(
% 3.09/1.01    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.09/1.01    inference(ennf_transformation,[],[f19])).
% 3.09/1.01  
% 3.09/1.01  fof(f40,plain,(
% 3.09/1.01    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.09/1.01    inference(flattening,[],[f39])).
% 3.09/1.01  
% 3.09/1.01  fof(f43,plain,(
% 3.09/1.01    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.09/1.01    introduced(choice_axiom,[])).
% 3.09/1.01  
% 3.09/1.01  fof(f44,plain,(
% 3.09/1.01    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.09/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43])).
% 3.09/1.01  
% 3.09/1.01  fof(f77,plain,(
% 3.09/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.09/1.01    inference(cnf_transformation,[],[f44])).
% 3.09/1.01  
% 3.09/1.01  fof(f7,axiom,(
% 3.09/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f26,plain,(
% 3.09/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.09/1.01    inference(ennf_transformation,[],[f7])).
% 3.09/1.01  
% 3.09/1.01  fof(f51,plain,(
% 3.09/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f26])).
% 3.09/1.01  
% 3.09/1.01  fof(f8,axiom,(
% 3.09/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f52,plain,(
% 3.09/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.09/1.01    inference(cnf_transformation,[],[f8])).
% 3.09/1.01  
% 3.09/1.01  fof(f11,axiom,(
% 3.09/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f29,plain,(
% 3.09/1.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.09/1.01    inference(ennf_transformation,[],[f11])).
% 3.09/1.01  
% 3.09/1.01  fof(f30,plain,(
% 3.09/1.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.09/1.01    inference(flattening,[],[f29])).
% 3.09/1.01  
% 3.09/1.01  fof(f58,plain,(
% 3.09/1.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f30])).
% 3.09/1.01  
% 3.09/1.01  fof(f78,plain,(
% 3.09/1.01    v2_funct_1(sK2)),
% 3.09/1.01    inference(cnf_transformation,[],[f44])).
% 3.09/1.01  
% 3.09/1.01  fof(f75,plain,(
% 3.09/1.01    v1_funct_1(sK2)),
% 3.09/1.01    inference(cnf_transformation,[],[f44])).
% 3.09/1.01  
% 3.09/1.01  fof(f14,axiom,(
% 3.09/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f32,plain,(
% 3.09/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.01    inference(ennf_transformation,[],[f14])).
% 3.09/1.01  
% 3.09/1.01  fof(f62,plain,(
% 3.09/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/1.01    inference(cnf_transformation,[],[f32])).
% 3.09/1.01  
% 3.09/1.01  fof(f79,plain,(
% 3.09/1.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.09/1.01    inference(cnf_transformation,[],[f44])).
% 3.09/1.01  
% 3.09/1.01  fof(f57,plain,(
% 3.09/1.01    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f30])).
% 3.09/1.01  
% 3.09/1.01  fof(f3,axiom,(
% 3.09/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f47,plain,(
% 3.09/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f3])).
% 3.09/1.01  
% 3.09/1.01  fof(f17,axiom,(
% 3.09/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f37,plain,(
% 3.09/1.01    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.09/1.01    inference(ennf_transformation,[],[f17])).
% 3.09/1.01  
% 3.09/1.01  fof(f38,plain,(
% 3.09/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.09/1.01    inference(flattening,[],[f37])).
% 3.09/1.01  
% 3.09/1.01  fof(f73,plain,(
% 3.09/1.01    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f38])).
% 3.09/1.01  
% 3.09/1.01  fof(f80,plain,(
% 3.09/1.01    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.09/1.01    inference(cnf_transformation,[],[f44])).
% 3.09/1.01  
% 3.09/1.01  fof(f10,axiom,(
% 3.09/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f27,plain,(
% 3.09/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.09/1.01    inference(ennf_transformation,[],[f10])).
% 3.09/1.01  
% 3.09/1.01  fof(f28,plain,(
% 3.09/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.09/1.01    inference(flattening,[],[f27])).
% 3.09/1.01  
% 3.09/1.01  fof(f56,plain,(
% 3.09/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f28])).
% 3.09/1.01  
% 3.09/1.01  fof(f55,plain,(
% 3.09/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f28])).
% 3.09/1.01  
% 3.09/1.01  fof(f9,axiom,(
% 3.09/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f54,plain,(
% 3.09/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.09/1.01    inference(cnf_transformation,[],[f9])).
% 3.09/1.01  
% 3.09/1.01  fof(f1,axiom,(
% 3.09/1.01    v1_xboole_0(k1_xboole_0)),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f45,plain,(
% 3.09/1.01    v1_xboole_0(k1_xboole_0)),
% 3.09/1.01    inference(cnf_transformation,[],[f1])).
% 3.09/1.01  
% 3.09/1.01  fof(f2,axiom,(
% 3.09/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f22,plain,(
% 3.09/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.09/1.01    inference(ennf_transformation,[],[f2])).
% 3.09/1.01  
% 3.09/1.01  fof(f46,plain,(
% 3.09/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f22])).
% 3.09/1.01  
% 3.09/1.01  fof(f15,axiom,(
% 3.09/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f33,plain,(
% 3.09/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.01    inference(ennf_transformation,[],[f15])).
% 3.09/1.01  
% 3.09/1.01  fof(f34,plain,(
% 3.09/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.01    inference(flattening,[],[f33])).
% 3.09/1.01  
% 3.09/1.01  fof(f42,plain,(
% 3.09/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.01    inference(nnf_transformation,[],[f34])).
% 3.09/1.01  
% 3.09/1.01  fof(f63,plain,(
% 3.09/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/1.01    inference(cnf_transformation,[],[f42])).
% 3.09/1.01  
% 3.09/1.01  fof(f76,plain,(
% 3.09/1.01    v1_funct_2(sK2,sK0,sK1)),
% 3.09/1.01    inference(cnf_transformation,[],[f44])).
% 3.09/1.01  
% 3.09/1.01  fof(f13,axiom,(
% 3.09/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f31,plain,(
% 3.09/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.01    inference(ennf_transformation,[],[f13])).
% 3.09/1.01  
% 3.09/1.01  fof(f61,plain,(
% 3.09/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/1.01    inference(cnf_transformation,[],[f31])).
% 3.09/1.01  
% 3.09/1.01  fof(f16,axiom,(
% 3.09/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f35,plain,(
% 3.09/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.09/1.01    inference(ennf_transformation,[],[f16])).
% 3.09/1.01  
% 3.09/1.01  fof(f36,plain,(
% 3.09/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.09/1.01    inference(flattening,[],[f35])).
% 3.09/1.01  
% 3.09/1.01  fof(f71,plain,(
% 3.09/1.01    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f36])).
% 3.09/1.01  
% 3.09/1.01  fof(f70,plain,(
% 3.09/1.01    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f36])).
% 3.09/1.01  
% 3.09/1.01  fof(f5,axiom,(
% 3.09/1.01    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f24,plain,(
% 3.09/1.01    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.09/1.01    inference(ennf_transformation,[],[f5])).
% 3.09/1.01  
% 3.09/1.01  fof(f49,plain,(
% 3.09/1.01    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f24])).
% 3.09/1.01  
% 3.09/1.01  fof(f6,axiom,(
% 3.09/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f25,plain,(
% 3.09/1.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.09/1.01    inference(ennf_transformation,[],[f6])).
% 3.09/1.01  
% 3.09/1.01  fof(f50,plain,(
% 3.09/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f25])).
% 3.09/1.01  
% 3.09/1.01  fof(f4,axiom,(
% 3.09/1.01    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.09/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f23,plain,(
% 3.09/1.01    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 3.09/1.01    inference(ennf_transformation,[],[f4])).
% 3.09/1.01  
% 3.09/1.01  fof(f48,plain,(
% 3.09/1.01    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f23])).
% 3.09/1.01  
% 3.09/1.01  cnf(c_33,negated_conjecture,
% 3.09/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.09/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1356,plain,
% 3.09/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_6,plain,
% 3.09/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1365,plain,
% 3.09/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.09/1.01      | v1_relat_1(X1) != iProver_top
% 3.09/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3746,plain,
% 3.09/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.09/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1356,c_1365]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_38,plain,
% 3.09/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1659,plain,
% 3.09/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | v1_relat_1(sK2) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1775,plain,
% 3.09/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.09/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.09/1.01      | v1_relat_1(sK2) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_1659]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1776,plain,
% 3.09/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.09/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.09/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_1775]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_7,plain,
% 3.09/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.09/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1884,plain,
% 3.09/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1885,plain,
% 3.09/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_1884]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4018,plain,
% 3.09/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_3746,c_38,c_1776,c_1885]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_12,plain,
% 3.09/1.01      ( ~ v2_funct_1(X0)
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_32,negated_conjecture,
% 3.09/1.01      ( v2_funct_1(sK2) ),
% 3.09/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_412,plain,
% 3.09/1.01      ( ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.09/1.01      | sK2 != X0 ),
% 3.09/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_32]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_413,plain,
% 3.09/1.01      ( ~ v1_funct_1(sK2)
% 3.09/1.01      | ~ v1_relat_1(sK2)
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.09/1.01      inference(unflattening,[status(thm)],[c_412]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_35,negated_conjecture,
% 3.09/1.01      ( v1_funct_1(sK2) ),
% 3.09/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_415,plain,
% 3.09/1.01      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.09/1.01      inference(global_propositional_subsumption,[status(thm)],[c_413,c_35]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1352,plain,
% 3.09/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.09/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4023,plain,
% 3.09/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_4018,c_1352]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_17,plain,
% 3.09/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1358,plain,
% 3.09/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.09/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2334,plain,
% 3.09/1.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1356,c_1358]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_31,negated_conjecture,
% 3.09/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.09/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2335,plain,
% 3.09/1.01      ( k2_relat_1(sK2) = sK1 ),
% 3.09/1.01      inference(light_normalisation,[status(thm)],[c_2334,c_31]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_13,plain,
% 3.09/1.01      ( ~ v2_funct_1(X0)
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_398,plain,
% 3.09/1.01      ( ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.09/1.01      | sK2 != X0 ),
% 3.09/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_399,plain,
% 3.09/1.01      ( ~ v1_funct_1(sK2)
% 3.09/1.01      | ~ v1_relat_1(sK2)
% 3.09/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.09/1.01      inference(unflattening,[status(thm)],[c_398]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_401,plain,
% 3.09/1.01      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.09/1.01      inference(global_propositional_subsumption,[status(thm)],[c_399,c_35]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1353,plain,
% 3.09/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.09/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2337,plain,
% 3.09/1.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1 | v1_relat_1(sK2) != iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_2335,c_1353]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2455,plain,
% 3.09/1.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_2337,c_38,c_1776,c_1885]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2,plain,
% 3.09/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_28,plain,
% 3.09/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.09/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_352,plain,
% 3.09/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | X1 != X2
% 3.09/1.01      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.09/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_28]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_353,plain,
% 3.09/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.09/1.01      inference(unflattening,[status(thm)],[c_352]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_30,negated_conjecture,
% 3.09/1.01      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.09/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.09/1.01      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.09/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_688,plain,
% 3.09/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | k2_funct_1(sK2) != X0
% 3.09/1.01      | k1_relat_1(X0) != sK1
% 3.09/1.01      | k2_relat_1(X0) != k1_xboole_0
% 3.09/1.01      | sK0 != X1 ),
% 3.09/1.01      inference(resolution_lifted,[status(thm)],[c_353,c_30]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_689,plain,
% 3.09/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.09/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.09/1.01      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.09/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.09/1.01      inference(unflattening,[status(thm)],[c_688]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1340,plain,
% 3.09/1.01      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.09/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2459,plain,
% 3.09/1.01      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.09/1.01      | sK1 != sK1
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.09/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_2455,c_1340]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2460,plain,
% 3.09/1.01      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.09/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.09/1.01      inference(equality_resolution_simp,[status(thm)],[c_2459]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_36,plain,
% 3.09/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_10,plain,
% 3.09/1.01      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1656,plain,
% 3.09/1.01      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1657,plain,
% 3.09/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.09/1.01      | v1_funct_1(sK2) != iProver_top
% 3.09/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_1656]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_11,plain,
% 3.09/1.01      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.09/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2264,plain,
% 3.09/1.01      ( ~ v1_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2265,plain,
% 3.09/1.01      ( v1_funct_1(sK2) != iProver_top
% 3.09/1.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.09/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_2264]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2556,plain,
% 3.09/1.01      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_2460,c_36,c_38,c_1657,c_1776,c_1885,c_2265]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4176,plain,
% 3.09/1.01      ( k1_relat_1(sK2) != k1_xboole_0
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_4023,c_2556]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_8,plain,
% 3.09/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.09/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_0,plain,
% 3.09/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_799,plain,( X0 = X0 ),theory(equality) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1750,plain,
% 3.09/1.01      ( sK2 = sK2 ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_799]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_808,plain,
% 3.09/1.01      ( X0 != X1 | k2_funct_1(X0) = k2_funct_1(X1) ),
% 3.09/1.01      theory(equality) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1783,plain,
% 3.09/1.01      ( k2_funct_1(sK2) = k2_funct_1(X0) | sK2 != X0 ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_808]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2024,plain,
% 3.09/1.01      ( k2_funct_1(sK2) = k2_funct_1(sK2) | sK2 != sK2 ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_1783]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_800,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1781,plain,
% 3.09/1.01      ( X0 != X1 | k2_funct_1(sK2) != X1 | k2_funct_1(sK2) = X0 ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_800]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2030,plain,
% 3.09/1.01      ( X0 != k2_funct_1(sK2)
% 3.09/1.01      | k2_funct_1(sK2) = X0
% 3.09/1.01      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_1781]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2032,plain,
% 3.09/1.01      ( k2_funct_1(sK2) != k2_funct_1(sK2)
% 3.09/1.01      | k2_funct_1(sK2) = k1_xboole_0
% 3.09/1.01      | k1_xboole_0 != k2_funct_1(sK2) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_2030]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1,plain,
% 3.09/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.09/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2740,plain,
% 3.09/1.01      ( ~ v1_xboole_0(k2_funct_1(sK2)) | k1_xboole_0 = k2_funct_1(sK2) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_801,plain,
% 3.09/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.09/1.01      theory(equality) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2978,plain,
% 3.09/1.01      ( ~ v1_xboole_0(X0)
% 3.09/1.01      | v1_xboole_0(k2_relat_1(X1))
% 3.09/1.01      | k2_relat_1(X1) != X0 ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_801]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2980,plain,
% 3.09/1.01      ( v1_xboole_0(k2_relat_1(k1_xboole_0))
% 3.09/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 3.09/1.01      | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_2978]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2484,plain,
% 3.09/1.01      ( k2_relat_1(k2_funct_1(sK2)) != X0
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.09/1.01      | k1_xboole_0 != X0 ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_800]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3866,plain,
% 3.09/1.01      ( k2_relat_1(k2_funct_1(sK2)) != k2_relat_1(X0)
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.09/1.01      | k1_xboole_0 != k2_relat_1(X0) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_2484]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3868,plain,
% 3.09/1.01      ( k2_relat_1(k2_funct_1(sK2)) != k2_relat_1(k1_xboole_0)
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.09/1.01      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_3866]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_806,plain,
% 3.09/1.01      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 3.09/1.01      theory(equality) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3867,plain,
% 3.09/1.01      ( k2_funct_1(sK2) != X0 | k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(X0) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_806]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3869,plain,
% 3.09/1.01      ( k2_funct_1(sK2) != k1_xboole_0
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k1_xboole_0) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_3867]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4381,plain,
% 3.09/1.01      ( ~ v1_xboole_0(k2_relat_1(X0)) | k1_xboole_0 = k2_relat_1(X0) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4383,plain,
% 3.09/1.01      ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
% 3.09/1.01      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_4381]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_23,plain,
% 3.09/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.09/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.09/1.01      | k1_xboole_0 = X2 ),
% 3.09/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_34,negated_conjecture,
% 3.09/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.09/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_658,plain,
% 3.09/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.09/1.01      | sK0 != X1
% 3.09/1.01      | sK1 != X2
% 3.09/1.01      | sK2 != X0
% 3.09/1.01      | k1_xboole_0 = X2 ),
% 3.09/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_659,plain,
% 3.09/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.09/1.01      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.09/1.01      | k1_xboole_0 = sK1 ),
% 3.09/1.01      inference(unflattening,[status(thm)],[c_658]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_661,plain,
% 3.09/1.01      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.09/1.01      inference(global_propositional_subsumption,[status(thm)],[c_659,c_33]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_16,plain,
% 3.09/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1359,plain,
% 3.09/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.09/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2776,plain,
% 3.09/1.01      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1356,c_1359]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2948,plain,
% 3.09/1.01      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_661,c_2776]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_24,plain,
% 3.09/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1357,plain,
% 3.09/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.09/1.01      | v1_funct_1(X0) != iProver_top
% 3.09/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4188,plain,
% 3.09/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 3.09/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.09/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_4023,c_1357]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4216,plain,
% 3.09/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 3.09/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.09/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.09/1.01      inference(light_normalisation,[status(thm)],[c_4188,c_2455]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4635,plain,
% 3.09/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_4216,c_36,c_38,c_1657,c_1776,c_1885,c_2265]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4643,plain,
% 3.09/1.01      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_4635,c_1359]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4649,plain,
% 3.09/1.01      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
% 3.09/1.01      inference(light_normalisation,[status(thm)],[c_4643,c_2455]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4703,plain,
% 3.09/1.01      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1 | sK1 = k1_xboole_0 ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_2948,c_4649]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_25,plain,
% 3.09/1.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_669,plain,
% 3.09/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | k2_funct_1(sK2) != X0
% 3.09/1.01      | k1_relat_1(X0) != sK1
% 3.09/1.01      | k2_relat_1(X0) != sK0 ),
% 3.09/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_670,plain,
% 3.09/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.09/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.09/1.01      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.09/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.09/1.01      inference(unflattening,[status(thm)],[c_669]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1341,plain,
% 3.09/1.01      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.09/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_671,plain,
% 3.09/1.01      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.09/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1972,plain,
% 3.09/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.09/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.09/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_1341,c_36,c_38,c_671,c_1657,c_1776,c_1885]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1973,plain,
% 3.09/1.01      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.09/1.01      inference(renaming,[status(thm)],[c_1972]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2458,plain,
% 3.09/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.09/1.01      | sK1 != sK1
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_2455,c_1973]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2469,plain,
% 3.09/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.09/1.01      inference(equality_resolution_simp,[status(thm)],[c_2458]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2549,plain,
% 3.09/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_2469,c_36,c_38,c_1776,c_1885,c_2265]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2550,plain,
% 3.09/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.09/1.01      inference(renaming,[status(thm)],[c_2549]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4177,plain,
% 3.09/1.01      ( k1_relat_1(sK2) != sK0
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_4023,c_2550]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4640,plain,
% 3.09/1.01      ( sK1 = k1_xboole_0
% 3.09/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_2948,c_4635]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4782,plain,
% 3.09/1.01      ( sK1 = k1_xboole_0 ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_4703,c_2948,c_4177,c_4640]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4787,plain,
% 3.09/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_4782,c_4635]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1370,plain,
% 3.09/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4,plain,
% 3.09/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.09/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1367,plain,
% 3.09/1.01      ( v1_xboole_0(X0) != iProver_top
% 3.09/1.01      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1369,plain,
% 3.09/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2279,plain,
% 3.09/1.01      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1367,c_1369]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2588,plain,
% 3.09/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1370,c_2279]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4868,plain,
% 3.09/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_4787,c_2588]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4891,plain,
% 3.09/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
% 3.09/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_4868]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_5,plain,
% 3.09/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.09/1.01      | ~ v1_xboole_0(X1)
% 3.09/1.01      | v1_xboole_0(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4949,plain,
% 3.09/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(X0))
% 3.09/1.01      | ~ v1_xboole_0(X0)
% 3.09/1.01      | v1_xboole_0(k2_funct_1(sK2)) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4951,plain,
% 3.09/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
% 3.09/1.01      | v1_xboole_0(k2_funct_1(sK2))
% 3.09/1.01      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_4949]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_6665,plain,
% 3.09/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_4176,c_36,c_38,c_8,c_0,c_1657,c_1750,c_1776,c_1885,c_2024,
% 3.09/1.01                 c_2032,c_2265,c_2460,c_2740,c_2980,c_3868,c_3869,c_4383,
% 3.09/1.01                 c_4891,c_4951]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3961,plain,
% 3.09/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
% 3.09/1.01      | v1_funct_1(sK2) != iProver_top
% 3.09/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_2335,c_1357]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4080,plain,
% 3.09/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_3961,c_36,c_38,c_1776,c_1885]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1366,plain,
% 3.09/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.09/1.01      | v1_xboole_0(X1) != iProver_top
% 3.09/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4086,plain,
% 3.09/1.01      ( v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK2),sK1)) != iProver_top
% 3.09/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_4080,c_1366]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4626,plain,
% 3.09/1.01      ( v1_xboole_0(k1_relat_1(sK2)) != iProver_top
% 3.09/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1367,c_4086]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_108,plain,
% 3.09/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3788,plain,
% 3.09/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_801]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3789,plain,
% 3.09/1.01      ( sK1 != X0
% 3.09/1.01      | v1_xboole_0(X0) != iProver_top
% 3.09/1.01      | v1_xboole_0(sK1) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_3788]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3791,plain,
% 3.09/1.01      ( sK1 != k1_xboole_0
% 3.09/1.01      | v1_xboole_0(sK1) = iProver_top
% 3.09/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_3789]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3,plain,
% 3.09/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 3.09/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1368,plain,
% 3.09/1.01      ( v1_xboole_0(X0) != iProver_top
% 3.09/1.01      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3857,plain,
% 3.09/1.01      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.09/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1356,c_1366]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4068,plain,
% 3.09/1.01      ( v1_xboole_0(sK1) != iProver_top | v1_xboole_0(sK2) = iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1368,c_3857]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_5039,plain,
% 3.09/1.01      ( v1_xboole_0(sK2) = iProver_top ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_4626,c_108,c_2948,c_3791,c_4068,c_4177,c_4640]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_5046,plain,
% 3.09/1.01      ( sK2 = k1_xboole_0 ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_5039,c_1369]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4641,plain,
% 3.09/1.01      ( v1_xboole_0(k2_zfmisc_1(sK1,k1_relat_1(sK2))) != iProver_top
% 3.09/1.01      | v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_4635,c_1366]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4950,plain,
% 3.09/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(X0)) != iProver_top
% 3.09/1.01      | v1_xboole_0(X0) != iProver_top
% 3.09/1.01      | v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_4949]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4952,plain,
% 3.09/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.09/1.01      | v1_xboole_0(k2_funct_1(sK2)) = iProver_top
% 3.09/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_4950]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_5950,plain,
% 3.09/1.01      ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_4641,c_108,c_4868,c_4952]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_5954,plain,
% 3.09/1.01      ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 3.09/1.01      inference(light_normalisation,[status(thm)],[c_5950,c_5046]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_5959,plain,
% 3.09/1.01      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_5954,c_1369]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_6669,plain,
% 3.09/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.09/1.01      inference(light_normalisation,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_6665,c_4782,c_5046,c_5959]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_6670,plain,
% 3.09/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_6669,c_2588]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4805,plain,
% 3.09/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_4782,c_1356]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2286,plain,
% 3.09/1.01      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | v1_xboole_0(X1) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1368,c_1369]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3206,plain,
% 3.09/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1370,c_2286]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4810,plain,
% 3.09/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_4805,c_3206]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_5459,plain,
% 3.09/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.09/1.01      inference(light_normalisation,[status(thm)],[c_4810,c_5046]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_6672,plain,
% 3.09/1.01      ( $false ),
% 3.09/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_6670,c_5459]) ).
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.09/1.01  
% 3.09/1.01  ------                               Statistics
% 3.09/1.01  
% 3.09/1.01  ------ General
% 3.09/1.01  
% 3.09/1.01  abstr_ref_over_cycles:                  0
% 3.09/1.01  abstr_ref_under_cycles:                 0
% 3.09/1.01  gc_basic_clause_elim:                   0
% 3.09/1.01  forced_gc_time:                         0
% 3.09/1.01  parsing_time:                           0.016
% 3.09/1.01  unif_index_cands_time:                  0.
% 3.09/1.01  unif_index_add_time:                    0.
% 3.09/1.01  orderings_time:                         0.
% 3.09/1.01  out_proof_time:                         0.014
% 3.09/1.01  total_time:                             0.253
% 3.09/1.01  num_of_symbols:                         49
% 3.09/1.01  num_of_terms:                           5349
% 3.09/1.01  
% 3.09/1.01  ------ Preprocessing
% 3.09/1.01  
% 3.09/1.01  num_of_splits:                          0
% 3.09/1.01  num_of_split_atoms:                     0
% 3.09/1.01  num_of_reused_defs:                     0
% 3.09/1.01  num_eq_ax_congr_red:                    3
% 3.09/1.01  num_of_sem_filtered_clauses:            1
% 3.09/1.01  num_of_subtypes:                        0
% 3.09/1.01  monotx_restored_types:                  0
% 3.09/1.01  sat_num_of_epr_types:                   0
% 3.09/1.01  sat_num_of_non_cyclic_types:            0
% 3.09/1.01  sat_guarded_non_collapsed_types:        0
% 3.09/1.01  num_pure_diseq_elim:                    0
% 3.09/1.01  simp_replaced_by:                       0
% 3.09/1.01  res_preprocessed:                       133
% 3.09/1.01  prep_upred:                             0
% 3.09/1.01  prep_unflattend:                        55
% 3.09/1.01  smt_new_axioms:                         0
% 3.09/1.01  pred_elim_cands:                        7
% 3.09/1.01  pred_elim:                              3
% 3.09/1.01  pred_elim_cl:                           -2
% 3.09/1.01  pred_elim_cycles:                       4
% 3.09/1.01  merged_defs:                            0
% 3.09/1.01  merged_defs_ncl:                        0
% 3.09/1.01  bin_hyper_res:                          0
% 3.09/1.01  prep_cycles:                            3
% 3.09/1.01  pred_elim_time:                         0.009
% 3.09/1.01  splitting_time:                         0.
% 3.09/1.01  sem_filter_time:                        0.
% 3.09/1.01  monotx_time:                            0.
% 3.09/1.01  subtype_inf_time:                       0.
% 3.09/1.01  
% 3.09/1.01  ------ Problem properties
% 3.09/1.01  
% 3.09/1.01  clauses:                                36
% 3.09/1.01  conjectures:                            3
% 3.09/1.01  epr:                                    5
% 3.09/1.01  horn:                                   31
% 3.09/1.01  ground:                                 19
% 3.09/1.01  unary:                                  9
% 3.09/1.01  binary:                                 8
% 3.09/1.01  lits:                                   105
% 3.09/1.01  lits_eq:                                42
% 3.09/1.01  fd_pure:                                0
% 3.09/1.01  fd_pseudo:                              0
% 3.09/1.01  fd_cond:                                3
% 3.09/1.01  fd_pseudo_cond:                         0
% 3.09/1.01  ac_symbols:                             0
% 3.09/1.01  
% 3.09/1.01  ------ Propositional Solver
% 3.09/1.01  
% 3.09/1.01  prop_solver_calls:                      23
% 3.09/1.01  prop_fast_solver_calls:                 1144
% 3.09/1.01  smt_solver_calls:                       0
% 3.09/1.01  smt_fast_solver_calls:                  0
% 3.09/1.01  prop_num_of_clauses:                    2255
% 3.09/1.01  prop_preprocess_simplified:             6343
% 3.09/1.01  prop_fo_subsumed:                       52
% 3.09/1.01  prop_solver_time:                       0.
% 3.09/1.01  smt_solver_time:                        0.
% 3.09/1.01  smt_fast_solver_time:                   0.
% 3.09/1.01  prop_fast_solver_time:                  0.
% 3.09/1.01  prop_unsat_core_time:                   0.
% 3.09/1.01  
% 3.09/1.01  ------ QBF
% 3.09/1.01  
% 3.09/1.01  qbf_q_res:                              0
% 3.09/1.01  qbf_num_tautologies:                    0
% 3.09/1.01  qbf_prep_cycles:                        0
% 3.09/1.01  
% 3.09/1.01  ------ BMC1
% 3.09/1.01  
% 3.09/1.01  bmc1_current_bound:                     -1
% 3.09/1.01  bmc1_last_solved_bound:                 -1
% 3.09/1.01  bmc1_unsat_core_size:                   -1
% 3.09/1.01  bmc1_unsat_core_parents_size:           -1
% 3.09/1.01  bmc1_merge_next_fun:                    0
% 3.09/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.09/1.01  
% 3.09/1.01  ------ Instantiation
% 3.09/1.01  
% 3.09/1.01  inst_num_of_clauses:                    761
% 3.09/1.01  inst_num_in_passive:                    28
% 3.09/1.01  inst_num_in_active:                     384
% 3.09/1.01  inst_num_in_unprocessed:                349
% 3.09/1.01  inst_num_of_loops:                      460
% 3.09/1.01  inst_num_of_learning_restarts:          0
% 3.09/1.01  inst_num_moves_active_passive:          74
% 3.09/1.01  inst_lit_activity:                      0
% 3.09/1.01  inst_lit_activity_moves:                0
% 3.09/1.01  inst_num_tautologies:                   0
% 3.09/1.01  inst_num_prop_implied:                  0
% 3.09/1.01  inst_num_existing_simplified:           0
% 3.09/1.01  inst_num_eq_res_simplified:             0
% 3.09/1.01  inst_num_child_elim:                    0
% 3.09/1.01  inst_num_of_dismatching_blockings:      435
% 3.09/1.01  inst_num_of_non_proper_insts:           687
% 3.09/1.01  inst_num_of_duplicates:                 0
% 3.09/1.01  inst_inst_num_from_inst_to_res:         0
% 3.09/1.01  inst_dismatching_checking_time:         0.
% 3.09/1.01  
% 3.09/1.01  ------ Resolution
% 3.09/1.01  
% 3.09/1.01  res_num_of_clauses:                     0
% 3.09/1.01  res_num_in_passive:                     0
% 3.09/1.01  res_num_in_active:                      0
% 3.09/1.01  res_num_of_loops:                       136
% 3.09/1.01  res_forward_subset_subsumed:            36
% 3.09/1.01  res_backward_subset_subsumed:           2
% 3.09/1.01  res_forward_subsumed:                   0
% 3.09/1.01  res_backward_subsumed:                  0
% 3.09/1.01  res_forward_subsumption_resolution:     1
% 3.09/1.01  res_backward_subsumption_resolution:    0
% 3.09/1.01  res_clause_to_clause_subsumption:       301
% 3.09/1.01  res_orphan_elimination:                 0
% 3.09/1.01  res_tautology_del:                      120
% 3.09/1.01  res_num_eq_res_simplified:              0
% 3.09/1.01  res_num_sel_changes:                    0
% 3.09/1.01  res_moves_from_active_to_pass:          0
% 3.09/1.01  
% 3.09/1.01  ------ Superposition
% 3.09/1.01  
% 3.09/1.01  sup_time_total:                         0.
% 3.09/1.01  sup_time_generating:                    0.
% 3.09/1.01  sup_time_sim_full:                      0.
% 3.09/1.01  sup_time_sim_immed:                     0.
% 3.09/1.01  
% 3.09/1.01  sup_num_of_clauses:                     73
% 3.09/1.01  sup_num_in_active:                      45
% 3.09/1.01  sup_num_in_passive:                     28
% 3.09/1.01  sup_num_of_loops:                       90
% 3.09/1.01  sup_fw_superposition:                   58
% 3.09/1.01  sup_bw_superposition:                   59
% 3.09/1.01  sup_immediate_simplified:               70
% 3.09/1.01  sup_given_eliminated:                   2
% 3.09/1.01  comparisons_done:                       0
% 3.09/1.01  comparisons_avoided:                    5
% 3.09/1.01  
% 3.09/1.01  ------ Simplifications
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  sim_fw_subset_subsumed:                 12
% 3.09/1.01  sim_bw_subset_subsumed:                 9
% 3.09/1.01  sim_fw_subsumed:                        5
% 3.09/1.01  sim_bw_subsumed:                        1
% 3.09/1.01  sim_fw_subsumption_res:                 2
% 3.09/1.01  sim_bw_subsumption_res:                 3
% 3.09/1.01  sim_tautology_del:                      10
% 3.09/1.01  sim_eq_tautology_del:                   14
% 3.09/1.01  sim_eq_res_simp:                        6
% 3.09/1.01  sim_fw_demodulated:                     17
% 3.09/1.01  sim_bw_demodulated:                     48
% 3.09/1.01  sim_light_normalised:                   57
% 3.09/1.01  sim_joinable_taut:                      0
% 3.09/1.01  sim_joinable_simp:                      0
% 3.09/1.01  sim_ac_normalised:                      0
% 3.09/1.01  sim_smt_subsumption:                    0
% 3.09/1.01  
%------------------------------------------------------------------------------

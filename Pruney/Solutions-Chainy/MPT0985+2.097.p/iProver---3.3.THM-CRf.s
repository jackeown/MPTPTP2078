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
% DateTime   : Thu Dec  3 12:02:39 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  237 (20427 expanded)
%              Number of clauses        :  165 (6357 expanded)
%              Number of leaves         :   21 (4020 expanded)
%              Depth                    :   31
%              Number of atoms          :  695 (110856 expanded)
%              Number of equality atoms :  346 (21263 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
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
    inference(ennf_transformation,[],[f13])).

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

fof(f41,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f19])).

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

fof(f42,plain,
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

fof(f43,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42])).

fof(f74,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f51,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] : k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f53,f66,f66])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_659,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_661,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_659,c_31])).

cnf(c_1512,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1516,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2997,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1512,c_1516])).

cnf(c_3170,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_661,c_2997])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_405,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_30])).

cnf(c_406,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_408,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_33])).

cnf(c_1508,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1810,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1819,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1508,c_33,c_31,c_406,c_1810])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1513,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3516,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1819,c_1513])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1515,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2622,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1512,c_1515])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2624,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2622,c_29])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_391,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_30])).

cnf(c_392,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_394,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_33])).

cnf(c_1509,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_1823,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1509,c_33,c_31,c_392,c_1810])).

cnf(c_2632,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2624,c_1823])).

cnf(c_3553,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3516,c_2632])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1789,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1790,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1789])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1792,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1793,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1792])).

cnf(c_1811,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1810])).

cnf(c_3819,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3553,c_34,c_36,c_1790,c_1793,c_1811])).

cnf(c_3825,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3819,c_1516])).

cnf(c_3844,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3825,c_2632])).

cnf(c_3855,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3170,c_3844])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_28,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_669,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k2_relat_1(X0) != sK0
    | k1_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_670,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_682,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_670,c_10])).

cnf(c_1498,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_671,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_2336,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1498,c_34,c_36,c_671,c_1790,c_1793,c_1811])).

cnf(c_2337,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2336])).

cnf(c_2340,plain,
    ( k2_relat_1(sK2) != sK1
    | k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2337,c_1819,c_1823])).

cnf(c_2630,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2624,c_2340])).

cnf(c_2640,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2630])).

cnf(c_3269,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3170,c_2640])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_345,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_26])).

cnf(c_346,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_688,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_346,c_28])).

cnf(c_689,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_701,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_689,c_10])).

cnf(c_1497,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_690,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_1894,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1497,c_34,c_36,c_690,c_1790,c_1793,c_1811])).

cnf(c_1895,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1894])).

cnf(c_1898,plain,
    ( k2_relat_1(sK2) != sK1
    | k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1895,c_1819,c_1823])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1523,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2647,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2624,c_1523])).

cnf(c_2735,plain,
    ( sK1 != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2647,c_36,c_1811])).

cnf(c_2736,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2735])).

cnf(c_3376,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3269,c_1898,c_2624,c_2736])).

cnf(c_3824,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3170,c_3819])).

cnf(c_4173,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3855,c_1898,c_2624,c_2736,c_3269,c_3824])).

cnf(c_2631,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2624,c_1898])).

cnf(c_2635,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2631])).

cnf(c_4189,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4173,c_2635])).

cnf(c_4191,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4173,c_2736])).

cnf(c_4241,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4191])).

cnf(c_4250,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4189,c_4241])).

cnf(c_4251,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4250])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1517,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3156,plain,
    ( v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1517])).

cnf(c_4185,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4173,c_3156])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_110,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_990,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2056,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_2057,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2056])).

cnf(c_2059,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2057])).

cnf(c_2299,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3025,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2299])).

cnf(c_3026,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3025])).

cnf(c_4867,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4185,c_36,c_110,c_1898,c_2059,c_2624,c_2736,c_3026,c_3269,c_3824])).

cnf(c_1525,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1524,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2451,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_1524])).

cnf(c_4872,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4867,c_2451])).

cnf(c_21,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1514,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3155,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_1517])).

cnf(c_4093,plain,
    ( k6_partfun1(X0) = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_1524])).

cnf(c_5153,plain,
    ( k6_partfun1(k1_xboole_0) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_4093])).

cnf(c_6056,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1525,c_5153])).

cnf(c_9,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_6668,plain,
    ( k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6056,c_9])).

cnf(c_6669,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6668,c_6056])).

cnf(c_7164,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4251,c_4872,c_6669])).

cnf(c_4193,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4173,c_2624])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_25])).

cnf(c_364,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_1510,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_4894,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4193,c_1510])).

cnf(c_1829,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_1830,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1829])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1883,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5170,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4894,c_34,c_31,c_36,c_1810,c_1811,c_1830,c_1883,c_1898,c_2624,c_2647,c_2736,c_3269,c_3824])).

cnf(c_5415,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4872,c_5170])).

cnf(c_1511,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5429,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4872,c_1511])).

cnf(c_1521,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | k1_relset_1(X1,X2,X0) = X1
    | k2_relat_1(X3) != X2
    | k1_relat_1(X3) != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_23])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_596,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_22])).

cnf(c_1501,plain,
    ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_3041,plain,
    ( k1_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k1_relat_1(k2_funct_1(X0))
    | k2_relat_1(k2_funct_1(X0)) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_1501])).

cnf(c_92,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5568,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k2_relat_1(k2_funct_1(X0)) = k1_xboole_0
    | k1_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k1_relat_1(k2_funct_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3041,c_92])).

cnf(c_5569,plain,
    ( k1_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k1_relat_1(k2_funct_1(X0))
    | k2_relat_1(k2_funct_1(X0)) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5568])).

cnf(c_5584,plain,
    ( k1_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5429,c_5569])).

cnf(c_54,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1805,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_relat_1(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1807,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_relat_1(k6_partfun1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1805])).

cnf(c_993,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2172,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_2184,plain,
    ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
    | v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2172])).

cnf(c_2399,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k6_partfun1(X1))
    | X0 = k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2401,plain,
    ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2399])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2706,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2708,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2706])).

cnf(c_5592,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5584])).

cnf(c_6477,plain,
    ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k1_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5584,c_54,c_0,c_1807,c_2184,c_2401,c_2708,c_5592])).

cnf(c_6478,plain,
    ( k1_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6477])).

cnf(c_5428,plain,
    ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4872,c_1819])).

cnf(c_6479,plain,
    ( k1_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k1_xboole_0),k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6478,c_5428])).

cnf(c_6480,plain,
    ( k1_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k1_xboole_0),k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0))
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6479,c_5428])).

cnf(c_102,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5420,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4872,c_4193])).

cnf(c_6483,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6480,c_54,c_102,c_0,c_1807,c_2184,c_2401,c_2708,c_5420])).

cnf(c_6821,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5415,c_6483])).

cnf(c_7166,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7164,c_6821])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n002.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 16:00:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.80/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.04  
% 2.80/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/1.04  
% 2.80/1.04  ------  iProver source info
% 2.80/1.04  
% 2.80/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.80/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/1.04  git: non_committed_changes: false
% 2.80/1.04  git: last_make_outside_of_git: false
% 2.80/1.04  
% 2.80/1.04  ------ 
% 2.80/1.04  
% 2.80/1.04  ------ Input Options
% 2.80/1.04  
% 2.80/1.04  --out_options                           all
% 2.80/1.04  --tptp_safe_out                         true
% 2.80/1.04  --problem_path                          ""
% 2.80/1.04  --include_path                          ""
% 2.80/1.04  --clausifier                            res/vclausify_rel
% 2.80/1.04  --clausifier_options                    --mode clausify
% 2.80/1.04  --stdin                                 false
% 2.80/1.04  --stats_out                             all
% 2.80/1.04  
% 2.80/1.04  ------ General Options
% 2.80/1.04  
% 2.80/1.04  --fof                                   false
% 2.80/1.04  --time_out_real                         305.
% 2.80/1.04  --time_out_virtual                      -1.
% 2.80/1.04  --symbol_type_check                     false
% 2.80/1.04  --clausify_out                          false
% 2.80/1.04  --sig_cnt_out                           false
% 2.80/1.04  --trig_cnt_out                          false
% 2.80/1.04  --trig_cnt_out_tolerance                1.
% 2.80/1.04  --trig_cnt_out_sk_spl                   false
% 2.80/1.04  --abstr_cl_out                          false
% 2.80/1.04  
% 2.80/1.04  ------ Global Options
% 2.80/1.04  
% 2.80/1.04  --schedule                              default
% 2.80/1.04  --add_important_lit                     false
% 2.80/1.04  --prop_solver_per_cl                    1000
% 2.80/1.04  --min_unsat_core                        false
% 2.80/1.04  --soft_assumptions                      false
% 2.80/1.04  --soft_lemma_size                       3
% 2.80/1.04  --prop_impl_unit_size                   0
% 2.80/1.04  --prop_impl_unit                        []
% 2.80/1.04  --share_sel_clauses                     true
% 2.80/1.04  --reset_solvers                         false
% 2.80/1.04  --bc_imp_inh                            [conj_cone]
% 2.80/1.04  --conj_cone_tolerance                   3.
% 2.80/1.04  --extra_neg_conj                        none
% 2.80/1.04  --large_theory_mode                     true
% 2.80/1.04  --prolific_symb_bound                   200
% 2.80/1.04  --lt_threshold                          2000
% 2.80/1.04  --clause_weak_htbl                      true
% 2.80/1.04  --gc_record_bc_elim                     false
% 2.80/1.04  
% 2.80/1.04  ------ Preprocessing Options
% 2.80/1.04  
% 2.80/1.04  --preprocessing_flag                    true
% 2.80/1.04  --time_out_prep_mult                    0.1
% 2.80/1.04  --splitting_mode                        input
% 2.80/1.04  --splitting_grd                         true
% 2.80/1.04  --splitting_cvd                         false
% 2.80/1.04  --splitting_cvd_svl                     false
% 2.80/1.04  --splitting_nvd                         32
% 2.80/1.04  --sub_typing                            true
% 2.80/1.04  --prep_gs_sim                           true
% 2.80/1.04  --prep_unflatten                        true
% 2.80/1.04  --prep_res_sim                          true
% 2.80/1.04  --prep_upred                            true
% 2.80/1.04  --prep_sem_filter                       exhaustive
% 2.80/1.04  --prep_sem_filter_out                   false
% 2.80/1.04  --pred_elim                             true
% 2.80/1.04  --res_sim_input                         true
% 2.80/1.04  --eq_ax_congr_red                       true
% 2.80/1.04  --pure_diseq_elim                       true
% 2.80/1.04  --brand_transform                       false
% 2.80/1.04  --non_eq_to_eq                          false
% 2.80/1.04  --prep_def_merge                        true
% 2.80/1.04  --prep_def_merge_prop_impl              false
% 2.80/1.04  --prep_def_merge_mbd                    true
% 2.80/1.04  --prep_def_merge_tr_red                 false
% 2.80/1.04  --prep_def_merge_tr_cl                  false
% 2.80/1.04  --smt_preprocessing                     true
% 2.80/1.04  --smt_ac_axioms                         fast
% 2.80/1.04  --preprocessed_out                      false
% 2.80/1.04  --preprocessed_stats                    false
% 2.80/1.04  
% 2.80/1.04  ------ Abstraction refinement Options
% 2.80/1.04  
% 2.80/1.04  --abstr_ref                             []
% 2.80/1.04  --abstr_ref_prep                        false
% 2.80/1.04  --abstr_ref_until_sat                   false
% 2.80/1.04  --abstr_ref_sig_restrict                funpre
% 2.80/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/1.04  --abstr_ref_under                       []
% 2.80/1.04  
% 2.80/1.04  ------ SAT Options
% 2.80/1.04  
% 2.80/1.04  --sat_mode                              false
% 2.80/1.04  --sat_fm_restart_options                ""
% 2.80/1.04  --sat_gr_def                            false
% 2.80/1.04  --sat_epr_types                         true
% 2.80/1.04  --sat_non_cyclic_types                  false
% 2.80/1.04  --sat_finite_models                     false
% 2.80/1.04  --sat_fm_lemmas                         false
% 2.80/1.04  --sat_fm_prep                           false
% 2.80/1.04  --sat_fm_uc_incr                        true
% 2.80/1.04  --sat_out_model                         small
% 2.80/1.04  --sat_out_clauses                       false
% 2.80/1.04  
% 2.80/1.04  ------ QBF Options
% 2.80/1.04  
% 2.80/1.04  --qbf_mode                              false
% 2.80/1.04  --qbf_elim_univ                         false
% 2.80/1.04  --qbf_dom_inst                          none
% 2.80/1.04  --qbf_dom_pre_inst                      false
% 2.80/1.04  --qbf_sk_in                             false
% 2.80/1.04  --qbf_pred_elim                         true
% 2.80/1.04  --qbf_split                             512
% 2.80/1.04  
% 2.80/1.04  ------ BMC1 Options
% 2.80/1.04  
% 2.80/1.04  --bmc1_incremental                      false
% 2.80/1.04  --bmc1_axioms                           reachable_all
% 2.80/1.04  --bmc1_min_bound                        0
% 2.80/1.04  --bmc1_max_bound                        -1
% 2.80/1.04  --bmc1_max_bound_default                -1
% 2.80/1.04  --bmc1_symbol_reachability              true
% 2.80/1.04  --bmc1_property_lemmas                  false
% 2.80/1.04  --bmc1_k_induction                      false
% 2.80/1.04  --bmc1_non_equiv_states                 false
% 2.80/1.04  --bmc1_deadlock                         false
% 2.80/1.04  --bmc1_ucm                              false
% 2.80/1.04  --bmc1_add_unsat_core                   none
% 2.80/1.04  --bmc1_unsat_core_children              false
% 2.80/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/1.04  --bmc1_out_stat                         full
% 2.80/1.04  --bmc1_ground_init                      false
% 2.80/1.04  --bmc1_pre_inst_next_state              false
% 2.80/1.04  --bmc1_pre_inst_state                   false
% 2.80/1.04  --bmc1_pre_inst_reach_state             false
% 2.80/1.04  --bmc1_out_unsat_core                   false
% 2.80/1.04  --bmc1_aig_witness_out                  false
% 2.80/1.04  --bmc1_verbose                          false
% 2.80/1.04  --bmc1_dump_clauses_tptp                false
% 2.80/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.80/1.04  --bmc1_dump_file                        -
% 2.80/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.80/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.80/1.04  --bmc1_ucm_extend_mode                  1
% 2.80/1.04  --bmc1_ucm_init_mode                    2
% 2.80/1.04  --bmc1_ucm_cone_mode                    none
% 2.80/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.80/1.04  --bmc1_ucm_relax_model                  4
% 2.80/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.80/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/1.04  --bmc1_ucm_layered_model                none
% 2.80/1.04  --bmc1_ucm_max_lemma_size               10
% 2.80/1.04  
% 2.80/1.04  ------ AIG Options
% 2.80/1.04  
% 2.80/1.04  --aig_mode                              false
% 2.80/1.04  
% 2.80/1.04  ------ Instantiation Options
% 2.80/1.04  
% 2.80/1.04  --instantiation_flag                    true
% 2.80/1.04  --inst_sos_flag                         false
% 2.80/1.04  --inst_sos_phase                        true
% 2.80/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/1.04  --inst_lit_sel_side                     num_symb
% 2.80/1.04  --inst_solver_per_active                1400
% 2.80/1.04  --inst_solver_calls_frac                1.
% 2.80/1.04  --inst_passive_queue_type               priority_queues
% 2.80/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/1.04  --inst_passive_queues_freq              [25;2]
% 2.80/1.04  --inst_dismatching                      true
% 2.80/1.04  --inst_eager_unprocessed_to_passive     true
% 2.80/1.04  --inst_prop_sim_given                   true
% 2.80/1.04  --inst_prop_sim_new                     false
% 2.80/1.04  --inst_subs_new                         false
% 2.80/1.04  --inst_eq_res_simp                      false
% 2.80/1.04  --inst_subs_given                       false
% 2.80/1.04  --inst_orphan_elimination               true
% 2.80/1.04  --inst_learning_loop_flag               true
% 2.80/1.04  --inst_learning_start                   3000
% 2.80/1.04  --inst_learning_factor                  2
% 2.80/1.04  --inst_start_prop_sim_after_learn       3
% 2.80/1.04  --inst_sel_renew                        solver
% 2.80/1.04  --inst_lit_activity_flag                true
% 2.80/1.04  --inst_restr_to_given                   false
% 2.80/1.04  --inst_activity_threshold               500
% 2.80/1.04  --inst_out_proof                        true
% 2.80/1.04  
% 2.80/1.04  ------ Resolution Options
% 2.80/1.04  
% 2.80/1.04  --resolution_flag                       true
% 2.80/1.04  --res_lit_sel                           adaptive
% 2.80/1.04  --res_lit_sel_side                      none
% 2.80/1.04  --res_ordering                          kbo
% 2.80/1.04  --res_to_prop_solver                    active
% 2.80/1.04  --res_prop_simpl_new                    false
% 2.80/1.04  --res_prop_simpl_given                  true
% 2.80/1.04  --res_passive_queue_type                priority_queues
% 2.80/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/1.04  --res_passive_queues_freq               [15;5]
% 2.80/1.04  --res_forward_subs                      full
% 2.80/1.04  --res_backward_subs                     full
% 2.80/1.04  --res_forward_subs_resolution           true
% 2.80/1.04  --res_backward_subs_resolution          true
% 2.80/1.04  --res_orphan_elimination                true
% 2.80/1.04  --res_time_limit                        2.
% 2.80/1.04  --res_out_proof                         true
% 2.80/1.04  
% 2.80/1.04  ------ Superposition Options
% 2.80/1.04  
% 2.80/1.04  --superposition_flag                    true
% 2.80/1.04  --sup_passive_queue_type                priority_queues
% 2.80/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.80/1.04  --demod_completeness_check              fast
% 2.80/1.04  --demod_use_ground                      true
% 2.80/1.04  --sup_to_prop_solver                    passive
% 2.80/1.04  --sup_prop_simpl_new                    true
% 2.80/1.04  --sup_prop_simpl_given                  true
% 2.80/1.04  --sup_fun_splitting                     false
% 2.80/1.04  --sup_smt_interval                      50000
% 2.80/1.04  
% 2.80/1.04  ------ Superposition Simplification Setup
% 2.80/1.04  
% 2.80/1.04  --sup_indices_passive                   []
% 2.80/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.04  --sup_full_bw                           [BwDemod]
% 2.80/1.04  --sup_immed_triv                        [TrivRules]
% 2.80/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.04  --sup_immed_bw_main                     []
% 2.80/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.04  
% 2.80/1.04  ------ Combination Options
% 2.80/1.04  
% 2.80/1.04  --comb_res_mult                         3
% 2.80/1.04  --comb_sup_mult                         2
% 2.80/1.04  --comb_inst_mult                        10
% 2.80/1.04  
% 2.80/1.04  ------ Debug Options
% 2.80/1.04  
% 2.80/1.04  --dbg_backtrace                         false
% 2.80/1.04  --dbg_dump_prop_clauses                 false
% 2.80/1.04  --dbg_dump_prop_clauses_file            -
% 2.80/1.04  --dbg_out_stat                          false
% 2.80/1.04  ------ Parsing...
% 2.80/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/1.04  
% 2.80/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.80/1.04  
% 2.80/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/1.04  
% 2.80/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/1.04  ------ Proving...
% 2.80/1.04  ------ Problem Properties 
% 2.80/1.04  
% 2.80/1.04  
% 2.80/1.04  clauses                                 33
% 2.80/1.04  conjectures                             3
% 2.80/1.04  EPR                                     3
% 2.80/1.04  Horn                                    28
% 2.80/1.04  unary                                   6
% 2.80/1.04  binary                                  6
% 2.80/1.04  lits                                    98
% 2.80/1.04  lits eq                                 42
% 2.80/1.04  fd_pure                                 0
% 2.80/1.04  fd_pseudo                               0
% 2.80/1.04  fd_cond                                 2
% 2.80/1.04  fd_pseudo_cond                          1
% 2.80/1.04  AC symbols                              0
% 2.80/1.04  
% 2.80/1.04  ------ Schedule dynamic 5 is on 
% 2.80/1.04  
% 2.80/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.80/1.04  
% 2.80/1.04  
% 2.80/1.04  ------ 
% 2.80/1.04  Current options:
% 2.80/1.04  ------ 
% 2.80/1.04  
% 2.80/1.04  ------ Input Options
% 2.80/1.04  
% 2.80/1.04  --out_options                           all
% 2.80/1.04  --tptp_safe_out                         true
% 2.80/1.04  --problem_path                          ""
% 2.80/1.04  --include_path                          ""
% 2.80/1.04  --clausifier                            res/vclausify_rel
% 2.80/1.04  --clausifier_options                    --mode clausify
% 2.80/1.04  --stdin                                 false
% 2.80/1.04  --stats_out                             all
% 2.80/1.04  
% 2.80/1.04  ------ General Options
% 2.80/1.04  
% 2.80/1.04  --fof                                   false
% 2.80/1.04  --time_out_real                         305.
% 2.80/1.04  --time_out_virtual                      -1.
% 2.80/1.04  --symbol_type_check                     false
% 2.80/1.04  --clausify_out                          false
% 2.80/1.04  --sig_cnt_out                           false
% 2.80/1.04  --trig_cnt_out                          false
% 2.80/1.04  --trig_cnt_out_tolerance                1.
% 2.80/1.04  --trig_cnt_out_sk_spl                   false
% 2.80/1.04  --abstr_cl_out                          false
% 2.80/1.04  
% 2.80/1.04  ------ Global Options
% 2.80/1.04  
% 2.80/1.04  --schedule                              default
% 2.80/1.04  --add_important_lit                     false
% 2.80/1.04  --prop_solver_per_cl                    1000
% 2.80/1.04  --min_unsat_core                        false
% 2.80/1.04  --soft_assumptions                      false
% 2.80/1.04  --soft_lemma_size                       3
% 2.80/1.04  --prop_impl_unit_size                   0
% 2.80/1.04  --prop_impl_unit                        []
% 2.80/1.04  --share_sel_clauses                     true
% 2.80/1.04  --reset_solvers                         false
% 2.80/1.04  --bc_imp_inh                            [conj_cone]
% 2.80/1.04  --conj_cone_tolerance                   3.
% 2.80/1.04  --extra_neg_conj                        none
% 2.80/1.04  --large_theory_mode                     true
% 2.80/1.04  --prolific_symb_bound                   200
% 2.80/1.04  --lt_threshold                          2000
% 2.80/1.04  --clause_weak_htbl                      true
% 2.80/1.04  --gc_record_bc_elim                     false
% 2.80/1.04  
% 2.80/1.04  ------ Preprocessing Options
% 2.80/1.04  
% 2.80/1.04  --preprocessing_flag                    true
% 2.80/1.04  --time_out_prep_mult                    0.1
% 2.80/1.04  --splitting_mode                        input
% 2.80/1.04  --splitting_grd                         true
% 2.80/1.04  --splitting_cvd                         false
% 2.80/1.04  --splitting_cvd_svl                     false
% 2.80/1.04  --splitting_nvd                         32
% 2.80/1.04  --sub_typing                            true
% 2.80/1.04  --prep_gs_sim                           true
% 2.80/1.04  --prep_unflatten                        true
% 2.80/1.04  --prep_res_sim                          true
% 2.80/1.04  --prep_upred                            true
% 2.80/1.04  --prep_sem_filter                       exhaustive
% 2.80/1.04  --prep_sem_filter_out                   false
% 2.80/1.04  --pred_elim                             true
% 2.80/1.04  --res_sim_input                         true
% 2.80/1.04  --eq_ax_congr_red                       true
% 2.80/1.04  --pure_diseq_elim                       true
% 2.80/1.04  --brand_transform                       false
% 2.80/1.04  --non_eq_to_eq                          false
% 2.80/1.04  --prep_def_merge                        true
% 2.80/1.04  --prep_def_merge_prop_impl              false
% 2.80/1.04  --prep_def_merge_mbd                    true
% 2.80/1.04  --prep_def_merge_tr_red                 false
% 2.80/1.04  --prep_def_merge_tr_cl                  false
% 2.80/1.04  --smt_preprocessing                     true
% 2.80/1.04  --smt_ac_axioms                         fast
% 2.80/1.04  --preprocessed_out                      false
% 2.80/1.04  --preprocessed_stats                    false
% 2.80/1.04  
% 2.80/1.04  ------ Abstraction refinement Options
% 2.80/1.04  
% 2.80/1.04  --abstr_ref                             []
% 2.80/1.04  --abstr_ref_prep                        false
% 2.80/1.04  --abstr_ref_until_sat                   false
% 2.80/1.04  --abstr_ref_sig_restrict                funpre
% 2.80/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/1.04  --abstr_ref_under                       []
% 2.80/1.04  
% 2.80/1.04  ------ SAT Options
% 2.80/1.04  
% 2.80/1.04  --sat_mode                              false
% 2.80/1.04  --sat_fm_restart_options                ""
% 2.80/1.04  --sat_gr_def                            false
% 2.80/1.04  --sat_epr_types                         true
% 2.80/1.04  --sat_non_cyclic_types                  false
% 2.80/1.04  --sat_finite_models                     false
% 2.80/1.04  --sat_fm_lemmas                         false
% 2.80/1.04  --sat_fm_prep                           false
% 2.80/1.04  --sat_fm_uc_incr                        true
% 2.80/1.04  --sat_out_model                         small
% 2.80/1.04  --sat_out_clauses                       false
% 2.80/1.04  
% 2.80/1.04  ------ QBF Options
% 2.80/1.04  
% 2.80/1.04  --qbf_mode                              false
% 2.80/1.04  --qbf_elim_univ                         false
% 2.80/1.04  --qbf_dom_inst                          none
% 2.80/1.04  --qbf_dom_pre_inst                      false
% 2.80/1.04  --qbf_sk_in                             false
% 2.80/1.04  --qbf_pred_elim                         true
% 2.80/1.04  --qbf_split                             512
% 2.80/1.04  
% 2.80/1.04  ------ BMC1 Options
% 2.80/1.04  
% 2.80/1.04  --bmc1_incremental                      false
% 2.80/1.04  --bmc1_axioms                           reachable_all
% 2.80/1.04  --bmc1_min_bound                        0
% 2.80/1.04  --bmc1_max_bound                        -1
% 2.80/1.04  --bmc1_max_bound_default                -1
% 2.80/1.04  --bmc1_symbol_reachability              true
% 2.80/1.04  --bmc1_property_lemmas                  false
% 2.80/1.04  --bmc1_k_induction                      false
% 2.80/1.04  --bmc1_non_equiv_states                 false
% 2.80/1.04  --bmc1_deadlock                         false
% 2.80/1.04  --bmc1_ucm                              false
% 2.80/1.04  --bmc1_add_unsat_core                   none
% 2.80/1.04  --bmc1_unsat_core_children              false
% 2.80/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/1.04  --bmc1_out_stat                         full
% 2.80/1.04  --bmc1_ground_init                      false
% 2.80/1.04  --bmc1_pre_inst_next_state              false
% 2.80/1.04  --bmc1_pre_inst_state                   false
% 2.80/1.04  --bmc1_pre_inst_reach_state             false
% 2.80/1.04  --bmc1_out_unsat_core                   false
% 2.80/1.04  --bmc1_aig_witness_out                  false
% 2.80/1.04  --bmc1_verbose                          false
% 2.80/1.04  --bmc1_dump_clauses_tptp                false
% 2.80/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.80/1.04  --bmc1_dump_file                        -
% 2.80/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.80/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.80/1.04  --bmc1_ucm_extend_mode                  1
% 2.80/1.04  --bmc1_ucm_init_mode                    2
% 2.80/1.04  --bmc1_ucm_cone_mode                    none
% 2.80/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.80/1.04  --bmc1_ucm_relax_model                  4
% 2.80/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.80/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/1.04  --bmc1_ucm_layered_model                none
% 2.80/1.04  --bmc1_ucm_max_lemma_size               10
% 2.80/1.04  
% 2.80/1.04  ------ AIG Options
% 2.80/1.04  
% 2.80/1.04  --aig_mode                              false
% 2.80/1.04  
% 2.80/1.04  ------ Instantiation Options
% 2.80/1.04  
% 2.80/1.04  --instantiation_flag                    true
% 2.80/1.04  --inst_sos_flag                         false
% 2.80/1.04  --inst_sos_phase                        true
% 2.80/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/1.04  --inst_lit_sel_side                     none
% 2.80/1.04  --inst_solver_per_active                1400
% 2.80/1.04  --inst_solver_calls_frac                1.
% 2.80/1.04  --inst_passive_queue_type               priority_queues
% 2.80/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/1.04  --inst_passive_queues_freq              [25;2]
% 2.80/1.04  --inst_dismatching                      true
% 2.80/1.04  --inst_eager_unprocessed_to_passive     true
% 2.80/1.04  --inst_prop_sim_given                   true
% 2.80/1.04  --inst_prop_sim_new                     false
% 2.80/1.04  --inst_subs_new                         false
% 2.80/1.04  --inst_eq_res_simp                      false
% 2.80/1.04  --inst_subs_given                       false
% 2.80/1.04  --inst_orphan_elimination               true
% 2.80/1.04  --inst_learning_loop_flag               true
% 2.80/1.04  --inst_learning_start                   3000
% 2.80/1.04  --inst_learning_factor                  2
% 2.80/1.04  --inst_start_prop_sim_after_learn       3
% 2.80/1.04  --inst_sel_renew                        solver
% 2.80/1.04  --inst_lit_activity_flag                true
% 2.80/1.04  --inst_restr_to_given                   false
% 2.80/1.04  --inst_activity_threshold               500
% 2.80/1.04  --inst_out_proof                        true
% 2.80/1.04  
% 2.80/1.04  ------ Resolution Options
% 2.80/1.04  
% 2.80/1.04  --resolution_flag                       false
% 2.80/1.04  --res_lit_sel                           adaptive
% 2.80/1.04  --res_lit_sel_side                      none
% 2.80/1.04  --res_ordering                          kbo
% 2.80/1.04  --res_to_prop_solver                    active
% 2.80/1.04  --res_prop_simpl_new                    false
% 2.80/1.04  --res_prop_simpl_given                  true
% 2.80/1.04  --res_passive_queue_type                priority_queues
% 2.80/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/1.04  --res_passive_queues_freq               [15;5]
% 2.80/1.04  --res_forward_subs                      full
% 2.80/1.04  --res_backward_subs                     full
% 2.80/1.04  --res_forward_subs_resolution           true
% 2.80/1.04  --res_backward_subs_resolution          true
% 2.80/1.04  --res_orphan_elimination                true
% 2.80/1.04  --res_time_limit                        2.
% 2.80/1.04  --res_out_proof                         true
% 2.80/1.04  
% 2.80/1.04  ------ Superposition Options
% 2.80/1.04  
% 2.80/1.04  --superposition_flag                    true
% 2.80/1.04  --sup_passive_queue_type                priority_queues
% 2.80/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.80/1.04  --demod_completeness_check              fast
% 2.80/1.04  --demod_use_ground                      true
% 2.80/1.04  --sup_to_prop_solver                    passive
% 2.80/1.04  --sup_prop_simpl_new                    true
% 2.80/1.04  --sup_prop_simpl_given                  true
% 2.80/1.04  --sup_fun_splitting                     false
% 2.80/1.04  --sup_smt_interval                      50000
% 2.80/1.04  
% 2.80/1.04  ------ Superposition Simplification Setup
% 2.80/1.04  
% 2.80/1.04  --sup_indices_passive                   []
% 2.80/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.04  --sup_full_bw                           [BwDemod]
% 2.80/1.04  --sup_immed_triv                        [TrivRules]
% 2.80/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.04  --sup_immed_bw_main                     []
% 2.80/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.04  
% 2.80/1.04  ------ Combination Options
% 2.80/1.04  
% 2.80/1.04  --comb_res_mult                         3
% 2.80/1.04  --comb_sup_mult                         2
% 2.80/1.04  --comb_inst_mult                        10
% 2.80/1.04  
% 2.80/1.04  ------ Debug Options
% 2.80/1.04  
% 2.80/1.04  --dbg_backtrace                         false
% 2.80/1.04  --dbg_dump_prop_clauses                 false
% 2.80/1.04  --dbg_dump_prop_clauses_file            -
% 2.80/1.04  --dbg_out_stat                          false
% 2.80/1.04  
% 2.80/1.04  
% 2.80/1.04  
% 2.80/1.04  
% 2.80/1.04  ------ Proving...
% 2.80/1.04  
% 2.80/1.04  
% 2.80/1.04  % SZS status Theorem for theBenchmark.p
% 2.80/1.04  
% 2.80/1.04   Resolution empty clause
% 2.80/1.04  
% 2.80/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/1.04  
% 2.80/1.04  fof(f13,axiom,(
% 2.80/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f32,plain,(
% 2.80/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/1.04    inference(ennf_transformation,[],[f13])).
% 2.80/1.04  
% 2.80/1.04  fof(f33,plain,(
% 2.80/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/1.04    inference(flattening,[],[f32])).
% 2.80/1.04  
% 2.80/1.04  fof(f41,plain,(
% 2.80/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/1.04    inference(nnf_transformation,[],[f33])).
% 2.80/1.04  
% 2.80/1.04  fof(f59,plain,(
% 2.80/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/1.04    inference(cnf_transformation,[],[f41])).
% 2.80/1.04  
% 2.80/1.04  fof(f18,conjecture,(
% 2.80/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f19,negated_conjecture,(
% 2.80/1.04    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.80/1.04    inference(negated_conjecture,[],[f18])).
% 2.80/1.04  
% 2.80/1.04  fof(f38,plain,(
% 2.80/1.04    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.80/1.04    inference(ennf_transformation,[],[f19])).
% 2.80/1.04  
% 2.80/1.04  fof(f39,plain,(
% 2.80/1.04    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.80/1.04    inference(flattening,[],[f38])).
% 2.80/1.04  
% 2.80/1.04  fof(f42,plain,(
% 2.80/1.04    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.80/1.04    introduced(choice_axiom,[])).
% 2.80/1.04  
% 2.80/1.04  fof(f43,plain,(
% 2.80/1.04    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.80/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42])).
% 2.80/1.04  
% 2.80/1.04  fof(f74,plain,(
% 2.80/1.04    v1_funct_2(sK2,sK0,sK1)),
% 2.80/1.04    inference(cnf_transformation,[],[f43])).
% 2.80/1.04  
% 2.80/1.04  fof(f75,plain,(
% 2.80/1.04    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.80/1.04    inference(cnf_transformation,[],[f43])).
% 2.80/1.04  
% 2.80/1.04  fof(f11,axiom,(
% 2.80/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f30,plain,(
% 2.80/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/1.04    inference(ennf_transformation,[],[f11])).
% 2.80/1.04  
% 2.80/1.04  fof(f57,plain,(
% 2.80/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/1.04    inference(cnf_transformation,[],[f30])).
% 2.80/1.04  
% 2.80/1.04  fof(f6,axiom,(
% 2.80/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f25,plain,(
% 2.80/1.04    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.80/1.04    inference(ennf_transformation,[],[f6])).
% 2.80/1.04  
% 2.80/1.04  fof(f26,plain,(
% 2.80/1.04    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.80/1.04    inference(flattening,[],[f25])).
% 2.80/1.04  
% 2.80/1.04  fof(f52,plain,(
% 2.80/1.04    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f26])).
% 2.80/1.04  
% 2.80/1.04  fof(f76,plain,(
% 2.80/1.04    v2_funct_1(sK2)),
% 2.80/1.04    inference(cnf_transformation,[],[f43])).
% 2.80/1.04  
% 2.80/1.04  fof(f73,plain,(
% 2.80/1.04    v1_funct_1(sK2)),
% 2.80/1.04    inference(cnf_transformation,[],[f43])).
% 2.80/1.04  
% 2.80/1.04  fof(f8,axiom,(
% 2.80/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f27,plain,(
% 2.80/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/1.04    inference(ennf_transformation,[],[f8])).
% 2.80/1.04  
% 2.80/1.04  fof(f54,plain,(
% 2.80/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/1.04    inference(cnf_transformation,[],[f27])).
% 2.80/1.04  
% 2.80/1.04  fof(f16,axiom,(
% 2.80/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f34,plain,(
% 2.80/1.04    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.80/1.04    inference(ennf_transformation,[],[f16])).
% 2.80/1.04  
% 2.80/1.04  fof(f35,plain,(
% 2.80/1.04    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.80/1.04    inference(flattening,[],[f34])).
% 2.80/1.04  
% 2.80/1.04  fof(f69,plain,(
% 2.80/1.04    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f35])).
% 2.80/1.04  
% 2.80/1.04  fof(f12,axiom,(
% 2.80/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f31,plain,(
% 2.80/1.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/1.04    inference(ennf_transformation,[],[f12])).
% 2.80/1.04  
% 2.80/1.04  fof(f58,plain,(
% 2.80/1.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/1.04    inference(cnf_transformation,[],[f31])).
% 2.80/1.04  
% 2.80/1.04  fof(f77,plain,(
% 2.80/1.04    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.80/1.04    inference(cnf_transformation,[],[f43])).
% 2.80/1.04  
% 2.80/1.04  fof(f51,plain,(
% 2.80/1.04    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f26])).
% 2.80/1.04  
% 2.80/1.04  fof(f5,axiom,(
% 2.80/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f23,plain,(
% 2.80/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.80/1.04    inference(ennf_transformation,[],[f5])).
% 2.80/1.04  
% 2.80/1.04  fof(f24,plain,(
% 2.80/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.80/1.04    inference(flattening,[],[f23])).
% 2.80/1.04  
% 2.80/1.04  fof(f50,plain,(
% 2.80/1.04    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f24])).
% 2.80/1.04  
% 2.80/1.04  fof(f49,plain,(
% 2.80/1.04    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f24])).
% 2.80/1.04  
% 2.80/1.04  fof(f68,plain,(
% 2.80/1.04    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f35])).
% 2.80/1.04  
% 2.80/1.04  fof(f78,plain,(
% 2.80/1.04    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.80/1.04    inference(cnf_transformation,[],[f43])).
% 2.80/1.04  
% 2.80/1.04  fof(f2,axiom,(
% 2.80/1.04    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f45,plain,(
% 2.80/1.04    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f2])).
% 2.80/1.04  
% 2.80/1.04  fof(f17,axiom,(
% 2.80/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f36,plain,(
% 2.80/1.04    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.80/1.04    inference(ennf_transformation,[],[f17])).
% 2.80/1.04  
% 2.80/1.04  fof(f37,plain,(
% 2.80/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.80/1.04    inference(flattening,[],[f36])).
% 2.80/1.04  
% 2.80/1.04  fof(f71,plain,(
% 2.80/1.04    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f37])).
% 2.80/1.04  
% 2.80/1.04  fof(f4,axiom,(
% 2.80/1.04    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f22,plain,(
% 2.80/1.04    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.80/1.04    inference(ennf_transformation,[],[f4])).
% 2.80/1.04  
% 2.80/1.04  fof(f40,plain,(
% 2.80/1.04    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.80/1.04    inference(nnf_transformation,[],[f22])).
% 2.80/1.04  
% 2.80/1.04  fof(f48,plain,(
% 2.80/1.04    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f40])).
% 2.80/1.04  
% 2.80/1.04  fof(f10,axiom,(
% 2.80/1.04    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f29,plain,(
% 2.80/1.04    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.80/1.04    inference(ennf_transformation,[],[f10])).
% 2.80/1.04  
% 2.80/1.04  fof(f56,plain,(
% 2.80/1.04    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f29])).
% 2.80/1.04  
% 2.80/1.04  fof(f1,axiom,(
% 2.80/1.04    v1_xboole_0(k1_xboole_0)),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f44,plain,(
% 2.80/1.04    v1_xboole_0(k1_xboole_0)),
% 2.80/1.04    inference(cnf_transformation,[],[f1])).
% 2.80/1.04  
% 2.80/1.04  fof(f3,axiom,(
% 2.80/1.04    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f21,plain,(
% 2.80/1.04    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.80/1.04    inference(ennf_transformation,[],[f3])).
% 2.80/1.04  
% 2.80/1.04  fof(f46,plain,(
% 2.80/1.04    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f21])).
% 2.80/1.04  
% 2.80/1.04  fof(f14,axiom,(
% 2.80/1.04    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f20,plain,(
% 2.80/1.04    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.80/1.04    inference(pure_predicate_removal,[],[f14])).
% 2.80/1.04  
% 2.80/1.04  fof(f65,plain,(
% 2.80/1.04    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.80/1.04    inference(cnf_transformation,[],[f20])).
% 2.80/1.04  
% 2.80/1.04  fof(f7,axiom,(
% 2.80/1.04    ! [X0] : k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0)),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f53,plain,(
% 2.80/1.04    ( ! [X0] : (k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f7])).
% 2.80/1.04  
% 2.80/1.04  fof(f15,axiom,(
% 2.80/1.04    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f66,plain,(
% 2.80/1.04    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f15])).
% 2.80/1.04  
% 2.80/1.04  fof(f79,plain,(
% 2.80/1.04    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 2.80/1.04    inference(definition_unfolding,[],[f53,f66,f66])).
% 2.80/1.04  
% 2.80/1.04  fof(f72,plain,(
% 2.80/1.04    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f37])).
% 2.80/1.04  
% 2.80/1.04  fof(f47,plain,(
% 2.80/1.04    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f40])).
% 2.80/1.04  
% 2.80/1.04  fof(f9,axiom,(
% 2.80/1.04    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.80/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.04  
% 2.80/1.04  fof(f28,plain,(
% 2.80/1.04    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.80/1.04    inference(ennf_transformation,[],[f9])).
% 2.80/1.04  
% 2.80/1.04  fof(f55,plain,(
% 2.80/1.04    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.80/1.04    inference(cnf_transformation,[],[f28])).
% 2.80/1.04  
% 2.80/1.04  cnf(c_20,plain,
% 2.80/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 2.80/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.04      | k1_relset_1(X1,X2,X0) = X1
% 2.80/1.04      | k1_xboole_0 = X2 ),
% 2.80/1.04      inference(cnf_transformation,[],[f59]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_32,negated_conjecture,
% 2.80/1.04      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.80/1.04      inference(cnf_transformation,[],[f74]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_658,plain,
% 2.80/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.04      | k1_relset_1(X1,X2,X0) = X1
% 2.80/1.04      | sK0 != X1
% 2.80/1.04      | sK1 != X2
% 2.80/1.04      | sK2 != X0
% 2.80/1.04      | k1_xboole_0 = X2 ),
% 2.80/1.04      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_659,plain,
% 2.80/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.80/1.04      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.80/1.04      | k1_xboole_0 = sK1 ),
% 2.80/1.04      inference(unflattening,[status(thm)],[c_658]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_31,negated_conjecture,
% 2.80/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.80/1.04      inference(cnf_transformation,[],[f75]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_661,plain,
% 2.80/1.04      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.80/1.04      inference(global_propositional_subsumption,[status(thm)],[c_659,c_31]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1512,plain,
% 2.80/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_13,plain,
% 2.80/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f57]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1516,plain,
% 2.80/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.80/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2997,plain,
% 2.80/1.04      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_1512,c_1516]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3170,plain,
% 2.80/1.04      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_661,c_2997]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_7,plain,
% 2.80/1.04      ( ~ v2_funct_1(X0)
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0)
% 2.80/1.04      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f52]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_30,negated_conjecture,
% 2.80/1.04      ( v2_funct_1(sK2) ),
% 2.80/1.04      inference(cnf_transformation,[],[f76]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_405,plain,
% 2.80/1.04      ( ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0)
% 2.80/1.04      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.80/1.04      | sK2 != X0 ),
% 2.80/1.04      inference(resolution_lifted,[status(thm)],[c_7,c_30]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_406,plain,
% 2.80/1.04      ( ~ v1_funct_1(sK2)
% 2.80/1.04      | ~ v1_relat_1(sK2)
% 2.80/1.04      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.80/1.04      inference(unflattening,[status(thm)],[c_405]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_33,negated_conjecture,
% 2.80/1.04      ( v1_funct_1(sK2) ),
% 2.80/1.04      inference(cnf_transformation,[],[f73]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_408,plain,
% 2.80/1.04      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.80/1.04      inference(global_propositional_subsumption,[status(thm)],[c_406,c_33]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1508,plain,
% 2.80/1.04      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.80/1.04      | v1_relat_1(sK2) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_10,plain,
% 2.80/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f54]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1810,plain,
% 2.80/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.80/1.04      | v1_relat_1(sK2) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_10]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1819,plain,
% 2.80/1.04      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.80/1.04      inference(global_propositional_subsumption,
% 2.80/1.04                [status(thm)],
% 2.80/1.04                [c_1508,c_33,c_31,c_406,c_1810]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_22,plain,
% 2.80/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f69]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1513,plain,
% 2.80/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.80/1.04      | v1_funct_1(X0) != iProver_top
% 2.80/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3516,plain,
% 2.80/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 2.80/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.80/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_1819,c_1513]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_14,plain,
% 2.80/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.04      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f58]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1515,plain,
% 2.80/1.04      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.80/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2622,plain,
% 2.80/1.04      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_1512,c_1515]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_29,negated_conjecture,
% 2.80/1.04      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.80/1.04      inference(cnf_transformation,[],[f77]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2624,plain,
% 2.80/1.04      ( k2_relat_1(sK2) = sK1 ),
% 2.80/1.04      inference(light_normalisation,[status(thm)],[c_2622,c_29]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_8,plain,
% 2.80/1.04      ( ~ v2_funct_1(X0)
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0)
% 2.80/1.04      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f51]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_391,plain,
% 2.80/1.04      ( ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0)
% 2.80/1.04      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.80/1.04      | sK2 != X0 ),
% 2.80/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_30]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_392,plain,
% 2.80/1.04      ( ~ v1_funct_1(sK2)
% 2.80/1.04      | ~ v1_relat_1(sK2)
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.80/1.04      inference(unflattening,[status(thm)],[c_391]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_394,plain,
% 2.80/1.04      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.80/1.04      inference(global_propositional_subsumption,[status(thm)],[c_392,c_33]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1509,plain,
% 2.80/1.04      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.80/1.04      | v1_relat_1(sK2) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1823,plain,
% 2.80/1.04      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.80/1.04      inference(global_propositional_subsumption,
% 2.80/1.04                [status(thm)],
% 2.80/1.04                [c_1509,c_33,c_31,c_392,c_1810]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2632,plain,
% 2.80/1.04      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 2.80/1.04      inference(demodulation,[status(thm)],[c_2624,c_1823]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3553,plain,
% 2.80/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.80/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.80/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.80/1.04      inference(light_normalisation,[status(thm)],[c_3516,c_2632]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_34,plain,
% 2.80/1.04      ( v1_funct_1(sK2) = iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_36,plain,
% 2.80/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_5,plain,
% 2.80/1.04      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f50]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1789,plain,
% 2.80/1.04      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_5]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1790,plain,
% 2.80/1.04      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.80/1.04      | v1_funct_1(sK2) != iProver_top
% 2.80/1.04      | v1_relat_1(sK2) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_1789]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_6,plain,
% 2.80/1.04      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.80/1.04      inference(cnf_transformation,[],[f49]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1792,plain,
% 2.80/1.04      ( ~ v1_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1793,plain,
% 2.80/1.04      ( v1_funct_1(sK2) != iProver_top
% 2.80/1.04      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.80/1.04      | v1_relat_1(sK2) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_1792]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1811,plain,
% 2.80/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.80/1.04      | v1_relat_1(sK2) = iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_1810]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3819,plain,
% 2.80/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 2.80/1.04      inference(global_propositional_subsumption,
% 2.80/1.04                [status(thm)],
% 2.80/1.04                [c_3553,c_34,c_36,c_1790,c_1793,c_1811]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3825,plain,
% 2.80/1.04      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_3819,c_1516]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3844,plain,
% 2.80/1.04      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
% 2.80/1.04      inference(light_normalisation,[status(thm)],[c_3825,c_2632]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3855,plain,
% 2.80/1.04      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1 | sK1 = k1_xboole_0 ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_3170,c_3844]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_23,plain,
% 2.80/1.04      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f68]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_28,negated_conjecture,
% 2.80/1.04      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.80/1.04      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.80/1.04      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.80/1.04      inference(cnf_transformation,[],[f78]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_669,plain,
% 2.80/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.80/1.04      | ~ v1_relat_1(X0)
% 2.80/1.04      | k2_funct_1(sK2) != X0
% 2.80/1.04      | k2_relat_1(X0) != sK0
% 2.80/1.04      | k1_relat_1(X0) != sK1 ),
% 2.80/1.04      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_670,plain,
% 2.80/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.80/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.80/1.04      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.80/1.04      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.80/1.04      inference(unflattening,[status(thm)],[c_669]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_682,plain,
% 2.80/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.80/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.80/1.04      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.80/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_670,c_10]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1498,plain,
% 2.80/1.04      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.80/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_671,plain,
% 2.80/1.04      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.80/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.80/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2336,plain,
% 2.80/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.80/1.04      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.80/1.04      inference(global_propositional_subsumption,
% 2.80/1.04                [status(thm)],
% 2.80/1.04                [c_1498,c_34,c_36,c_671,c_1790,c_1793,c_1811]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2337,plain,
% 2.80/1.04      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.80/1.04      inference(renaming,[status(thm)],[c_2336]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2340,plain,
% 2.80/1.04      ( k2_relat_1(sK2) != sK1
% 2.80/1.04      | k1_relat_1(sK2) != sK0
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.80/1.04      inference(light_normalisation,[status(thm)],[c_2337,c_1819,c_1823]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2630,plain,
% 2.80/1.04      ( k1_relat_1(sK2) != sK0
% 2.80/1.04      | sK1 != sK1
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.80/1.04      inference(demodulation,[status(thm)],[c_2624,c_2340]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2640,plain,
% 2.80/1.04      ( k1_relat_1(sK2) != sK0
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.80/1.04      inference(equality_resolution_simp,[status(thm)],[c_2630]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3269,plain,
% 2.80/1.04      ( sK1 = k1_xboole_0
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_3170,c_2640]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1,plain,
% 2.80/1.04      ( r1_tarski(k1_xboole_0,X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f45]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_26,plain,
% 2.80/1.04      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.80/1.04      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f71]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_345,plain,
% 2.80/1.04      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0)
% 2.80/1.04      | X1 != X2
% 2.80/1.04      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.80/1.04      inference(resolution_lifted,[status(thm)],[c_1,c_26]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_346,plain,
% 2.80/1.04      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0)
% 2.80/1.04      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.80/1.04      inference(unflattening,[status(thm)],[c_345]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_688,plain,
% 2.80/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.80/1.04      | ~ v1_relat_1(X0)
% 2.80/1.04      | k2_funct_1(sK2) != X0
% 2.80/1.04      | k2_relat_1(X0) != k1_xboole_0
% 2.80/1.04      | k1_relat_1(X0) != sK1
% 2.80/1.04      | sK0 != X1 ),
% 2.80/1.04      inference(resolution_lifted,[status(thm)],[c_346,c_28]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_689,plain,
% 2.80/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.80/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.80/1.04      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.80/1.04      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.80/1.04      inference(unflattening,[status(thm)],[c_688]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_701,plain,
% 2.80/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.80/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.80/1.04      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.80/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_689,c_10]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1497,plain,
% 2.80/1.04      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.80/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_690,plain,
% 2.80/1.04      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.80/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.80/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1894,plain,
% 2.80/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.80/1.04      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.80/1.04      inference(global_propositional_subsumption,
% 2.80/1.04                [status(thm)],
% 2.80/1.04                [c_1497,c_34,c_36,c_690,c_1790,c_1793,c_1811]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1895,plain,
% 2.80/1.04      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.80/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.80/1.04      inference(renaming,[status(thm)],[c_1894]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1898,plain,
% 2.80/1.04      ( k2_relat_1(sK2) != sK1
% 2.80/1.04      | k1_relat_1(sK2) != k1_xboole_0
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.80/1.04      inference(light_normalisation,[status(thm)],[c_1895,c_1819,c_1823]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3,plain,
% 2.80/1.04      ( ~ v1_relat_1(X0)
% 2.80/1.04      | k2_relat_1(X0) != k1_xboole_0
% 2.80/1.04      | k1_relat_1(X0) = k1_xboole_0 ),
% 2.80/1.04      inference(cnf_transformation,[],[f48]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1523,plain,
% 2.80/1.04      ( k2_relat_1(X0) != k1_xboole_0
% 2.80/1.04      | k1_relat_1(X0) = k1_xboole_0
% 2.80/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2647,plain,
% 2.80/1.04      ( k1_relat_1(sK2) = k1_xboole_0
% 2.80/1.04      | sK1 != k1_xboole_0
% 2.80/1.04      | v1_relat_1(sK2) != iProver_top ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_2624,c_1523]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2735,plain,
% 2.80/1.04      ( sK1 != k1_xboole_0 | k1_relat_1(sK2) = k1_xboole_0 ),
% 2.80/1.04      inference(global_propositional_subsumption,
% 2.80/1.04                [status(thm)],
% 2.80/1.04                [c_2647,c_36,c_1811]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2736,plain,
% 2.80/1.04      ( k1_relat_1(sK2) = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 2.80/1.04      inference(renaming,[status(thm)],[c_2735]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3376,plain,
% 2.80/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.80/1.04      inference(global_propositional_subsumption,
% 2.80/1.04                [status(thm)],
% 2.80/1.04                [c_3269,c_1898,c_2624,c_2736]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3824,plain,
% 2.80/1.04      ( sK1 = k1_xboole_0
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_3170,c_3819]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4173,plain,
% 2.80/1.04      ( sK1 = k1_xboole_0 ),
% 2.80/1.04      inference(global_propositional_subsumption,
% 2.80/1.04                [status(thm)],
% 2.80/1.04                [c_3855,c_1898,c_2624,c_2736,c_3269,c_3824]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2631,plain,
% 2.80/1.04      ( k1_relat_1(sK2) != k1_xboole_0
% 2.80/1.04      | sK1 != sK1
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.80/1.04      inference(demodulation,[status(thm)],[c_2624,c_1898]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2635,plain,
% 2.80/1.04      ( k1_relat_1(sK2) != k1_xboole_0
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.80/1.04      inference(equality_resolution_simp,[status(thm)],[c_2631]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4189,plain,
% 2.80/1.04      ( k1_relat_1(sK2) != k1_xboole_0
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.80/1.04      inference(demodulation,[status(thm)],[c_4173,c_2635]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4191,plain,
% 2.80/1.04      ( k1_relat_1(sK2) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.80/1.04      inference(demodulation,[status(thm)],[c_4173,c_2736]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4241,plain,
% 2.80/1.04      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 2.80/1.04      inference(equality_resolution_simp,[status(thm)],[c_4191]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4250,plain,
% 2.80/1.04      ( k1_xboole_0 != k1_xboole_0
% 2.80/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.80/1.04      inference(light_normalisation,[status(thm)],[c_4189,c_4241]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4251,plain,
% 2.80/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.80/1.04      inference(equality_resolution_simp,[status(thm)],[c_4250]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_12,plain,
% 2.80/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.04      | ~ v1_xboole_0(X2)
% 2.80/1.04      | v1_xboole_0(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f56]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1517,plain,
% 2.80/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.80/1.04      | v1_xboole_0(X2) != iProver_top
% 2.80/1.04      | v1_xboole_0(X0) = iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3156,plain,
% 2.80/1.04      ( v1_xboole_0(sK1) != iProver_top | v1_xboole_0(sK2) = iProver_top ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_1512,c_1517]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4185,plain,
% 2.80/1.04      ( v1_xboole_0(sK2) = iProver_top
% 2.80/1.04      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.80/1.04      inference(demodulation,[status(thm)],[c_4173,c_3156]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_0,plain,
% 2.80/1.04      ( v1_xboole_0(k1_xboole_0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f44]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_110,plain,
% 2.80/1.04      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_990,plain,
% 2.80/1.04      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.80/1.04      theory(equality) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2056,plain,
% 2.80/1.04      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_990]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2057,plain,
% 2.80/1.04      ( sK1 != X0
% 2.80/1.04      | v1_xboole_0(X0) != iProver_top
% 2.80/1.04      | v1_xboole_0(sK1) = iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_2056]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2059,plain,
% 2.80/1.04      ( sK1 != k1_xboole_0
% 2.80/1.04      | v1_xboole_0(sK1) = iProver_top
% 2.80/1.04      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_2057]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2299,plain,
% 2.80/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.80/1.04      | ~ v1_xboole_0(X1)
% 2.80/1.04      | v1_xboole_0(sK2) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3025,plain,
% 2.80/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.80/1.04      | ~ v1_xboole_0(sK1)
% 2.80/1.04      | v1_xboole_0(sK2) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_2299]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3026,plain,
% 2.80/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.80/1.04      | v1_xboole_0(sK1) != iProver_top
% 2.80/1.04      | v1_xboole_0(sK2) = iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_3025]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4867,plain,
% 2.80/1.04      ( v1_xboole_0(sK2) = iProver_top ),
% 2.80/1.04      inference(global_propositional_subsumption,
% 2.80/1.04                [status(thm)],
% 2.80/1.04                [c_4185,c_36,c_110,c_1898,c_2059,c_2624,c_2736,c_3026,c_3269,
% 2.80/1.04                 c_3824]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1525,plain,
% 2.80/1.04      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2,plain,
% 2.80/1.04      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 2.80/1.04      inference(cnf_transformation,[],[f46]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1524,plain,
% 2.80/1.04      ( X0 = X1
% 2.80/1.04      | v1_xboole_0(X0) != iProver_top
% 2.80/1.04      | v1_xboole_0(X1) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2451,plain,
% 2.80/1.04      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_1525,c_1524]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4872,plain,
% 2.80/1.04      ( sK2 = k1_xboole_0 ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_4867,c_2451]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_21,plain,
% 2.80/1.04      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.80/1.04      inference(cnf_transformation,[],[f65]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1514,plain,
% 2.80/1.04      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3155,plain,
% 2.80/1.04      ( v1_xboole_0(X0) != iProver_top
% 2.80/1.04      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_1514,c_1517]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4093,plain,
% 2.80/1.04      ( k6_partfun1(X0) = X1
% 2.80/1.04      | v1_xboole_0(X0) != iProver_top
% 2.80/1.04      | v1_xboole_0(X1) != iProver_top ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_3155,c_1524]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_5153,plain,
% 2.80/1.04      ( k6_partfun1(k1_xboole_0) = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_1525,c_4093]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_6056,plain,
% 2.80/1.04      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_1525,c_5153]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_9,plain,
% 2.80/1.04      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f79]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_6668,plain,
% 2.80/1.04      ( k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_6056,c_9]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_6669,plain,
% 2.80/1.04      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 2.80/1.04      inference(light_normalisation,[status(thm)],[c_6668,c_6056]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_7164,plain,
% 2.80/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.80/1.04      inference(light_normalisation,[status(thm)],[c_4251,c_4872,c_6669]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4193,plain,
% 2.80/1.04      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 2.80/1.04      inference(demodulation,[status(thm)],[c_4173,c_2624]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_25,plain,
% 2.80/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.80/1.04      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f72]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_363,plain,
% 2.80/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0)
% 2.80/1.04      | X1 != X2
% 2.80/1.04      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.80/1.04      inference(resolution_lifted,[status(thm)],[c_1,c_25]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_364,plain,
% 2.80/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0)
% 2.80/1.04      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.80/1.04      inference(unflattening,[status(thm)],[c_363]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1510,plain,
% 2.80/1.04      ( k2_relat_1(X0) != k1_xboole_0
% 2.80/1.04      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 2.80/1.04      | v1_funct_1(X0) != iProver_top
% 2.80/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4894,plain,
% 2.80/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
% 2.80/1.04      | v1_funct_1(sK2) != iProver_top
% 2.80/1.04      | v1_relat_1(sK2) != iProver_top ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_4193,c_1510]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1829,plain,
% 2.80/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
% 2.80/1.04      | ~ v1_funct_1(sK2)
% 2.80/1.04      | ~ v1_relat_1(sK2)
% 2.80/1.04      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_364]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1830,plain,
% 2.80/1.04      ( k2_relat_1(sK2) != k1_xboole_0
% 2.80/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
% 2.80/1.04      | v1_funct_1(sK2) != iProver_top
% 2.80/1.04      | v1_relat_1(sK2) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_1829]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_4,plain,
% 2.80/1.04      ( ~ v1_relat_1(X0)
% 2.80/1.04      | k2_relat_1(X0) = k1_xboole_0
% 2.80/1.04      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.80/1.04      inference(cnf_transformation,[],[f47]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1883,plain,
% 2.80/1.04      ( ~ v1_relat_1(sK2)
% 2.80/1.04      | k2_relat_1(sK2) = k1_xboole_0
% 2.80/1.04      | k1_relat_1(sK2) != k1_xboole_0 ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_4]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_5170,plain,
% 2.80/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top ),
% 2.80/1.04      inference(global_propositional_subsumption,
% 2.80/1.04                [status(thm)],
% 2.80/1.04                [c_4894,c_34,c_31,c_36,c_1810,c_1811,c_1830,c_1883,c_1898,
% 2.80/1.04                 c_2624,c_2647,c_2736,c_3269,c_3824]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_5415,plain,
% 2.80/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X0))) = iProver_top ),
% 2.80/1.04      inference(demodulation,[status(thm)],[c_4872,c_5170]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1511,plain,
% 2.80/1.04      ( v1_funct_1(sK2) = iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_5429,plain,
% 2.80/1.04      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 2.80/1.04      inference(demodulation,[status(thm)],[c_4872,c_1511]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1521,plain,
% 2.80/1.04      ( v1_funct_1(X0) != iProver_top
% 2.80/1.04      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 2.80/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_591,plain,
% 2.80/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.04      | ~ v1_funct_1(X3)
% 2.80/1.04      | ~ v1_relat_1(X3)
% 2.80/1.04      | X3 != X0
% 2.80/1.04      | k1_relset_1(X1,X2,X0) = X1
% 2.80/1.04      | k2_relat_1(X3) != X2
% 2.80/1.04      | k1_relat_1(X3) != X1
% 2.80/1.04      | k1_xboole_0 = X2 ),
% 2.80/1.04      inference(resolution_lifted,[status(thm)],[c_20,c_23]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_592,plain,
% 2.80/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.80/1.04      | ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0)
% 2.80/1.04      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 2.80/1.04      | k1_xboole_0 = k2_relat_1(X0) ),
% 2.80/1.04      inference(unflattening,[status(thm)],[c_591]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_596,plain,
% 2.80/1.04      ( ~ v1_funct_1(X0)
% 2.80/1.04      | ~ v1_relat_1(X0)
% 2.80/1.04      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 2.80/1.04      | k1_xboole_0 = k2_relat_1(X0) ),
% 2.80/1.04      inference(global_propositional_subsumption,[status(thm)],[c_592,c_22]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1501,plain,
% 2.80/1.04      ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 2.80/1.04      | k1_xboole_0 = k2_relat_1(X0)
% 2.80/1.04      | v1_funct_1(X0) != iProver_top
% 2.80/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_3041,plain,
% 2.80/1.04      ( k1_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k1_relat_1(k2_funct_1(X0))
% 2.80/1.04      | k2_relat_1(k2_funct_1(X0)) = k1_xboole_0
% 2.80/1.04      | v1_funct_1(X0) != iProver_top
% 2.80/1.04      | v1_relat_1(X0) != iProver_top
% 2.80/1.04      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_1521,c_1501]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_92,plain,
% 2.80/1.04      ( v1_funct_1(X0) != iProver_top
% 2.80/1.04      | v1_relat_1(X0) != iProver_top
% 2.80/1.04      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.80/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_5568,plain,
% 2.80/1.04      ( v1_relat_1(X0) != iProver_top
% 2.80/1.04      | v1_funct_1(X0) != iProver_top
% 2.80/1.04      | k2_relat_1(k2_funct_1(X0)) = k1_xboole_0
% 2.80/1.04      | k1_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k1_relat_1(k2_funct_1(X0)) ),
% 2.80/1.04      inference(global_propositional_subsumption,[status(thm)],[c_3041,c_92]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_5569,plain,
% 2.80/1.04      ( k1_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k1_relat_1(k2_funct_1(X0))
% 2.80/1.04      | k2_relat_1(k2_funct_1(X0)) = k1_xboole_0
% 2.80/1.04      | v1_funct_1(X0) != iProver_top
% 2.80/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.80/1.04      inference(renaming,[status(thm)],[c_5568]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_5584,plain,
% 2.80/1.04      ( k1_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0))
% 2.80/1.04      | k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 2.80/1.04      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.80/1.04      inference(superposition,[status(thm)],[c_5429,c_5569]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_54,plain,
% 2.80/1.04      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_21]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1805,plain,
% 2.80/1.04      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 2.80/1.04      | v1_relat_1(k6_partfun1(X0)) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_10]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_1807,plain,
% 2.80/1.04      ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 2.80/1.04      | v1_relat_1(k6_partfun1(k1_xboole_0)) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_1805]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_993,plain,
% 2.80/1.04      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 2.80/1.04      theory(equality) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2172,plain,
% 2.80/1.04      ( v1_relat_1(X0)
% 2.80/1.04      | ~ v1_relat_1(k6_partfun1(X1))
% 2.80/1.04      | X0 != k6_partfun1(X1) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_993]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2184,plain,
% 2.80/1.04      ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
% 2.80/1.04      | v1_relat_1(k1_xboole_0)
% 2.80/1.04      | k1_xboole_0 != k6_partfun1(k1_xboole_0) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_2172]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2399,plain,
% 2.80/1.04      ( ~ v1_xboole_0(X0)
% 2.80/1.04      | ~ v1_xboole_0(k6_partfun1(X1))
% 2.80/1.04      | X0 = k6_partfun1(X1) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_2]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2401,plain,
% 2.80/1.04      ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
% 2.80/1.04      | ~ v1_xboole_0(k1_xboole_0)
% 2.80/1.04      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_2399]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_11,plain,
% 2.80/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.04      | ~ v1_xboole_0(X1)
% 2.80/1.04      | v1_xboole_0(X0) ),
% 2.80/1.04      inference(cnf_transformation,[],[f55]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2706,plain,
% 2.80/1.04      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.04      | ~ v1_xboole_0(X1)
% 2.80/1.04      | v1_xboole_0(k6_partfun1(X0)) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_11]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_2708,plain,
% 2.80/1.04      ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 2.80/1.04      | v1_xboole_0(k6_partfun1(k1_xboole_0))
% 2.80/1.04      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_2706]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_5592,plain,
% 2.80/1.04      ( ~ v1_relat_1(k1_xboole_0)
% 2.80/1.04      | k1_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0))
% 2.80/1.04      | k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.80/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_5584]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_6477,plain,
% 2.80/1.04      ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 2.80/1.04      | k1_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
% 2.80/1.04      inference(global_propositional_subsumption,
% 2.80/1.04                [status(thm)],
% 2.80/1.04                [c_5584,c_54,c_0,c_1807,c_2184,c_2401,c_2708,c_5592]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_6478,plain,
% 2.80/1.04      ( k1_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0))
% 2.80/1.04      | k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.80/1.04      inference(renaming,[status(thm)],[c_6477]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_5428,plain,
% 2.80/1.04      ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 2.80/1.04      inference(demodulation,[status(thm)],[c_4872,c_1819]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_6479,plain,
% 2.80/1.04      ( k1_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k1_xboole_0),k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0))
% 2.80/1.04      | k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.80/1.04      inference(light_normalisation,[status(thm)],[c_6478,c_5428]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_6480,plain,
% 2.80/1.04      ( k1_relset_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k1_xboole_0),k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0))
% 2.80/1.04      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.80/1.04      inference(demodulation,[status(thm)],[c_6479,c_5428]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_102,plain,
% 2.80/1.04      ( ~ v1_relat_1(k1_xboole_0)
% 2.80/1.04      | k2_relat_1(k1_xboole_0) != k1_xboole_0
% 2.80/1.04      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.80/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_5420,plain,
% 2.80/1.04      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.80/1.04      inference(demodulation,[status(thm)],[c_4872,c_4193]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_6483,plain,
% 2.80/1.04      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.80/1.04      inference(global_propositional_subsumption,
% 2.80/1.04                [status(thm)],
% 2.80/1.04                [c_6480,c_54,c_102,c_0,c_1807,c_2184,c_2401,c_2708,c_5420]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_6821,plain,
% 2.80/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
% 2.80/1.04      inference(light_normalisation,[status(thm)],[c_5415,c_6483]) ).
% 2.80/1.04  
% 2.80/1.04  cnf(c_7166,plain,
% 2.80/1.04      ( $false ),
% 2.80/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_7164,c_6821]) ).
% 2.80/1.04  
% 2.80/1.04  
% 2.80/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/1.04  
% 2.80/1.04  ------                               Statistics
% 2.80/1.04  
% 2.80/1.04  ------ General
% 2.80/1.04  
% 2.80/1.04  abstr_ref_over_cycles:                  0
% 2.80/1.04  abstr_ref_under_cycles:                 0
% 2.80/1.04  gc_basic_clause_elim:                   0
% 2.80/1.04  forced_gc_time:                         0
% 2.80/1.04  parsing_time:                           0.012
% 2.80/1.04  unif_index_cands_time:                  0.
% 2.80/1.04  unif_index_add_time:                    0.
% 2.80/1.04  orderings_time:                         0.
% 2.80/1.04  out_proof_time:                         0.012
% 2.80/1.04  total_time:                             0.267
% 2.80/1.04  num_of_symbols:                         50
% 2.80/1.04  num_of_terms:                           3786
% 2.80/1.04  
% 2.80/1.04  ------ Preprocessing
% 2.80/1.04  
% 2.80/1.04  num_of_splits:                          0
% 2.80/1.04  num_of_split_atoms:                     0
% 2.80/1.04  num_of_reused_defs:                     0
% 2.80/1.04  num_eq_ax_congr_red:                    6
% 2.80/1.04  num_of_sem_filtered_clauses:            1
% 2.80/1.04  num_of_subtypes:                        0
% 2.80/1.04  monotx_restored_types:                  0
% 2.80/1.04  sat_num_of_epr_types:                   0
% 2.80/1.04  sat_num_of_non_cyclic_types:            0
% 2.80/1.04  sat_guarded_non_collapsed_types:        0
% 2.80/1.04  num_pure_diseq_elim:                    0
% 2.80/1.04  simp_replaced_by:                       0
% 2.80/1.04  res_preprocessed:                       158
% 2.80/1.04  prep_upred:                             0
% 2.80/1.04  prep_unflattend:                        55
% 2.80/1.04  smt_new_axioms:                         0
% 2.80/1.04  pred_elim_cands:                        4
% 2.80/1.04  pred_elim:                              3
% 2.80/1.04  pred_elim_cl:                           -1
% 2.80/1.04  pred_elim_cycles:                       5
% 2.80/1.04  merged_defs:                            0
% 2.80/1.04  merged_defs_ncl:                        0
% 2.80/1.04  bin_hyper_res:                          0
% 2.80/1.04  prep_cycles:                            4
% 2.80/1.04  pred_elim_time:                         0.017
% 2.80/1.04  splitting_time:                         0.
% 2.80/1.04  sem_filter_time:                        0.
% 2.80/1.04  monotx_time:                            0.001
% 2.80/1.04  subtype_inf_time:                       0.
% 2.80/1.04  
% 2.80/1.04  ------ Problem properties
% 2.80/1.04  
% 2.80/1.04  clauses:                                33
% 2.80/1.04  conjectures:                            3
% 2.80/1.04  epr:                                    3
% 2.80/1.04  horn:                                   28
% 2.80/1.04  ground:                                 15
% 2.80/1.04  unary:                                  6
% 2.80/1.04  binary:                                 6
% 2.80/1.04  lits:                                   98
% 2.80/1.04  lits_eq:                                42
% 2.80/1.04  fd_pure:                                0
% 2.80/1.04  fd_pseudo:                              0
% 2.80/1.04  fd_cond:                                2
% 2.80/1.04  fd_pseudo_cond:                         1
% 2.80/1.04  ac_symbols:                             0
% 2.80/1.04  
% 2.80/1.04  ------ Propositional Solver
% 2.80/1.04  
% 2.80/1.04  prop_solver_calls:                      29
% 2.80/1.04  prop_fast_solver_calls:                 1393
% 2.80/1.04  smt_solver_calls:                       0
% 2.80/1.04  smt_fast_solver_calls:                  0
% 2.80/1.04  prop_num_of_clauses:                    2523
% 2.80/1.04  prop_preprocess_simplified:             7613
% 2.80/1.04  prop_fo_subsumed:                       66
% 2.80/1.04  prop_solver_time:                       0.
% 2.80/1.04  smt_solver_time:                        0.
% 2.80/1.04  smt_fast_solver_time:                   0.
% 2.80/1.04  prop_fast_solver_time:                  0.
% 2.80/1.04  prop_unsat_core_time:                   0.
% 2.80/1.04  
% 2.80/1.04  ------ QBF
% 2.80/1.04  
% 2.80/1.04  qbf_q_res:                              0
% 2.80/1.04  qbf_num_tautologies:                    0
% 2.80/1.04  qbf_prep_cycles:                        0
% 2.80/1.04  
% 2.80/1.04  ------ BMC1
% 2.80/1.04  
% 2.80/1.04  bmc1_current_bound:                     -1
% 2.80/1.04  bmc1_last_solved_bound:                 -1
% 2.80/1.04  bmc1_unsat_core_size:                   -1
% 2.80/1.04  bmc1_unsat_core_parents_size:           -1
% 2.80/1.04  bmc1_merge_next_fun:                    0
% 2.80/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.80/1.04  
% 2.80/1.04  ------ Instantiation
% 2.80/1.04  
% 2.80/1.04  inst_num_of_clauses:                    860
% 2.80/1.04  inst_num_in_passive:                    442
% 2.80/1.04  inst_num_in_active:                     353
% 2.80/1.04  inst_num_in_unprocessed:                65
% 2.80/1.04  inst_num_of_loops:                      530
% 2.80/1.04  inst_num_of_learning_restarts:          0
% 2.80/1.04  inst_num_moves_active_passive:          174
% 2.80/1.04  inst_lit_activity:                      0
% 2.80/1.04  inst_lit_activity_moves:                0
% 2.80/1.04  inst_num_tautologies:                   0
% 2.80/1.04  inst_num_prop_implied:                  0
% 2.80/1.04  inst_num_existing_simplified:           0
% 2.80/1.04  inst_num_eq_res_simplified:             0
% 2.80/1.04  inst_num_child_elim:                    0
% 2.80/1.04  inst_num_of_dismatching_blockings:      74
% 2.80/1.04  inst_num_of_non_proper_insts:           670
% 2.80/1.04  inst_num_of_duplicates:                 0
% 2.80/1.04  inst_inst_num_from_inst_to_res:         0
% 2.80/1.04  inst_dismatching_checking_time:         0.
% 2.80/1.04  
% 2.80/1.04  ------ Resolution
% 2.80/1.04  
% 2.80/1.04  res_num_of_clauses:                     0
% 2.80/1.04  res_num_in_passive:                     0
% 2.80/1.04  res_num_in_active:                      0
% 2.80/1.04  res_num_of_loops:                       162
% 2.80/1.04  res_forward_subset_subsumed:            29
% 2.80/1.04  res_backward_subset_subsumed:           2
% 2.80/1.04  res_forward_subsumed:                   0
% 2.80/1.04  res_backward_subsumed:                  1
% 2.80/1.04  res_forward_subsumption_resolution:     5
% 2.80/1.04  res_backward_subsumption_resolution:    0
% 2.80/1.04  res_clause_to_clause_subsumption:       259
% 2.80/1.04  res_orphan_elimination:                 0
% 2.80/1.04  res_tautology_del:                      84
% 2.80/1.04  res_num_eq_res_simplified:              0
% 2.80/1.04  res_num_sel_changes:                    0
% 2.80/1.04  res_moves_from_active_to_pass:          0
% 2.80/1.04  
% 2.80/1.04  ------ Superposition
% 2.80/1.04  
% 2.80/1.04  sup_time_total:                         0.
% 2.80/1.04  sup_time_generating:                    0.
% 2.80/1.04  sup_time_sim_full:                      0.
% 2.80/1.04  sup_time_sim_immed:                     0.
% 2.80/1.04  
% 2.80/1.04  sup_num_of_clauses:                     75
% 2.80/1.04  sup_num_in_active:                      50
% 2.80/1.04  sup_num_in_passive:                     25
% 2.80/1.04  sup_num_of_loops:                       104
% 2.80/1.04  sup_fw_superposition:                   63
% 2.80/1.04  sup_bw_superposition:                   93
% 2.80/1.04  sup_immediate_simplified:               86
% 2.80/1.04  sup_given_eliminated:                   3
% 2.80/1.04  comparisons_done:                       0
% 2.80/1.04  comparisons_avoided:                    11
% 2.80/1.04  
% 2.80/1.04  ------ Simplifications
% 2.80/1.04  
% 2.80/1.04  
% 2.80/1.04  sim_fw_subset_subsumed:                 32
% 2.80/1.04  sim_bw_subset_subsumed:                 9
% 2.80/1.04  sim_fw_subsumed:                        3
% 2.80/1.04  sim_bw_subsumed:                        5
% 2.80/1.04  sim_fw_subsumption_res:                 2
% 2.80/1.04  sim_bw_subsumption_res:                 1
% 2.80/1.04  sim_tautology_del:                      8
% 2.80/1.04  sim_eq_tautology_del:                   16
% 2.80/1.04  sim_eq_res_simp:                        8
% 2.80/1.04  sim_fw_demodulated:                     8
% 2.80/1.04  sim_bw_demodulated:                     56
% 2.80/1.04  sim_light_normalised:                   70
% 2.80/1.04  sim_joinable_taut:                      0
% 2.80/1.04  sim_joinable_simp:                      0
% 2.80/1.04  sim_ac_normalised:                      0
% 2.80/1.04  sim_smt_subsumption:                    0
% 2.80/1.04  
%------------------------------------------------------------------------------

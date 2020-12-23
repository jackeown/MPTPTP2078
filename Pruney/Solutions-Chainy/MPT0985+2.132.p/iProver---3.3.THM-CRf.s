%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:47 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  247 (27296 expanded)
%              Number of clauses        :  180 (8363 expanded)
%              Number of leaves         :   21 (5382 expanded)
%              Depth                    :   29
%              Number of atoms          :  717 (149721 expanded)
%              Number of equality atoms :  364 (28717 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f17])).

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

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f51,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_463,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_30])).

cnf(c_464,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_466,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_33])).

cnf(c_2087,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2404,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2413,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2087,c_33,c_31,c_464,c_2404])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2093,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4179,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2413,c_2093])).

cnf(c_2091,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2097,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2863,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2091,c_2097])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2865,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2863,c_29])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_449,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_30])).

cnf(c_450,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_452,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_33])).

cnf(c_2088,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_2417,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2088,c_33,c_31,c_450,c_2404])).

cnf(c_2876,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2865,c_2417])).

cnf(c_4226,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4179,c_2876])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2405,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2404])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2483,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2484,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2483])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2482,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2486,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2482])).

cnf(c_5152,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4226,c_34,c_36,c_2405,c_2484,c_2486])).

cnf(c_5163,plain,
    ( k2_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5152,c_2097])).

cnf(c_5168,plain,
    ( k2_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5163,c_2413])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2099,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5220,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5168,c_2099])).

cnf(c_9000,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5220,c_34,c_36,c_2405,c_2484,c_2486,c_4226])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_890,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_891,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_890])).

cnf(c_893,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_891,c_31])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2098,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2923,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2091,c_2098])).

cnf(c_3015,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_893,c_2923])).

cnf(c_5162,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5152,c_2098])).

cnf(c_5171,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5162,c_2876])).

cnf(c_5217,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3015,c_5171])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_901,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(X0) != sK0
    | k1_relat_1(X0) != sK1
    | k2_funct_1(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_902,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_901])).

cnf(c_914,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_902,c_9])).

cnf(c_2074,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_914])).

cnf(c_903,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_902])).

cnf(c_3230,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2074,c_34,c_36,c_903,c_2405,c_2484,c_2486,c_2876])).

cnf(c_3231,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3230])).

cnf(c_3234,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3231,c_2413])).

cnf(c_3238,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3015,c_3234])).

cnf(c_5157,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3015,c_5152])).

cnf(c_5988,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5217,c_3238,c_5157])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_722,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK0 != X1
    | sK1 != k1_xboole_0
    | sK2 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_723,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_722])).

cnf(c_2082,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_6023,plain,
    ( sK0 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5988,c_2082])).

cnf(c_6064,plain,
    ( sK0 = k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6023])).

cnf(c_6031,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5988,c_2091])).

cnf(c_6068,plain,
    ( sK0 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6064,c_6031])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_117,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1305,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2547,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1308,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_3806,plain,
    ( k1_zfmisc_1(sK0) = k1_zfmisc_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_1,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4331,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0))
    | ~ r1_tarski(X0,sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4333,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_4331])).

cnf(c_4375,plain,
    ( r1_tarski(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2092,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4675,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_2092])).

cnf(c_4735,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4675,c_2413])).

cnf(c_5281,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4735,c_34,c_36,c_2405,c_2484,c_2486])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_920,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(X0) != sK1
    | k2_funct_1(sK2) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_921,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_933,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_921,c_9])).

cnf(c_2073,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_922,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_2803,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2073,c_34,c_36,c_922,c_2405,c_2484,c_2486])).

cnf(c_2804,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2803])).

cnf(c_2807,plain,
    ( k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2804,c_2413,c_2417])).

cnf(c_2875,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2865,c_2807])).

cnf(c_2879,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2875])).

cnf(c_5297,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5281,c_2879])).

cnf(c_5336,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5297])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
    | r1_tarski(X0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5960,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_4380])).

cnf(c_6022,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5988,c_2865])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_697,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_696])).

cnf(c_713,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_697,c_25])).

cnf(c_2083,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_6290,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6022,c_2083])).

cnf(c_6302,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6290])).

cnf(c_1309,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2451,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_2566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2451])).

cnf(c_4351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
    | m1_subset_1(X1,k1_zfmisc_1(sK0))
    | X1 != X0
    | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
    inference(instantiation,[status(thm)],[c_2566])).

cnf(c_6449,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | k1_relat_1(sK2) != X0
    | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
    inference(instantiation,[status(thm)],[c_4351])).

cnf(c_6451,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | k1_relat_1(sK2) != k1_xboole_0
    | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
    inference(instantiation,[status(thm)],[c_6449])).

cnf(c_7560,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6068,c_33,c_31,c_117,c_2404,c_2547,c_3806,c_4333,c_4375,c_5336,c_5960,c_6302,c_6451])).

cnf(c_9004,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_relat_1(k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9000,c_7560])).

cnf(c_2103,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9007,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9004,c_2103])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_428,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_30])).

cnf(c_429,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_433,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(X0,k1_relat_1(sK2))
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_33])).

cnf(c_434,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_433])).

cnf(c_2089,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_435,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_2663,plain,
    ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2089,c_36,c_435,c_2405])).

cnf(c_2664,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2663])).

cnf(c_7582,plain,
    ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7560,c_2664])).

cnf(c_9409,plain,
    ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9007,c_7582])).

cnf(c_4178,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2865,c_2093])).

cnf(c_4277,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4178,c_34,c_36,c_2405])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2096,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4286,plain,
    ( k7_relset_1(k1_relat_1(sK2),sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_4277,c_2096])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2094,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4285,plain,
    ( k7_relset_1(k1_relat_1(sK2),sK1,sK2,k1_relat_1(sK2)) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_4277,c_2094])).

cnf(c_4288,plain,
    ( k2_relset_1(k1_relat_1(sK2),sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4277,c_2097])).

cnf(c_4291,plain,
    ( k2_relset_1(k1_relat_1(sK2),sK1,sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4288,c_2865])).

cnf(c_4297,plain,
    ( k7_relset_1(k1_relat_1(sK2),sK1,sK2,k1_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4285,c_4291])).

cnf(c_4548,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_4286,c_4297])).

cnf(c_9165,plain,
    ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4548,c_5988,c_7560])).

cnf(c_9410,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_9409,c_9165])).

cnf(c_7576,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7560,c_6022])).

cnf(c_2104,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2105,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2862,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2104,c_2097])).

cnf(c_4863,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2105,c_2862])).

cnf(c_5530,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4863,c_2099])).

cnf(c_7333,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2104,c_5530])).

cnf(c_7484,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7333,c_2105])).

cnf(c_7939,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7576,c_7484])).

cnf(c_4000,plain,
    ( k7_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),X3),X0) = k2_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),X3))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X0,X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2099,c_2094])).

cnf(c_11151,plain,
    ( k7_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),k1_xboole_0),X0) = k2_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_7939,c_4000])).

cnf(c_7940,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7576,c_4863])).

cnf(c_7491,plain,
    ( k7_relset_1(X0,X1,k2_relat_1(k1_xboole_0),X2) = k9_relat_1(k2_relat_1(k1_xboole_0),X2) ),
    inference(superposition,[status(thm)],[c_7484,c_2096])).

cnf(c_8628,plain,
    ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(light_normalisation,[status(thm)],[c_7491,c_7576])).

cnf(c_11153,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11151,c_7940,c_8628])).

cnf(c_2671,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2105,c_2664])).

cnf(c_7581,plain,
    ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7560,c_2671])).

cnf(c_13536,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11153,c_7581])).

cnf(c_13644,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9410,c_13536])).

cnf(c_1306,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3318,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1306])).

cnf(c_3319,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3318])).

cnf(c_1315,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_2717,plain,
    ( k1_relat_1(sK2) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_2719,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2717])).

cnf(c_2527,plain,
    ( k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1306])).

cnf(c_2716,plain,
    ( k1_relat_1(sK2) != k1_relat_1(X0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_2718,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2716])).

cnf(c_1334,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13644,c_6451,c_6302,c_5960,c_5336,c_4375,c_4333,c_3806,c_3319,c_2719,c_2718,c_2547,c_2404,c_1334,c_117,c_31,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:51:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.61/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/0.92  
% 3.61/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.92  
% 3.61/0.92  ------  iProver source info
% 3.61/0.92  
% 3.61/0.92  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.92  git: non_committed_changes: false
% 3.61/0.92  git: last_make_outside_of_git: false
% 3.61/0.92  
% 3.61/0.92  ------ 
% 3.61/0.92  
% 3.61/0.92  ------ Input Options
% 3.61/0.92  
% 3.61/0.92  --out_options                           all
% 3.61/0.92  --tptp_safe_out                         true
% 3.61/0.92  --problem_path                          ""
% 3.61/0.92  --include_path                          ""
% 3.61/0.92  --clausifier                            res/vclausify_rel
% 3.61/0.92  --clausifier_options                    --mode clausify
% 3.61/0.92  --stdin                                 false
% 3.61/0.92  --stats_out                             all
% 3.61/0.92  
% 3.61/0.92  ------ General Options
% 3.61/0.92  
% 3.61/0.92  --fof                                   false
% 3.61/0.92  --time_out_real                         305.
% 3.61/0.92  --time_out_virtual                      -1.
% 3.61/0.92  --symbol_type_check                     false
% 3.61/0.92  --clausify_out                          false
% 3.61/0.92  --sig_cnt_out                           false
% 3.61/0.92  --trig_cnt_out                          false
% 3.61/0.92  --trig_cnt_out_tolerance                1.
% 3.61/0.92  --trig_cnt_out_sk_spl                   false
% 3.61/0.92  --abstr_cl_out                          false
% 3.61/0.92  
% 3.61/0.92  ------ Global Options
% 3.61/0.92  
% 3.61/0.92  --schedule                              default
% 3.61/0.92  --add_important_lit                     false
% 3.61/0.92  --prop_solver_per_cl                    1000
% 3.61/0.92  --min_unsat_core                        false
% 3.61/0.92  --soft_assumptions                      false
% 3.61/0.92  --soft_lemma_size                       3
% 3.61/0.92  --prop_impl_unit_size                   0
% 3.61/0.92  --prop_impl_unit                        []
% 3.61/0.92  --share_sel_clauses                     true
% 3.61/0.92  --reset_solvers                         false
% 3.61/0.92  --bc_imp_inh                            [conj_cone]
% 3.61/0.92  --conj_cone_tolerance                   3.
% 3.61/0.92  --extra_neg_conj                        none
% 3.61/0.92  --large_theory_mode                     true
% 3.61/0.92  --prolific_symb_bound                   200
% 3.61/0.92  --lt_threshold                          2000
% 3.61/0.92  --clause_weak_htbl                      true
% 3.61/0.92  --gc_record_bc_elim                     false
% 3.61/0.92  
% 3.61/0.92  ------ Preprocessing Options
% 3.61/0.92  
% 3.61/0.92  --preprocessing_flag                    true
% 3.61/0.92  --time_out_prep_mult                    0.1
% 3.61/0.92  --splitting_mode                        input
% 3.61/0.92  --splitting_grd                         true
% 3.61/0.92  --splitting_cvd                         false
% 3.61/0.92  --splitting_cvd_svl                     false
% 3.61/0.92  --splitting_nvd                         32
% 3.61/0.92  --sub_typing                            true
% 3.61/0.92  --prep_gs_sim                           true
% 3.61/0.92  --prep_unflatten                        true
% 3.61/0.92  --prep_res_sim                          true
% 3.61/0.92  --prep_upred                            true
% 3.61/0.92  --prep_sem_filter                       exhaustive
% 3.61/0.92  --prep_sem_filter_out                   false
% 3.61/0.92  --pred_elim                             true
% 3.61/0.92  --res_sim_input                         true
% 3.61/0.92  --eq_ax_congr_red                       true
% 3.61/0.92  --pure_diseq_elim                       true
% 3.61/0.92  --brand_transform                       false
% 3.61/0.92  --non_eq_to_eq                          false
% 3.61/0.92  --prep_def_merge                        true
% 3.61/0.92  --prep_def_merge_prop_impl              false
% 3.61/0.92  --prep_def_merge_mbd                    true
% 3.61/0.92  --prep_def_merge_tr_red                 false
% 3.61/0.92  --prep_def_merge_tr_cl                  false
% 3.61/0.92  --smt_preprocessing                     true
% 3.61/0.92  --smt_ac_axioms                         fast
% 3.61/0.92  --preprocessed_out                      false
% 3.61/0.92  --preprocessed_stats                    false
% 3.61/0.92  
% 3.61/0.92  ------ Abstraction refinement Options
% 3.61/0.92  
% 3.61/0.92  --abstr_ref                             []
% 3.61/0.92  --abstr_ref_prep                        false
% 3.61/0.92  --abstr_ref_until_sat                   false
% 3.61/0.92  --abstr_ref_sig_restrict                funpre
% 3.61/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/0.92  --abstr_ref_under                       []
% 3.61/0.92  
% 3.61/0.92  ------ SAT Options
% 3.61/0.92  
% 3.61/0.92  --sat_mode                              false
% 3.61/0.92  --sat_fm_restart_options                ""
% 3.61/0.92  --sat_gr_def                            false
% 3.61/0.92  --sat_epr_types                         true
% 3.61/0.92  --sat_non_cyclic_types                  false
% 3.61/0.92  --sat_finite_models                     false
% 3.61/0.92  --sat_fm_lemmas                         false
% 3.61/0.92  --sat_fm_prep                           false
% 3.61/0.92  --sat_fm_uc_incr                        true
% 3.61/0.92  --sat_out_model                         small
% 3.61/0.92  --sat_out_clauses                       false
% 3.61/0.92  
% 3.61/0.92  ------ QBF Options
% 3.61/0.92  
% 3.61/0.92  --qbf_mode                              false
% 3.61/0.92  --qbf_elim_univ                         false
% 3.61/0.92  --qbf_dom_inst                          none
% 3.61/0.92  --qbf_dom_pre_inst                      false
% 3.61/0.92  --qbf_sk_in                             false
% 3.61/0.92  --qbf_pred_elim                         true
% 3.61/0.92  --qbf_split                             512
% 3.61/0.92  
% 3.61/0.92  ------ BMC1 Options
% 3.61/0.92  
% 3.61/0.92  --bmc1_incremental                      false
% 3.61/0.92  --bmc1_axioms                           reachable_all
% 3.61/0.92  --bmc1_min_bound                        0
% 3.61/0.92  --bmc1_max_bound                        -1
% 3.61/0.92  --bmc1_max_bound_default                -1
% 3.61/0.92  --bmc1_symbol_reachability              true
% 3.61/0.92  --bmc1_property_lemmas                  false
% 3.61/0.92  --bmc1_k_induction                      false
% 3.61/0.92  --bmc1_non_equiv_states                 false
% 3.61/0.92  --bmc1_deadlock                         false
% 3.61/0.92  --bmc1_ucm                              false
% 3.61/0.92  --bmc1_add_unsat_core                   none
% 3.61/0.92  --bmc1_unsat_core_children              false
% 3.61/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/0.92  --bmc1_out_stat                         full
% 3.61/0.92  --bmc1_ground_init                      false
% 3.61/0.92  --bmc1_pre_inst_next_state              false
% 3.61/0.92  --bmc1_pre_inst_state                   false
% 3.61/0.92  --bmc1_pre_inst_reach_state             false
% 3.61/0.92  --bmc1_out_unsat_core                   false
% 3.61/0.92  --bmc1_aig_witness_out                  false
% 3.61/0.92  --bmc1_verbose                          false
% 3.61/0.92  --bmc1_dump_clauses_tptp                false
% 3.61/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.61/0.92  --bmc1_dump_file                        -
% 3.61/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.61/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.61/0.92  --bmc1_ucm_extend_mode                  1
% 3.61/0.92  --bmc1_ucm_init_mode                    2
% 3.61/0.92  --bmc1_ucm_cone_mode                    none
% 3.61/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.61/0.92  --bmc1_ucm_relax_model                  4
% 3.61/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.61/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/0.92  --bmc1_ucm_layered_model                none
% 3.61/0.92  --bmc1_ucm_max_lemma_size               10
% 3.61/0.92  
% 3.61/0.92  ------ AIG Options
% 3.61/0.92  
% 3.61/0.92  --aig_mode                              false
% 3.61/0.92  
% 3.61/0.92  ------ Instantiation Options
% 3.61/0.92  
% 3.61/0.92  --instantiation_flag                    true
% 3.61/0.92  --inst_sos_flag                         false
% 3.61/0.92  --inst_sos_phase                        true
% 3.61/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/0.92  --inst_lit_sel_side                     num_symb
% 3.61/0.92  --inst_solver_per_active                1400
% 3.61/0.92  --inst_solver_calls_frac                1.
% 3.61/0.92  --inst_passive_queue_type               priority_queues
% 3.61/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/0.92  --inst_passive_queues_freq              [25;2]
% 3.61/0.92  --inst_dismatching                      true
% 3.61/0.92  --inst_eager_unprocessed_to_passive     true
% 3.61/0.92  --inst_prop_sim_given                   true
% 3.61/0.92  --inst_prop_sim_new                     false
% 3.61/0.92  --inst_subs_new                         false
% 3.61/0.92  --inst_eq_res_simp                      false
% 3.61/0.92  --inst_subs_given                       false
% 3.61/0.92  --inst_orphan_elimination               true
% 3.61/0.92  --inst_learning_loop_flag               true
% 3.61/0.92  --inst_learning_start                   3000
% 3.61/0.92  --inst_learning_factor                  2
% 3.61/0.92  --inst_start_prop_sim_after_learn       3
% 3.61/0.92  --inst_sel_renew                        solver
% 3.61/0.92  --inst_lit_activity_flag                true
% 3.61/0.92  --inst_restr_to_given                   false
% 3.61/0.92  --inst_activity_threshold               500
% 3.61/0.92  --inst_out_proof                        true
% 3.61/0.92  
% 3.61/0.92  ------ Resolution Options
% 3.61/0.92  
% 3.61/0.92  --resolution_flag                       true
% 3.61/0.92  --res_lit_sel                           adaptive
% 3.61/0.92  --res_lit_sel_side                      none
% 3.61/0.92  --res_ordering                          kbo
% 3.61/0.92  --res_to_prop_solver                    active
% 3.61/0.92  --res_prop_simpl_new                    false
% 3.61/0.92  --res_prop_simpl_given                  true
% 3.61/0.92  --res_passive_queue_type                priority_queues
% 3.61/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/0.92  --res_passive_queues_freq               [15;5]
% 3.61/0.92  --res_forward_subs                      full
% 3.61/0.92  --res_backward_subs                     full
% 3.61/0.92  --res_forward_subs_resolution           true
% 3.61/0.92  --res_backward_subs_resolution          true
% 3.61/0.92  --res_orphan_elimination                true
% 3.61/0.92  --res_time_limit                        2.
% 3.61/0.92  --res_out_proof                         true
% 3.61/0.92  
% 3.61/0.92  ------ Superposition Options
% 3.61/0.92  
% 3.61/0.92  --superposition_flag                    true
% 3.61/0.92  --sup_passive_queue_type                priority_queues
% 3.61/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.61/0.92  --demod_completeness_check              fast
% 3.61/0.92  --demod_use_ground                      true
% 3.61/0.92  --sup_to_prop_solver                    passive
% 3.61/0.92  --sup_prop_simpl_new                    true
% 3.61/0.92  --sup_prop_simpl_given                  true
% 3.61/0.92  --sup_fun_splitting                     false
% 3.61/0.92  --sup_smt_interval                      50000
% 3.61/0.92  
% 3.61/0.92  ------ Superposition Simplification Setup
% 3.61/0.92  
% 3.61/0.92  --sup_indices_passive                   []
% 3.61/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.92  --sup_full_bw                           [BwDemod]
% 3.61/0.92  --sup_immed_triv                        [TrivRules]
% 3.61/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.92  --sup_immed_bw_main                     []
% 3.61/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.92  
% 3.61/0.92  ------ Combination Options
% 3.61/0.92  
% 3.61/0.92  --comb_res_mult                         3
% 3.61/0.92  --comb_sup_mult                         2
% 3.61/0.92  --comb_inst_mult                        10
% 3.61/0.92  
% 3.61/0.92  ------ Debug Options
% 3.61/0.92  
% 3.61/0.92  --dbg_backtrace                         false
% 3.61/0.92  --dbg_dump_prop_clauses                 false
% 3.61/0.92  --dbg_dump_prop_clauses_file            -
% 3.61/0.92  --dbg_out_stat                          false
% 3.61/0.92  ------ Parsing...
% 3.61/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.92  
% 3.61/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.61/0.92  
% 3.61/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.92  
% 3.61/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.92  ------ Proving...
% 3.61/0.92  ------ Problem Properties 
% 3.61/0.92  
% 3.61/0.92  
% 3.61/0.92  clauses                                 36
% 3.61/0.92  conjectures                             3
% 3.61/0.92  EPR                                     2
% 3.61/0.92  Horn                                    30
% 3.61/0.92  unary                                   4
% 3.61/0.92  binary                                  13
% 3.61/0.92  lits                                    107
% 3.61/0.92  lits eq                                 42
% 3.61/0.92  fd_pure                                 0
% 3.61/0.92  fd_pseudo                               0
% 3.61/0.92  fd_cond                                 3
% 3.61/0.92  fd_pseudo_cond                          0
% 3.61/0.92  AC symbols                              0
% 3.61/0.92  
% 3.61/0.92  ------ Schedule dynamic 5 is on 
% 3.61/0.92  
% 3.61/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.61/0.92  
% 3.61/0.92  
% 3.61/0.92  ------ 
% 3.61/0.92  Current options:
% 3.61/0.92  ------ 
% 3.61/0.92  
% 3.61/0.92  ------ Input Options
% 3.61/0.92  
% 3.61/0.92  --out_options                           all
% 3.61/0.92  --tptp_safe_out                         true
% 3.61/0.92  --problem_path                          ""
% 3.61/0.92  --include_path                          ""
% 3.61/0.92  --clausifier                            res/vclausify_rel
% 3.61/0.92  --clausifier_options                    --mode clausify
% 3.61/0.92  --stdin                                 false
% 3.61/0.92  --stats_out                             all
% 3.61/0.92  
% 3.61/0.92  ------ General Options
% 3.61/0.92  
% 3.61/0.92  --fof                                   false
% 3.61/0.92  --time_out_real                         305.
% 3.61/0.92  --time_out_virtual                      -1.
% 3.61/0.92  --symbol_type_check                     false
% 3.61/0.92  --clausify_out                          false
% 3.61/0.92  --sig_cnt_out                           false
% 3.61/0.92  --trig_cnt_out                          false
% 3.61/0.92  --trig_cnt_out_tolerance                1.
% 3.61/0.92  --trig_cnt_out_sk_spl                   false
% 3.61/0.92  --abstr_cl_out                          false
% 3.61/0.92  
% 3.61/0.92  ------ Global Options
% 3.61/0.92  
% 3.61/0.92  --schedule                              default
% 3.61/0.92  --add_important_lit                     false
% 3.61/0.92  --prop_solver_per_cl                    1000
% 3.61/0.92  --min_unsat_core                        false
% 3.61/0.92  --soft_assumptions                      false
% 3.61/0.92  --soft_lemma_size                       3
% 3.61/0.92  --prop_impl_unit_size                   0
% 3.61/0.92  --prop_impl_unit                        []
% 3.61/0.92  --share_sel_clauses                     true
% 3.61/0.92  --reset_solvers                         false
% 3.61/0.92  --bc_imp_inh                            [conj_cone]
% 3.61/0.92  --conj_cone_tolerance                   3.
% 3.61/0.92  --extra_neg_conj                        none
% 3.61/0.92  --large_theory_mode                     true
% 3.61/0.92  --prolific_symb_bound                   200
% 3.61/0.92  --lt_threshold                          2000
% 3.61/0.92  --clause_weak_htbl                      true
% 3.61/0.92  --gc_record_bc_elim                     false
% 3.61/0.92  
% 3.61/0.92  ------ Preprocessing Options
% 3.61/0.92  
% 3.61/0.92  --preprocessing_flag                    true
% 3.61/0.92  --time_out_prep_mult                    0.1
% 3.61/0.92  --splitting_mode                        input
% 3.61/0.92  --splitting_grd                         true
% 3.61/0.92  --splitting_cvd                         false
% 3.61/0.92  --splitting_cvd_svl                     false
% 3.61/0.92  --splitting_nvd                         32
% 3.61/0.92  --sub_typing                            true
% 3.61/0.92  --prep_gs_sim                           true
% 3.61/0.92  --prep_unflatten                        true
% 3.61/0.92  --prep_res_sim                          true
% 3.61/0.92  --prep_upred                            true
% 3.61/0.92  --prep_sem_filter                       exhaustive
% 3.61/0.92  --prep_sem_filter_out                   false
% 3.61/0.92  --pred_elim                             true
% 3.61/0.92  --res_sim_input                         true
% 3.61/0.92  --eq_ax_congr_red                       true
% 3.61/0.92  --pure_diseq_elim                       true
% 3.61/0.92  --brand_transform                       false
% 3.61/0.92  --non_eq_to_eq                          false
% 3.61/0.92  --prep_def_merge                        true
% 3.61/0.92  --prep_def_merge_prop_impl              false
% 3.61/0.92  --prep_def_merge_mbd                    true
% 3.61/0.92  --prep_def_merge_tr_red                 false
% 3.61/0.92  --prep_def_merge_tr_cl                  false
% 3.61/0.92  --smt_preprocessing                     true
% 3.61/0.92  --smt_ac_axioms                         fast
% 3.61/0.92  --preprocessed_out                      false
% 3.61/0.92  --preprocessed_stats                    false
% 3.61/0.92  
% 3.61/0.92  ------ Abstraction refinement Options
% 3.61/0.92  
% 3.61/0.92  --abstr_ref                             []
% 3.61/0.92  --abstr_ref_prep                        false
% 3.61/0.92  --abstr_ref_until_sat                   false
% 3.61/0.92  --abstr_ref_sig_restrict                funpre
% 3.61/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/0.92  --abstr_ref_under                       []
% 3.61/0.92  
% 3.61/0.92  ------ SAT Options
% 3.61/0.92  
% 3.61/0.92  --sat_mode                              false
% 3.61/0.92  --sat_fm_restart_options                ""
% 3.61/0.92  --sat_gr_def                            false
% 3.61/0.92  --sat_epr_types                         true
% 3.61/0.92  --sat_non_cyclic_types                  false
% 3.61/0.92  --sat_finite_models                     false
% 3.61/0.92  --sat_fm_lemmas                         false
% 3.61/0.92  --sat_fm_prep                           false
% 3.61/0.92  --sat_fm_uc_incr                        true
% 3.61/0.92  --sat_out_model                         small
% 3.61/0.92  --sat_out_clauses                       false
% 3.61/0.92  
% 3.61/0.92  ------ QBF Options
% 3.61/0.92  
% 3.61/0.92  --qbf_mode                              false
% 3.61/0.92  --qbf_elim_univ                         false
% 3.61/0.92  --qbf_dom_inst                          none
% 3.61/0.92  --qbf_dom_pre_inst                      false
% 3.61/0.92  --qbf_sk_in                             false
% 3.61/0.92  --qbf_pred_elim                         true
% 3.61/0.92  --qbf_split                             512
% 3.61/0.92  
% 3.61/0.92  ------ BMC1 Options
% 3.61/0.92  
% 3.61/0.92  --bmc1_incremental                      false
% 3.61/0.92  --bmc1_axioms                           reachable_all
% 3.61/0.92  --bmc1_min_bound                        0
% 3.61/0.92  --bmc1_max_bound                        -1
% 3.61/0.92  --bmc1_max_bound_default                -1
% 3.61/0.92  --bmc1_symbol_reachability              true
% 3.61/0.92  --bmc1_property_lemmas                  false
% 3.61/0.92  --bmc1_k_induction                      false
% 3.61/0.92  --bmc1_non_equiv_states                 false
% 3.61/0.92  --bmc1_deadlock                         false
% 3.61/0.92  --bmc1_ucm                              false
% 3.61/0.92  --bmc1_add_unsat_core                   none
% 3.61/0.92  --bmc1_unsat_core_children              false
% 3.61/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/0.92  --bmc1_out_stat                         full
% 3.61/0.92  --bmc1_ground_init                      false
% 3.61/0.92  --bmc1_pre_inst_next_state              false
% 3.61/0.92  --bmc1_pre_inst_state                   false
% 3.61/0.92  --bmc1_pre_inst_reach_state             false
% 3.61/0.92  --bmc1_out_unsat_core                   false
% 3.61/0.92  --bmc1_aig_witness_out                  false
% 3.61/0.92  --bmc1_verbose                          false
% 3.61/0.92  --bmc1_dump_clauses_tptp                false
% 3.61/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.61/0.92  --bmc1_dump_file                        -
% 3.61/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.61/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.61/0.92  --bmc1_ucm_extend_mode                  1
% 3.61/0.92  --bmc1_ucm_init_mode                    2
% 3.61/0.92  --bmc1_ucm_cone_mode                    none
% 3.61/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.61/0.92  --bmc1_ucm_relax_model                  4
% 3.61/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.61/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/0.92  --bmc1_ucm_layered_model                none
% 3.61/0.92  --bmc1_ucm_max_lemma_size               10
% 3.61/0.92  
% 3.61/0.92  ------ AIG Options
% 3.61/0.92  
% 3.61/0.92  --aig_mode                              false
% 3.61/0.92  
% 3.61/0.92  ------ Instantiation Options
% 3.61/0.92  
% 3.61/0.92  --instantiation_flag                    true
% 3.61/0.92  --inst_sos_flag                         false
% 3.61/0.92  --inst_sos_phase                        true
% 3.61/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/0.92  --inst_lit_sel_side                     none
% 3.61/0.92  --inst_solver_per_active                1400
% 3.61/0.92  --inst_solver_calls_frac                1.
% 3.61/0.92  --inst_passive_queue_type               priority_queues
% 3.61/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/0.92  --inst_passive_queues_freq              [25;2]
% 3.61/0.92  --inst_dismatching                      true
% 3.61/0.92  --inst_eager_unprocessed_to_passive     true
% 3.61/0.92  --inst_prop_sim_given                   true
% 3.61/0.92  --inst_prop_sim_new                     false
% 3.61/0.92  --inst_subs_new                         false
% 3.61/0.92  --inst_eq_res_simp                      false
% 3.61/0.92  --inst_subs_given                       false
% 3.61/0.92  --inst_orphan_elimination               true
% 3.61/0.92  --inst_learning_loop_flag               true
% 3.61/0.92  --inst_learning_start                   3000
% 3.61/0.92  --inst_learning_factor                  2
% 3.61/0.92  --inst_start_prop_sim_after_learn       3
% 3.61/0.92  --inst_sel_renew                        solver
% 3.61/0.92  --inst_lit_activity_flag                true
% 3.61/0.92  --inst_restr_to_given                   false
% 3.61/0.92  --inst_activity_threshold               500
% 3.61/0.92  --inst_out_proof                        true
% 3.61/0.92  
% 3.61/0.92  ------ Resolution Options
% 3.61/0.92  
% 3.61/0.92  --resolution_flag                       false
% 3.61/0.92  --res_lit_sel                           adaptive
% 3.61/0.92  --res_lit_sel_side                      none
% 3.61/0.92  --res_ordering                          kbo
% 3.61/0.92  --res_to_prop_solver                    active
% 3.61/0.92  --res_prop_simpl_new                    false
% 3.61/0.92  --res_prop_simpl_given                  true
% 3.61/0.92  --res_passive_queue_type                priority_queues
% 3.61/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/0.92  --res_passive_queues_freq               [15;5]
% 3.61/0.92  --res_forward_subs                      full
% 3.61/0.92  --res_backward_subs                     full
% 3.61/0.92  --res_forward_subs_resolution           true
% 3.61/0.92  --res_backward_subs_resolution          true
% 3.61/0.92  --res_orphan_elimination                true
% 3.61/0.92  --res_time_limit                        2.
% 3.61/0.92  --res_out_proof                         true
% 3.61/0.92  
% 3.61/0.92  ------ Superposition Options
% 3.61/0.92  
% 3.61/0.92  --superposition_flag                    true
% 3.61/0.92  --sup_passive_queue_type                priority_queues
% 3.61/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.61/0.92  --demod_completeness_check              fast
% 3.61/0.92  --demod_use_ground                      true
% 3.61/0.92  --sup_to_prop_solver                    passive
% 3.61/0.92  --sup_prop_simpl_new                    true
% 3.61/0.92  --sup_prop_simpl_given                  true
% 3.61/0.92  --sup_fun_splitting                     false
% 3.61/0.92  --sup_smt_interval                      50000
% 3.61/0.92  
% 3.61/0.92  ------ Superposition Simplification Setup
% 3.61/0.92  
% 3.61/0.92  --sup_indices_passive                   []
% 3.61/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.92  --sup_full_bw                           [BwDemod]
% 3.61/0.92  --sup_immed_triv                        [TrivRules]
% 3.61/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.92  --sup_immed_bw_main                     []
% 3.61/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.92  
% 3.61/0.92  ------ Combination Options
% 3.61/0.92  
% 3.61/0.92  --comb_res_mult                         3
% 3.61/0.92  --comb_sup_mult                         2
% 3.61/0.92  --comb_inst_mult                        10
% 3.61/0.92  
% 3.61/0.92  ------ Debug Options
% 3.61/0.92  
% 3.61/0.92  --dbg_backtrace                         false
% 3.61/0.92  --dbg_dump_prop_clauses                 false
% 3.61/0.92  --dbg_dump_prop_clauses_file            -
% 3.61/0.92  --dbg_out_stat                          false
% 3.61/0.92  
% 3.61/0.92  
% 3.61/0.92  
% 3.61/0.92  
% 3.61/0.92  ------ Proving...
% 3.61/0.92  
% 3.61/0.92  
% 3.61/0.92  % SZS status Theorem for theBenchmark.p
% 3.61/0.92  
% 3.61/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.92  
% 3.61/0.92  fof(f6,axiom,(
% 3.61/0.92    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f24,plain,(
% 3.61/0.92    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.61/0.92    inference(ennf_transformation,[],[f6])).
% 3.61/0.92  
% 3.61/0.92  fof(f25,plain,(
% 3.61/0.92    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/0.92    inference(flattening,[],[f24])).
% 3.61/0.92  
% 3.61/0.92  fof(f52,plain,(
% 3.61/0.92    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.92    inference(cnf_transformation,[],[f25])).
% 3.61/0.92  
% 3.61/0.92  fof(f16,conjecture,(
% 3.61/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f17,negated_conjecture,(
% 3.61/0.92    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.61/0.92    inference(negated_conjecture,[],[f16])).
% 3.61/0.92  
% 3.61/0.92  fof(f38,plain,(
% 3.61/0.92    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.61/0.92    inference(ennf_transformation,[],[f17])).
% 3.61/0.92  
% 3.61/0.92  fof(f39,plain,(
% 3.61/0.92    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.61/0.92    inference(flattening,[],[f38])).
% 3.61/0.92  
% 3.61/0.92  fof(f42,plain,(
% 3.61/0.92    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.61/0.92    introduced(choice_axiom,[])).
% 3.61/0.92  
% 3.61/0.92  fof(f43,plain,(
% 3.61/0.92    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.61/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42])).
% 3.61/0.92  
% 3.61/0.92  fof(f75,plain,(
% 3.61/0.92    v2_funct_1(sK2)),
% 3.61/0.92    inference(cnf_transformation,[],[f43])).
% 3.61/0.92  
% 3.61/0.92  fof(f72,plain,(
% 3.61/0.92    v1_funct_1(sK2)),
% 3.61/0.92    inference(cnf_transformation,[],[f43])).
% 3.61/0.92  
% 3.61/0.92  fof(f74,plain,(
% 3.61/0.92    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.61/0.92    inference(cnf_transformation,[],[f43])).
% 3.61/0.92  
% 3.61/0.92  fof(f7,axiom,(
% 3.61/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f26,plain,(
% 3.61/0.92    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.92    inference(ennf_transformation,[],[f7])).
% 3.61/0.92  
% 3.61/0.92  fof(f53,plain,(
% 3.61/0.92    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.92    inference(cnf_transformation,[],[f26])).
% 3.61/0.92  
% 3.61/0.92  fof(f14,axiom,(
% 3.61/0.92    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f34,plain,(
% 3.61/0.92    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.61/0.92    inference(ennf_transformation,[],[f14])).
% 3.61/0.92  
% 3.61/0.92  fof(f35,plain,(
% 3.61/0.92    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/0.92    inference(flattening,[],[f34])).
% 3.61/0.92  
% 3.61/0.92  fof(f68,plain,(
% 3.61/0.92    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.92    inference(cnf_transformation,[],[f35])).
% 3.61/0.92  
% 3.61/0.92  fof(f10,axiom,(
% 3.61/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f29,plain,(
% 3.61/0.92    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.92    inference(ennf_transformation,[],[f10])).
% 3.61/0.92  
% 3.61/0.92  fof(f56,plain,(
% 3.61/0.92    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.92    inference(cnf_transformation,[],[f29])).
% 3.61/0.92  
% 3.61/0.92  fof(f76,plain,(
% 3.61/0.92    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.61/0.92    inference(cnf_transformation,[],[f43])).
% 3.61/0.92  
% 3.61/0.92  fof(f51,plain,(
% 3.61/0.92    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.92    inference(cnf_transformation,[],[f25])).
% 3.61/0.92  
% 3.61/0.92  fof(f3,axiom,(
% 3.61/0.92    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f18,plain,(
% 3.61/0.92    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.61/0.92    inference(ennf_transformation,[],[f3])).
% 3.61/0.92  
% 3.61/0.92  fof(f19,plain,(
% 3.61/0.92    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/0.92    inference(flattening,[],[f18])).
% 3.61/0.92  
% 3.61/0.92  fof(f48,plain,(
% 3.61/0.92    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.92    inference(cnf_transformation,[],[f19])).
% 3.61/0.92  
% 3.61/0.92  fof(f47,plain,(
% 3.61/0.92    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.92    inference(cnf_transformation,[],[f19])).
% 3.61/0.92  
% 3.61/0.92  fof(f8,axiom,(
% 3.61/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f27,plain,(
% 3.61/0.92    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.92    inference(ennf_transformation,[],[f8])).
% 3.61/0.92  
% 3.61/0.92  fof(f54,plain,(
% 3.61/0.92    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.92    inference(cnf_transformation,[],[f27])).
% 3.61/0.92  
% 3.61/0.92  fof(f13,axiom,(
% 3.61/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f32,plain,(
% 3.61/0.92    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.92    inference(ennf_transformation,[],[f13])).
% 3.61/0.92  
% 3.61/0.92  fof(f33,plain,(
% 3.61/0.92    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.92    inference(flattening,[],[f32])).
% 3.61/0.92  
% 3.61/0.92  fof(f41,plain,(
% 3.61/0.92    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.92    inference(nnf_transformation,[],[f33])).
% 3.61/0.92  
% 3.61/0.92  fof(f60,plain,(
% 3.61/0.92    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.92    inference(cnf_transformation,[],[f41])).
% 3.61/0.92  
% 3.61/0.92  fof(f73,plain,(
% 3.61/0.92    v1_funct_2(sK2,sK0,sK1)),
% 3.61/0.92    inference(cnf_transformation,[],[f43])).
% 3.61/0.92  
% 3.61/0.92  fof(f9,axiom,(
% 3.61/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f28,plain,(
% 3.61/0.92    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.92    inference(ennf_transformation,[],[f9])).
% 3.61/0.92  
% 3.61/0.92  fof(f55,plain,(
% 3.61/0.92    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.92    inference(cnf_transformation,[],[f28])).
% 3.61/0.92  
% 3.61/0.92  fof(f67,plain,(
% 3.61/0.92    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.92    inference(cnf_transformation,[],[f35])).
% 3.61/0.92  
% 3.61/0.92  fof(f77,plain,(
% 3.61/0.92    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.61/0.92    inference(cnf_transformation,[],[f43])).
% 3.61/0.92  
% 3.61/0.92  fof(f64,plain,(
% 3.61/0.92    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.92    inference(cnf_transformation,[],[f41])).
% 3.61/0.92  
% 3.61/0.92  fof(f80,plain,(
% 3.61/0.92    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.61/0.92    inference(equality_resolution,[],[f64])).
% 3.61/0.92  
% 3.61/0.92  fof(f1,axiom,(
% 3.61/0.92    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f44,plain,(
% 3.61/0.92    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.61/0.92    inference(cnf_transformation,[],[f1])).
% 3.61/0.92  
% 3.61/0.92  fof(f2,axiom,(
% 3.61/0.92    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f40,plain,(
% 3.61/0.92    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.61/0.92    inference(nnf_transformation,[],[f2])).
% 3.61/0.92  
% 3.61/0.92  fof(f46,plain,(
% 3.61/0.92    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.61/0.92    inference(cnf_transformation,[],[f40])).
% 3.61/0.92  
% 3.61/0.92  fof(f15,axiom,(
% 3.61/0.92    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f36,plain,(
% 3.61/0.92    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.61/0.92    inference(ennf_transformation,[],[f15])).
% 3.61/0.92  
% 3.61/0.92  fof(f37,plain,(
% 3.61/0.92    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.61/0.92    inference(flattening,[],[f36])).
% 3.61/0.92  
% 3.61/0.92  fof(f71,plain,(
% 3.61/0.92    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.61/0.92    inference(cnf_transformation,[],[f37])).
% 3.61/0.92  
% 3.61/0.92  fof(f70,plain,(
% 3.61/0.92    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.61/0.92    inference(cnf_transformation,[],[f37])).
% 3.61/0.92  
% 3.61/0.92  fof(f45,plain,(
% 3.61/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.61/0.92    inference(cnf_transformation,[],[f40])).
% 3.61/0.92  
% 3.61/0.92  fof(f5,axiom,(
% 3.61/0.92    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f22,plain,(
% 3.61/0.92    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.61/0.92    inference(ennf_transformation,[],[f5])).
% 3.61/0.92  
% 3.61/0.92  fof(f23,plain,(
% 3.61/0.92    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.61/0.92    inference(flattening,[],[f22])).
% 3.61/0.92  
% 3.61/0.92  fof(f50,plain,(
% 3.61/0.92    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.61/0.92    inference(cnf_transformation,[],[f23])).
% 3.61/0.92  
% 3.61/0.92  fof(f11,axiom,(
% 3.61/0.92    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f30,plain,(
% 3.61/0.92    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.92    inference(ennf_transformation,[],[f11])).
% 3.61/0.92  
% 3.61/0.92  fof(f57,plain,(
% 3.61/0.92    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.92    inference(cnf_transformation,[],[f30])).
% 3.61/0.92  
% 3.61/0.92  fof(f12,axiom,(
% 3.61/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.61/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.92  
% 3.61/0.92  fof(f31,plain,(
% 3.61/0.92    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.92    inference(ennf_transformation,[],[f12])).
% 3.61/0.92  
% 3.61/0.92  fof(f58,plain,(
% 3.61/0.92    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.92    inference(cnf_transformation,[],[f31])).
% 3.61/0.92  
% 3.61/0.92  cnf(c_7,plain,
% 3.61/0.92      ( ~ v2_funct_1(X0)
% 3.61/0.92      | ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0)
% 3.61/0.92      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.61/0.92      inference(cnf_transformation,[],[f52]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_30,negated_conjecture,
% 3.61/0.92      ( v2_funct_1(sK2) ),
% 3.61/0.92      inference(cnf_transformation,[],[f75]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_463,plain,
% 3.61/0.92      ( ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0)
% 3.61/0.92      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.61/0.92      | sK2 != X0 ),
% 3.61/0.92      inference(resolution_lifted,[status(thm)],[c_7,c_30]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_464,plain,
% 3.61/0.92      ( ~ v1_relat_1(sK2)
% 3.61/0.92      | ~ v1_funct_1(sK2)
% 3.61/0.92      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.61/0.92      inference(unflattening,[status(thm)],[c_463]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_33,negated_conjecture,
% 3.61/0.92      ( v1_funct_1(sK2) ),
% 3.61/0.92      inference(cnf_transformation,[],[f72]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_466,plain,
% 3.61/0.92      ( ~ v1_relat_1(sK2)
% 3.61/0.92      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_464,c_33]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2087,plain,
% 3.61/0.92      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.61/0.92      | v1_relat_1(sK2) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_31,negated_conjecture,
% 3.61/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.61/0.92      inference(cnf_transformation,[],[f74]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_9,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.92      | v1_relat_1(X0) ),
% 3.61/0.92      inference(cnf_transformation,[],[f53]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2404,plain,
% 3.61/0.92      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.61/0.92      | v1_relat_1(sK2) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_9]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2413,plain,
% 3.61/0.92      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_2087,c_33,c_31,c_464,c_2404]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_22,plain,
% 3.61/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.61/0.92      | ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0) ),
% 3.61/0.92      inference(cnf_transformation,[],[f68]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2093,plain,
% 3.61/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.61/0.92      | v1_relat_1(X0) != iProver_top
% 3.61/0.92      | v1_funct_1(X0) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4179,plain,
% 3.61/0.92      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 3.61/0.92      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.61/0.92      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_2413,c_2093]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2091,plain,
% 3.61/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_12,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.92      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.61/0.92      inference(cnf_transformation,[],[f56]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2097,plain,
% 3.61/0.92      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.61/0.92      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2863,plain,
% 3.61/0.92      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_2091,c_2097]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_29,negated_conjecture,
% 3.61/0.92      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.61/0.92      inference(cnf_transformation,[],[f76]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2865,plain,
% 3.61/0.92      ( k2_relat_1(sK2) = sK1 ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_2863,c_29]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_8,plain,
% 3.61/0.92      ( ~ v2_funct_1(X0)
% 3.61/0.92      | ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0)
% 3.61/0.92      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.61/0.92      inference(cnf_transformation,[],[f51]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_449,plain,
% 3.61/0.92      ( ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0)
% 3.61/0.92      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.61/0.92      | sK2 != X0 ),
% 3.61/0.92      inference(resolution_lifted,[status(thm)],[c_8,c_30]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_450,plain,
% 3.61/0.92      ( ~ v1_relat_1(sK2)
% 3.61/0.92      | ~ v1_funct_1(sK2)
% 3.61/0.92      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.61/0.92      inference(unflattening,[status(thm)],[c_449]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_452,plain,
% 3.61/0.92      ( ~ v1_relat_1(sK2)
% 3.61/0.92      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_450,c_33]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2088,plain,
% 3.61/0.92      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.61/0.92      | v1_relat_1(sK2) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2417,plain,
% 3.61/0.92      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_2088,c_33,c_31,c_450,c_2404]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2876,plain,
% 3.61/0.92      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.61/0.92      inference(demodulation,[status(thm)],[c_2865,c_2417]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4226,plain,
% 3.61/0.92      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 3.61/0.92      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.61/0.92      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_4179,c_2876]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_34,plain,
% 3.61/0.92      ( v1_funct_1(sK2) = iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_36,plain,
% 3.61/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2405,plain,
% 3.61/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.61/0.92      | v1_relat_1(sK2) = iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_2404]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_3,plain,
% 3.61/0.92      ( ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0)
% 3.61/0.92      | v1_funct_1(k2_funct_1(X0)) ),
% 3.61/0.92      inference(cnf_transformation,[],[f48]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2483,plain,
% 3.61/0.92      ( ~ v1_relat_1(sK2)
% 3.61/0.92      | v1_funct_1(k2_funct_1(sK2))
% 3.61/0.92      | ~ v1_funct_1(sK2) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_3]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2484,plain,
% 3.61/0.92      ( v1_relat_1(sK2) != iProver_top
% 3.61/0.92      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.61/0.92      | v1_funct_1(sK2) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_2483]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4,plain,
% 3.61/0.92      ( ~ v1_relat_1(X0)
% 3.61/0.92      | v1_relat_1(k2_funct_1(X0))
% 3.61/0.92      | ~ v1_funct_1(X0) ),
% 3.61/0.92      inference(cnf_transformation,[],[f47]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2482,plain,
% 3.61/0.92      ( v1_relat_1(k2_funct_1(sK2))
% 3.61/0.92      | ~ v1_relat_1(sK2)
% 3.61/0.92      | ~ v1_funct_1(sK2) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_4]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2486,plain,
% 3.61/0.92      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.61/0.92      | v1_relat_1(sK2) != iProver_top
% 3.61/0.92      | v1_funct_1(sK2) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_2482]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5152,plain,
% 3.61/0.92      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_4226,c_34,c_36,c_2405,c_2484,c_2486]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5163,plain,
% 3.61/0.92      ( k2_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_5152,c_2097]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5168,plain,
% 3.61/0.92      ( k2_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_5163,c_2413]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_10,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.92      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.61/0.92      inference(cnf_transformation,[],[f54]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2099,plain,
% 3.61/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.92      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5220,plain,
% 3.61/0.92      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) != iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_5168,c_2099]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_9000,plain,
% 3.61/0.92      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_5220,c_34,c_36,c_2405,c_2484,c_2486,c_4226]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_21,plain,
% 3.61/0.92      ( ~ v1_funct_2(X0,X1,X2)
% 3.61/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.92      | k1_relset_1(X1,X2,X0) = X1
% 3.61/0.92      | k1_xboole_0 = X2 ),
% 3.61/0.92      inference(cnf_transformation,[],[f60]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_32,negated_conjecture,
% 3.61/0.92      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.61/0.92      inference(cnf_transformation,[],[f73]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_890,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.92      | k1_relset_1(X1,X2,X0) = X1
% 3.61/0.92      | sK0 != X1
% 3.61/0.92      | sK1 != X2
% 3.61/0.92      | sK2 != X0
% 3.61/0.92      | k1_xboole_0 = X2 ),
% 3.61/0.92      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_891,plain,
% 3.61/0.92      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.61/0.92      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.61/0.92      | k1_xboole_0 = sK1 ),
% 3.61/0.92      inference(unflattening,[status(thm)],[c_890]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_893,plain,
% 3.61/0.92      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_891,c_31]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_11,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.92      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.61/0.92      inference(cnf_transformation,[],[f55]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2098,plain,
% 3.61/0.92      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.61/0.92      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2923,plain,
% 3.61/0.92      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_2091,c_2098]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_3015,plain,
% 3.61/0.92      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_893,c_2923]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5162,plain,
% 3.61/0.92      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_5152,c_2098]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5171,plain,
% 3.61/0.92      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_5162,c_2876]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5217,plain,
% 3.61/0.92      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1 | sK1 = k1_xboole_0 ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_3015,c_5171]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_23,plain,
% 3.61/0.92      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.61/0.92      | ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0) ),
% 3.61/0.92      inference(cnf_transformation,[],[f67]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_28,negated_conjecture,
% 3.61/0.92      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.61/0.92      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.61/0.92      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.61/0.92      inference(cnf_transformation,[],[f77]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_901,plain,
% 3.61/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.61/0.92      | ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0)
% 3.61/0.92      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.61/0.92      | k2_relat_1(X0) != sK0
% 3.61/0.92      | k1_relat_1(X0) != sK1
% 3.61/0.92      | k2_funct_1(sK2) != X0 ),
% 3.61/0.92      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_902,plain,
% 3.61/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.61/0.92      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.61/0.92      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.61/0.92      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.61/0.92      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.61/0.92      inference(unflattening,[status(thm)],[c_901]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_914,plain,
% 3.61/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.61/0.92      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.61/0.92      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.61/0.92      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.61/0.92      inference(forward_subsumption_resolution,[status(thm)],[c_902,c_9]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2074,plain,
% 3.61/0.92      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.61/0.92      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.61/0.92      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_914]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_903,plain,
% 3.61/0.92      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.61/0.92      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.61/0.92      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.61/0.92      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_902]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_3230,plain,
% 3.61/0.92      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.61/0.92      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_2074,c_34,c_36,c_903,c_2405,c_2484,c_2486,c_2876]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_3231,plain,
% 3.61/0.92      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.61/0.92      inference(renaming,[status(thm)],[c_3230]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_3234,plain,
% 3.61/0.92      ( k1_relat_1(sK2) != sK0
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_3231,c_2413]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_3238,plain,
% 3.61/0.92      ( sK1 = k1_xboole_0
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_3015,c_3234]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5157,plain,
% 3.61/0.92      ( sK1 = k1_xboole_0
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_3015,c_5152]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5988,plain,
% 3.61/0.92      ( sK1 = k1_xboole_0 ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_5217,c_3238,c_5157]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_17,plain,
% 3.61/0.92      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.61/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.61/0.92      | k1_xboole_0 = X1
% 3.61/0.92      | k1_xboole_0 = X0 ),
% 3.61/0.92      inference(cnf_transformation,[],[f80]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_722,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.61/0.92      | sK0 != X1
% 3.61/0.92      | sK1 != k1_xboole_0
% 3.61/0.92      | sK2 != X0
% 3.61/0.92      | k1_xboole_0 = X0
% 3.61/0.92      | k1_xboole_0 = X1 ),
% 3.61/0.92      inference(resolution_lifted,[status(thm)],[c_17,c_32]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_723,plain,
% 3.61/0.92      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 3.61/0.92      | sK1 != k1_xboole_0
% 3.61/0.92      | k1_xboole_0 = sK0
% 3.61/0.92      | k1_xboole_0 = sK2 ),
% 3.61/0.92      inference(unflattening,[status(thm)],[c_722]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2082,plain,
% 3.61/0.92      ( sK1 != k1_xboole_0
% 3.61/0.92      | k1_xboole_0 = sK0
% 3.61/0.92      | k1_xboole_0 = sK2
% 3.61/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_6023,plain,
% 3.61/0.92      ( sK0 = k1_xboole_0
% 3.61/0.92      | sK2 = k1_xboole_0
% 3.61/0.92      | k1_xboole_0 != k1_xboole_0
% 3.61/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.61/0.92      inference(demodulation,[status(thm)],[c_5988,c_2082]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_6064,plain,
% 3.61/0.92      ( sK0 = k1_xboole_0
% 3.61/0.92      | sK2 = k1_xboole_0
% 3.61/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.61/0.92      inference(equality_resolution_simp,[status(thm)],[c_6023]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_6031,plain,
% 3.61/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.61/0.92      inference(demodulation,[status(thm)],[c_5988,c_2091]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_6068,plain,
% 3.61/0.92      ( sK0 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.61/0.92      inference(forward_subsumption_resolution,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_6064,c_6031]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_0,plain,
% 3.61/0.92      ( r1_tarski(k1_xboole_0,X0) ),
% 3.61/0.92      inference(cnf_transformation,[],[f44]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_117,plain,
% 3.61/0.92      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_0]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_1305,plain,( X0 = X0 ),theory(equality) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2547,plain,
% 3.61/0.92      ( sK0 = sK0 ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_1305]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_1308,plain,
% 3.61/0.92      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.61/0.92      theory(equality) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_3806,plain,
% 3.61/0.92      ( k1_zfmisc_1(sK0) = k1_zfmisc_1(sK0) | sK0 != sK0 ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_1308]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_1,plain,
% 3.61/0.92      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.61/0.92      inference(cnf_transformation,[],[f46]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4331,plain,
% 3.61/0.92      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~ r1_tarski(X0,sK0) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_1]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4333,plain,
% 3.61/0.92      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
% 3.61/0.92      | ~ r1_tarski(k1_xboole_0,sK0) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_4331]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4375,plain,
% 3.61/0.92      ( r1_tarski(k1_xboole_0,sK0) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_0]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_25,plain,
% 3.61/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.61/0.92      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.61/0.92      | ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0) ),
% 3.61/0.92      inference(cnf_transformation,[],[f71]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2092,plain,
% 3.61/0.92      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.61/0.92      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.61/0.92      | v1_relat_1(X0) != iProver_top
% 3.61/0.92      | v1_funct_1(X0) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4675,plain,
% 3.61/0.92      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.61/0.92      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 3.61/0.92      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.61/0.92      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_2876,c_2092]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4735,plain,
% 3.61/0.92      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.61/0.92      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 3.61/0.92      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.61/0.92      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_4675,c_2413]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5281,plain,
% 3.61/0.92      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.61/0.92      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_4735,c_34,c_36,c_2405,c_2484,c_2486]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_26,plain,
% 3.61/0.92      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.61/0.92      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.61/0.92      | ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0) ),
% 3.61/0.92      inference(cnf_transformation,[],[f70]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_920,plain,
% 3.61/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.61/0.92      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.61/0.92      | ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0)
% 3.61/0.92      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.61/0.92      | k1_relat_1(X0) != sK1
% 3.61/0.92      | k2_funct_1(sK2) != X0
% 3.61/0.92      | sK0 != X1 ),
% 3.61/0.92      inference(resolution_lifted,[status(thm)],[c_26,c_28]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_921,plain,
% 3.61/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.61/0.92      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.61/0.92      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.61/0.92      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.61/0.92      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.61/0.92      inference(unflattening,[status(thm)],[c_920]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_933,plain,
% 3.61/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.61/0.92      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.61/0.92      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.61/0.92      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.61/0.92      inference(forward_subsumption_resolution,[status(thm)],[c_921,c_9]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2073,plain,
% 3.61/0.92      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.61/0.92      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.61/0.92      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_922,plain,
% 3.61/0.92      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.61/0.92      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.61/0.92      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.61/0.92      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2803,plain,
% 3.61/0.92      ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.61/0.92      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_2073,c_34,c_36,c_922,c_2405,c_2484,c_2486]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2804,plain,
% 3.61/0.92      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.61/0.92      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
% 3.61/0.92      inference(renaming,[status(thm)],[c_2803]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2807,plain,
% 3.61/0.92      ( k2_relat_1(sK2) != sK1
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.61/0.92      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_2804,c_2413,c_2417]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2875,plain,
% 3.61/0.92      ( sK1 != sK1
% 3.61/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.61/0.92      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.61/0.92      inference(demodulation,[status(thm)],[c_2865,c_2807]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2879,plain,
% 3.61/0.92      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.61/0.92      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.61/0.92      inference(equality_resolution_simp,[status(thm)],[c_2875]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5297,plain,
% 3.61/0.92      ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_5281,c_2879]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5336,plain,
% 3.61/0.92      ( ~ r1_tarski(k1_relat_1(sK2),sK0) ),
% 3.61/0.92      inference(predicate_to_equality_rev,[status(thm)],[c_5297]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.61/0.92      inference(cnf_transformation,[],[f45]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4380,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(X0,sK0) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_2]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5960,plain,
% 3.61/0.92      ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
% 3.61/0.92      | r1_tarski(k1_relat_1(sK2),sK0) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_4380]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_6022,plain,
% 3.61/0.92      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 3.61/0.92      inference(demodulation,[status(thm)],[c_5988,c_2865]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_696,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.61/0.92      | ~ r1_tarski(k2_relat_1(X2),X3)
% 3.61/0.92      | ~ v1_relat_1(X2)
% 3.61/0.92      | ~ v1_funct_1(X2)
% 3.61/0.92      | X2 != X0
% 3.61/0.92      | k1_relat_1(X2) != X1
% 3.61/0.92      | k1_xboole_0 != X3
% 3.61/0.92      | k1_xboole_0 = X0
% 3.61/0.92      | k1_xboole_0 = X1 ),
% 3.61/0.92      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_697,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.61/0.92      | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 3.61/0.92      | ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0)
% 3.61/0.92      | k1_xboole_0 = X0
% 3.61/0.92      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.61/0.92      inference(unflattening,[status(thm)],[c_696]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_713,plain,
% 3.61/0.92      ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 3.61/0.92      | ~ v1_relat_1(X0)
% 3.61/0.92      | ~ v1_funct_1(X0)
% 3.61/0.92      | k1_xboole_0 = X0
% 3.61/0.92      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.61/0.92      inference(forward_subsumption_resolution,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_697,c_25]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2083,plain,
% 3.61/0.92      ( k1_xboole_0 = X0
% 3.61/0.92      | k1_xboole_0 = k1_relat_1(X0)
% 3.61/0.92      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.61/0.92      | v1_relat_1(X0) != iProver_top
% 3.61/0.92      | v1_funct_1(X0) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_6290,plain,
% 3.61/0.92      ( k1_relat_1(sK2) = k1_xboole_0
% 3.61/0.92      | sK2 = k1_xboole_0
% 3.61/0.92      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.61/0.92      | v1_relat_1(sK2) != iProver_top
% 3.61/0.92      | v1_funct_1(sK2) != iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_6022,c_2083]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_6302,plain,
% 3.61/0.92      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.61/0.92      | ~ v1_relat_1(sK2)
% 3.61/0.92      | ~ v1_funct_1(sK2)
% 3.61/0.92      | k1_relat_1(sK2) = k1_xboole_0
% 3.61/0.92      | sK2 = k1_xboole_0 ),
% 3.61/0.92      inference(predicate_to_equality_rev,[status(thm)],[c_6290]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_1309,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.61/0.92      theory(equality) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2451,plain,
% 3.61/0.92      ( m1_subset_1(X0,X1)
% 3.61/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.61/0.92      | X0 != X2
% 3.61/0.92      | X1 != k1_zfmisc_1(X3) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_1309]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2566,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/0.92      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.61/0.92      | X2 != X0
% 3.61/0.92      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_2451]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4351,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
% 3.61/0.92      | m1_subset_1(X1,k1_zfmisc_1(sK0))
% 3.61/0.92      | X1 != X0
% 3.61/0.92      | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_2566]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_6449,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
% 3.61/0.92      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
% 3.61/0.92      | k1_relat_1(sK2) != X0
% 3.61/0.92      | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_4351]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_6451,plain,
% 3.61/0.92      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
% 3.61/0.92      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
% 3.61/0.92      | k1_relat_1(sK2) != k1_xboole_0
% 3.61/0.92      | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_6449]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_7560,plain,
% 3.61/0.92      ( sK2 = k1_xboole_0 ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_6068,c_33,c_31,c_117,c_2404,c_2547,c_3806,c_4333,
% 3.61/0.92                 c_4375,c_5336,c_5960,c_6302,c_6451]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_9004,plain,
% 3.61/0.92      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_relat_1(k1_xboole_0))) = iProver_top ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_9000,c_7560]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2103,plain,
% 3.61/0.92      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.61/0.92      | r1_tarski(X0,X1) = iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_9007,plain,
% 3.61/0.92      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_9004,c_2103]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_6,plain,
% 3.61/0.92      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.61/0.92      | ~ v2_funct_1(X1)
% 3.61/0.92      | ~ v1_relat_1(X1)
% 3.61/0.92      | ~ v1_funct_1(X1)
% 3.61/0.92      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.61/0.92      inference(cnf_transformation,[],[f50]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_428,plain,
% 3.61/0.92      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.61/0.92      | ~ v1_relat_1(X1)
% 3.61/0.92      | ~ v1_funct_1(X1)
% 3.61/0.92      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 3.61/0.92      | sK2 != X1 ),
% 3.61/0.92      inference(resolution_lifted,[status(thm)],[c_6,c_30]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_429,plain,
% 3.61/0.92      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.61/0.92      | ~ v1_relat_1(sK2)
% 3.61/0.92      | ~ v1_funct_1(sK2)
% 3.61/0.92      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.61/0.92      inference(unflattening,[status(thm)],[c_428]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_433,plain,
% 3.61/0.92      ( ~ v1_relat_1(sK2)
% 3.61/0.92      | ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.61/0.92      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_429,c_33]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_434,plain,
% 3.61/0.92      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.61/0.92      | ~ v1_relat_1(sK2)
% 3.61/0.92      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.61/0.92      inference(renaming,[status(thm)],[c_433]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2089,plain,
% 3.61/0.92      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.61/0.92      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.61/0.92      | v1_relat_1(sK2) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_435,plain,
% 3.61/0.92      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.61/0.92      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.61/0.92      | v1_relat_1(sK2) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2663,plain,
% 3.61/0.92      ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.61/0.92      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_2089,c_36,c_435,c_2405]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2664,plain,
% 3.61/0.92      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 3.61/0.92      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 3.61/0.92      inference(renaming,[status(thm)],[c_2663]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_7582,plain,
% 3.61/0.92      ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = X0
% 3.61/0.92      | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 3.61/0.92      inference(demodulation,[status(thm)],[c_7560,c_2664]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_9409,plain,
% 3.61/0.92      ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))) = k1_relat_1(k1_xboole_0) ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_9007,c_7582]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4178,plain,
% 3.61/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
% 3.61/0.92      | v1_relat_1(sK2) != iProver_top
% 3.61/0.92      | v1_funct_1(sK2) != iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_2865,c_2093]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4277,plain,
% 3.61/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top ),
% 3.61/0.92      inference(global_propositional_subsumption,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_4178,c_34,c_36,c_2405]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_13,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.92      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.61/0.92      inference(cnf_transformation,[],[f57]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2096,plain,
% 3.61/0.92      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.61/0.92      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4286,plain,
% 3.61/0.92      ( k7_relset_1(k1_relat_1(sK2),sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_4277,c_2096]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_15,plain,
% 3.61/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.92      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 3.61/0.92      inference(cnf_transformation,[],[f58]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2094,plain,
% 3.61/0.92      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 3.61/0.92      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4285,plain,
% 3.61/0.92      ( k7_relset_1(k1_relat_1(sK2),sK1,sK2,k1_relat_1(sK2)) = k2_relset_1(k1_relat_1(sK2),sK1,sK2) ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_4277,c_2094]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4288,plain,
% 3.61/0.92      ( k2_relset_1(k1_relat_1(sK2),sK1,sK2) = k2_relat_1(sK2) ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_4277,c_2097]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4291,plain,
% 3.61/0.92      ( k2_relset_1(k1_relat_1(sK2),sK1,sK2) = sK1 ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_4288,c_2865]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4297,plain,
% 3.61/0.92      ( k7_relset_1(k1_relat_1(sK2),sK1,sK2,k1_relat_1(sK2)) = sK1 ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_4285,c_4291]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4548,plain,
% 3.61/0.92      ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK1 ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_4286,c_4297]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_9165,plain,
% 3.61/0.92      ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_4548,c_5988,c_7560]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_9410,plain,
% 3.61/0.92      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_9409,c_9165]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_7576,plain,
% 3.61/0.92      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.61/0.92      inference(demodulation,[status(thm)],[c_7560,c_6022]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2104,plain,
% 3.61/0.92      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.61/0.92      | r1_tarski(X0,X1) != iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2105,plain,
% 3.61/0.92      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.61/0.92      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2862,plain,
% 3.61/0.92      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.61/0.92      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_2104,c_2097]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4863,plain,
% 3.61/0.92      ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_2105,c_2862]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_5530,plain,
% 3.61/0.92      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
% 3.61/0.92      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_4863,c_2099]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_7333,plain,
% 3.61/0.92      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
% 3.61/0.92      | r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_2104,c_5530]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_7484,plain,
% 3.61/0.92      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.61/0.92      inference(forward_subsumption_resolution,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_7333,c_2105]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_7939,plain,
% 3.61/0.92      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.61/0.92      inference(demodulation,[status(thm)],[c_7576,c_7484]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_4000,plain,
% 3.61/0.92      ( k7_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),X3),X0) = k2_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),X3))
% 3.61/0.92      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X0,X1)))) != iProver_top ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_2099,c_2094]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_11151,plain,
% 3.61/0.92      ( k7_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),k1_xboole_0),X0) = k2_relset_1(X0,X1,k2_relset_1(X2,k2_zfmisc_1(X0,X1),k1_xboole_0)) ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_7939,c_4000]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_7940,plain,
% 3.61/0.92      ( k2_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 3.61/0.92      inference(demodulation,[status(thm)],[c_7576,c_4863]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_7491,plain,
% 3.61/0.92      ( k7_relset_1(X0,X1,k2_relat_1(k1_xboole_0),X2) = k9_relat_1(k2_relat_1(k1_xboole_0),X2) ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_7484,c_2096]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_8628,plain,
% 3.61/0.92      ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_7491,c_7576]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_11153,plain,
% 3.61/0.92      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.61/0.92      inference(demodulation,[status(thm)],[c_11151,c_7940,c_8628]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2671,plain,
% 3.61/0.92      ( k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 3.61/0.92      inference(superposition,[status(thm)],[c_2105,c_2664]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_7581,plain,
% 3.61/0.92      ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 3.61/0.92      inference(demodulation,[status(thm)],[c_7560,c_2671]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_13536,plain,
% 3.61/0.92      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.61/0.92      inference(demodulation,[status(thm)],[c_11153,c_7581]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_13644,plain,
% 3.61/0.92      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.61/0.92      inference(light_normalisation,[status(thm)],[c_9410,c_13536]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_1306,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_3318,plain,
% 3.61/0.92      ( k1_relat_1(X0) != X1
% 3.61/0.92      | k1_xboole_0 != X1
% 3.61/0.92      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_1306]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_3319,plain,
% 3.61/0.92      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 3.61/0.92      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 3.61/0.92      | k1_xboole_0 != k1_xboole_0 ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_3318]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_1315,plain,
% 3.61/0.92      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 3.61/0.92      theory(equality) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2717,plain,
% 3.61/0.92      ( k1_relat_1(sK2) = k1_relat_1(X0) | sK2 != X0 ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_1315]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2719,plain,
% 3.61/0.92      ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_2717]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2527,plain,
% 3.61/0.92      ( k1_relat_1(sK2) != X0
% 3.61/0.92      | k1_relat_1(sK2) = k1_xboole_0
% 3.61/0.92      | k1_xboole_0 != X0 ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_1306]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2716,plain,
% 3.61/0.92      ( k1_relat_1(sK2) != k1_relat_1(X0)
% 3.61/0.92      | k1_relat_1(sK2) = k1_xboole_0
% 3.61/0.92      | k1_xboole_0 != k1_relat_1(X0) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_2527]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_2718,plain,
% 3.61/0.92      ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
% 3.61/0.92      | k1_relat_1(sK2) = k1_xboole_0
% 3.61/0.92      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_2716]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(c_1334,plain,
% 3.61/0.92      ( k1_xboole_0 = k1_xboole_0 ),
% 3.61/0.92      inference(instantiation,[status(thm)],[c_1305]) ).
% 3.61/0.92  
% 3.61/0.92  cnf(contradiction,plain,
% 3.61/0.92      ( $false ),
% 3.61/0.92      inference(minisat,
% 3.61/0.92                [status(thm)],
% 3.61/0.92                [c_13644,c_6451,c_6302,c_5960,c_5336,c_4375,c_4333,
% 3.61/0.92                 c_3806,c_3319,c_2719,c_2718,c_2547,c_2404,c_1334,c_117,
% 3.61/0.92                 c_31,c_33]) ).
% 3.61/0.92  
% 3.61/0.92  
% 3.61/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.92  
% 3.61/0.92  ------                               Statistics
% 3.61/0.92  
% 3.61/0.92  ------ General
% 3.61/0.92  
% 3.61/0.92  abstr_ref_over_cycles:                  0
% 3.61/0.92  abstr_ref_under_cycles:                 0
% 3.61/0.92  gc_basic_clause_elim:                   0
% 3.61/0.92  forced_gc_time:                         0
% 3.61/0.92  parsing_time:                           0.012
% 3.61/0.92  unif_index_cands_time:                  0.
% 3.61/0.92  unif_index_add_time:                    0.
% 3.61/0.92  orderings_time:                         0.
% 3.61/0.92  out_proof_time:                         0.015
% 3.61/0.92  total_time:                             0.374
% 3.61/0.92  num_of_symbols:                         52
% 3.61/0.92  num_of_terms:                           9039
% 3.61/0.92  
% 3.61/0.92  ------ Preprocessing
% 3.61/0.92  
% 3.61/0.92  num_of_splits:                          0
% 3.61/0.92  num_of_split_atoms:                     0
% 3.61/0.92  num_of_reused_defs:                     0
% 3.61/0.92  num_eq_ax_congr_red:                    21
% 3.61/0.92  num_of_sem_filtered_clauses:            1
% 3.61/0.92  num_of_subtypes:                        0
% 3.61/0.92  monotx_restored_types:                  0
% 3.61/0.92  sat_num_of_epr_types:                   0
% 3.61/0.92  sat_num_of_non_cyclic_types:            0
% 3.61/0.92  sat_guarded_non_collapsed_types:        0
% 3.61/0.92  num_pure_diseq_elim:                    0
% 3.61/0.92  simp_replaced_by:                       0
% 3.61/0.92  res_preprocessed:                       135
% 3.61/0.92  prep_upred:                             0
% 3.61/0.92  prep_unflattend:                        88
% 3.61/0.92  smt_new_axioms:                         0
% 3.61/0.92  pred_elim_cands:                        6
% 3.61/0.92  pred_elim:                              2
% 3.61/0.92  pred_elim_cl:                           -4
% 3.61/0.92  pred_elim_cycles:                       4
% 3.61/0.92  merged_defs:                            6
% 3.61/0.92  merged_defs_ncl:                        0
% 3.61/0.92  bin_hyper_res:                          6
% 3.61/0.92  prep_cycles:                            3
% 3.61/0.92  pred_elim_time:                         0.019
% 3.61/0.92  splitting_time:                         0.
% 3.61/0.92  sem_filter_time:                        0.
% 3.61/0.92  monotx_time:                            0.
% 3.61/0.92  subtype_inf_time:                       0.
% 3.61/0.92  
% 3.61/0.92  ------ Problem properties
% 3.61/0.92  
% 3.61/0.92  clauses:                                36
% 3.61/0.92  conjectures:                            3
% 3.61/0.92  epr:                                    2
% 3.61/0.92  horn:                                   30
% 3.61/0.92  ground:                                 14
% 3.61/0.92  unary:                                  4
% 3.61/0.92  binary:                                 13
% 3.61/0.92  lits:                                   107
% 3.61/0.92  lits_eq:                                42
% 3.61/0.92  fd_pure:                                0
% 3.61/0.92  fd_pseudo:                              0
% 3.61/0.92  fd_cond:                                3
% 3.61/0.92  fd_pseudo_cond:                         0
% 3.61/0.92  ac_symbols:                             0
% 3.61/0.92  
% 3.61/0.92  ------ Propositional Solver
% 3.61/0.92  
% 3.61/0.92  prop_solver_calls:                      26
% 3.61/0.92  prop_fast_solver_calls:                 1509
% 3.61/0.92  smt_solver_calls:                       0
% 3.61/0.92  smt_fast_solver_calls:                  0
% 3.61/0.92  prop_num_of_clauses:                    5096
% 3.61/0.92  prop_preprocess_simplified:             9761
% 3.61/0.92  prop_fo_subsumed:                       75
% 3.61/0.92  prop_solver_time:                       0.
% 3.61/0.92  smt_solver_time:                        0.
% 3.61/0.92  smt_fast_solver_time:                   0.
% 3.61/0.92  prop_fast_solver_time:                  0.
% 3.61/0.92  prop_unsat_core_time:                   0.
% 3.61/0.92  
% 3.61/0.92  ------ QBF
% 3.61/0.92  
% 3.61/0.92  qbf_q_res:                              0
% 3.61/0.92  qbf_num_tautologies:                    0
% 3.61/0.92  qbf_prep_cycles:                        0
% 3.61/0.92  
% 3.61/0.92  ------ BMC1
% 3.61/0.92  
% 3.61/0.92  bmc1_current_bound:                     -1
% 3.61/0.92  bmc1_last_solved_bound:                 -1
% 3.61/0.92  bmc1_unsat_core_size:                   -1
% 3.61/0.92  bmc1_unsat_core_parents_size:           -1
% 3.61/0.92  bmc1_merge_next_fun:                    0
% 3.61/0.92  bmc1_unsat_core_clauses_time:           0.
% 3.61/0.92  
% 3.61/0.92  ------ Instantiation
% 3.61/0.92  
% 3.61/0.92  inst_num_of_clauses:                    1578
% 3.61/0.92  inst_num_in_passive:                    131
% 3.61/0.92  inst_num_in_active:                     736
% 3.61/0.92  inst_num_in_unprocessed:                711
% 3.61/0.92  inst_num_of_loops:                      900
% 3.61/0.92  inst_num_of_learning_restarts:          0
% 3.61/0.92  inst_num_moves_active_passive:          159
% 3.61/0.92  inst_lit_activity:                      0
% 3.61/0.92  inst_lit_activity_moves:                0
% 3.61/0.92  inst_num_tautologies:                   0
% 3.61/0.92  inst_num_prop_implied:                  0
% 3.61/0.92  inst_num_existing_simplified:           0
% 3.61/0.92  inst_num_eq_res_simplified:             0
% 3.61/0.92  inst_num_child_elim:                    0
% 3.61/0.92  inst_num_of_dismatching_blockings:      591
% 3.61/0.92  inst_num_of_non_proper_insts:           1847
% 3.61/0.92  inst_num_of_duplicates:                 0
% 3.61/0.92  inst_inst_num_from_inst_to_res:         0
% 3.61/0.92  inst_dismatching_checking_time:         0.
% 3.61/0.92  
% 3.61/0.92  ------ Resolution
% 3.61/0.92  
% 3.61/0.92  res_num_of_clauses:                     0
% 3.61/0.92  res_num_in_passive:                     0
% 3.61/0.92  res_num_in_active:                      0
% 3.61/0.92  res_num_of_loops:                       138
% 3.61/0.92  res_forward_subset_subsumed:            61
% 3.61/0.92  res_backward_subset_subsumed:           4
% 3.61/0.92  res_forward_subsumed:                   0
% 3.61/0.92  res_backward_subsumed:                  0
% 3.61/0.92  res_forward_subsumption_resolution:     6
% 3.61/0.92  res_backward_subsumption_resolution:    1
% 3.61/0.92  res_clause_to_clause_subsumption:       682
% 3.61/0.92  res_orphan_elimination:                 0
% 3.61/0.92  res_tautology_del:                      214
% 3.61/0.92  res_num_eq_res_simplified:              0
% 3.61/0.92  res_num_sel_changes:                    0
% 3.61/0.92  res_moves_from_active_to_pass:          0
% 3.61/0.92  
% 3.61/0.92  ------ Superposition
% 3.61/0.92  
% 3.61/0.92  sup_time_total:                         0.
% 3.61/0.92  sup_time_generating:                    0.
% 3.61/0.92  sup_time_sim_full:                      0.
% 3.61/0.92  sup_time_sim_immed:                     0.
% 3.61/0.92  
% 3.61/0.92  sup_num_of_clauses:                     201
% 3.61/0.92  sup_num_in_active:                      94
% 3.61/0.92  sup_num_in_passive:                     107
% 3.61/0.92  sup_num_of_loops:                       178
% 3.61/0.92  sup_fw_superposition:                   204
% 3.61/0.92  sup_bw_superposition:                   226
% 3.61/0.92  sup_immediate_simplified:               158
% 3.61/0.92  sup_given_eliminated:                   0
% 3.61/0.92  comparisons_done:                       0
% 3.61/0.92  comparisons_avoided:                    15
% 3.61/0.92  
% 3.61/0.92  ------ Simplifications
% 3.61/0.92  
% 3.61/0.92  
% 3.61/0.92  sim_fw_subset_subsumed:                 41
% 3.61/0.92  sim_bw_subset_subsumed:                 21
% 3.61/0.92  sim_fw_subsumed:                        28
% 3.61/0.92  sim_bw_subsumed:                        4
% 3.61/0.92  sim_fw_subsumption_res:                 2
% 3.61/0.92  sim_bw_subsumption_res:                 0
% 3.61/0.92  sim_tautology_del:                      6
% 3.61/0.92  sim_eq_tautology_del:                   34
% 3.61/0.92  sim_eq_res_simp:                        3
% 3.61/0.92  sim_fw_demodulated:                     30
% 3.61/0.92  sim_bw_demodulated:                     81
% 3.61/0.92  sim_light_normalised:                   119
% 3.61/0.92  sim_joinable_taut:                      0
% 3.61/0.92  sim_joinable_simp:                      0
% 3.61/0.92  sim_ac_normalised:                      0
% 3.61/0.92  sim_smt_subsumption:                    0
% 3.61/0.92  
%------------------------------------------------------------------------------

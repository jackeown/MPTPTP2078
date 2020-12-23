%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:27 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  161 (1164 expanded)
%              Number of clauses        :   91 ( 360 expanded)
%              Number of leaves         :   19 ( 230 expanded)
%              Depth                    :   19
%              Number of atoms          :  526 (6258 expanded)
%              Number of equality atoms :  181 (1145 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f15])).

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

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

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
   => ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
        | ~ v1_funct_1(k2_funct_1(sK4)) )
      & k2_relset_1(sK2,sK3,sK4) = sK3
      & v2_funct_1(sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f48])).

fof(f83,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f81,plain,(
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

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2279,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6400,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_funct_1(sK4))
    | k2_funct_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_2279])).

cnf(c_6402,plain,
    ( v1_xboole_0(k2_funct_1(sK4))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_funct_1(sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6400])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_36])).

cnf(c_1525,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_1524])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1527,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1525,c_35])).

cnf(c_3066,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3069,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4840,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3066,c_3069])).

cnf(c_5174,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1527,c_4840])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_498,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_499,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_501,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_37])).

cnf(c_3063,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3380,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3394,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3063,c_37,c_35,c_499,c_3380])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3067,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5469,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3394,c_3067])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3068,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4378,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3066,c_3068])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4380,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_4378,c_33])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_484,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_34])).

cnf(c_485,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_487,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_37])).

cnf(c_3064,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_3398,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3064,c_37,c_35,c_485,c_3380])).

cnf(c_4488,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_4380,c_3398])).

cnf(c_5496,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5469,c_4488])).

cnf(c_38,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3360,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3361,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3360])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3372,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3373,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3372])).

cnf(c_3381,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3380])).

cnf(c_5846,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5496,c_38,c_40,c_3361,c_3373,c_3381])).

cnf(c_5851,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5174,c_5846])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5405,plain,
    ( ~ r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4))
    | ~ v1_xboole_0(k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1617,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK4) != X0
    | k1_relat_1(X0) != sK3
    | k2_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_1618,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1617])).

cnf(c_1630,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1618,c_17])).

cnf(c_3053,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1630])).

cnf(c_1619,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1618])).

cnf(c_3694,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3053,c_38,c_40,c_1619,c_3361,c_3373,c_3381])).

cnf(c_3695,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3694])).

cnf(c_3698,plain,
    ( k1_relat_1(sK4) != sK2
    | k2_relat_1(sK4) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3695,c_3394,c_3398])).

cnf(c_4487,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4380,c_3698])).

cnf(c_4491,plain,
    ( k1_relat_1(sK4) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4487])).

cnf(c_5180,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5174,c_4491])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_458,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_22,c_20])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_22,c_20])).

cnf(c_463,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_462])).

cnf(c_1495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_xboole_0(X1)
    | k2_funct_1(sK4) != X0
    | sK2 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_463,c_32])).

cnf(c_1496,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1495])).

cnf(c_1789,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_1496])).

cnf(c_1790,plain,
    ( sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1789])).

cnf(c_5276,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5180,c_38,c_40,c_1790,c_3361,c_3381])).

cnf(c_5278,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5276])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3075,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4502,plain,
    ( k2_funct_1(sK4) = k1_xboole_0
    | sK3 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4488,c_3075])).

cnf(c_4503,plain,
    ( ~ v1_relat_1(k2_funct_1(sK4))
    | k2_funct_1(sK4) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4502])).

cnf(c_4719,plain,
    ( sK3 != k1_xboole_0
    | k2_funct_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4502,c_37,c_35,c_3372,c_3380,c_4503])).

cnf(c_4720,plain,
    ( k2_funct_1(sK4) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4719])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3662,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4676,plain,
    ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2))
    | r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_3662])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3375,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4184,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_3375])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6402,c_5851,c_5405,c_5278,c_5276,c_4720,c_4676,c_4184,c_5])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.66/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/0.98  
% 2.66/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.66/0.98  
% 2.66/0.98  ------  iProver source info
% 2.66/0.98  
% 2.66/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.66/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.66/0.98  git: non_committed_changes: false
% 2.66/0.98  git: last_make_outside_of_git: false
% 2.66/0.98  
% 2.66/0.98  ------ 
% 2.66/0.98  
% 2.66/0.98  ------ Input Options
% 2.66/0.98  
% 2.66/0.98  --out_options                           all
% 2.66/0.98  --tptp_safe_out                         true
% 2.66/0.98  --problem_path                          ""
% 2.66/0.98  --include_path                          ""
% 2.66/0.98  --clausifier                            res/vclausify_rel
% 2.66/0.98  --clausifier_options                    --mode clausify
% 2.66/0.98  --stdin                                 false
% 2.66/0.98  --stats_out                             all
% 2.66/0.98  
% 2.66/0.98  ------ General Options
% 2.66/0.98  
% 2.66/0.98  --fof                                   false
% 2.66/0.98  --time_out_real                         305.
% 2.66/0.98  --time_out_virtual                      -1.
% 2.66/0.98  --symbol_type_check                     false
% 2.66/0.98  --clausify_out                          false
% 2.66/0.98  --sig_cnt_out                           false
% 2.66/0.98  --trig_cnt_out                          false
% 2.66/0.98  --trig_cnt_out_tolerance                1.
% 2.66/0.98  --trig_cnt_out_sk_spl                   false
% 2.66/0.98  --abstr_cl_out                          false
% 2.66/0.98  
% 2.66/0.98  ------ Global Options
% 2.66/0.98  
% 2.66/0.98  --schedule                              default
% 2.66/0.98  --add_important_lit                     false
% 2.66/0.98  --prop_solver_per_cl                    1000
% 2.66/0.98  --min_unsat_core                        false
% 2.66/0.98  --soft_assumptions                      false
% 2.66/0.98  --soft_lemma_size                       3
% 2.66/0.98  --prop_impl_unit_size                   0
% 2.66/0.98  --prop_impl_unit                        []
% 2.66/0.98  --share_sel_clauses                     true
% 2.66/0.98  --reset_solvers                         false
% 2.66/0.98  --bc_imp_inh                            [conj_cone]
% 2.66/0.98  --conj_cone_tolerance                   3.
% 2.66/0.98  --extra_neg_conj                        none
% 2.66/0.98  --large_theory_mode                     true
% 2.66/0.98  --prolific_symb_bound                   200
% 2.66/0.98  --lt_threshold                          2000
% 2.66/0.98  --clause_weak_htbl                      true
% 2.66/0.98  --gc_record_bc_elim                     false
% 2.66/0.98  
% 2.66/0.98  ------ Preprocessing Options
% 2.66/0.98  
% 2.66/0.98  --preprocessing_flag                    true
% 2.66/0.98  --time_out_prep_mult                    0.1
% 2.66/0.98  --splitting_mode                        input
% 2.66/0.98  --splitting_grd                         true
% 2.66/0.98  --splitting_cvd                         false
% 2.66/0.98  --splitting_cvd_svl                     false
% 2.66/0.98  --splitting_nvd                         32
% 2.66/0.98  --sub_typing                            true
% 2.66/0.98  --prep_gs_sim                           true
% 2.66/0.98  --prep_unflatten                        true
% 2.66/0.98  --prep_res_sim                          true
% 2.66/0.98  --prep_upred                            true
% 2.66/0.98  --prep_sem_filter                       exhaustive
% 2.66/0.98  --prep_sem_filter_out                   false
% 2.66/0.98  --pred_elim                             true
% 2.66/0.98  --res_sim_input                         true
% 2.66/0.98  --eq_ax_congr_red                       true
% 2.66/0.98  --pure_diseq_elim                       true
% 2.66/0.98  --brand_transform                       false
% 2.66/0.98  --non_eq_to_eq                          false
% 2.66/0.98  --prep_def_merge                        true
% 2.66/0.98  --prep_def_merge_prop_impl              false
% 2.66/0.98  --prep_def_merge_mbd                    true
% 2.66/0.98  --prep_def_merge_tr_red                 false
% 2.66/0.98  --prep_def_merge_tr_cl                  false
% 2.66/0.98  --smt_preprocessing                     true
% 2.66/0.98  --smt_ac_axioms                         fast
% 2.66/0.98  --preprocessed_out                      false
% 2.66/0.98  --preprocessed_stats                    false
% 2.66/0.98  
% 2.66/0.98  ------ Abstraction refinement Options
% 2.66/0.98  
% 2.66/0.98  --abstr_ref                             []
% 2.66/0.98  --abstr_ref_prep                        false
% 2.66/0.98  --abstr_ref_until_sat                   false
% 2.66/0.98  --abstr_ref_sig_restrict                funpre
% 2.66/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/0.98  --abstr_ref_under                       []
% 2.66/0.98  
% 2.66/0.98  ------ SAT Options
% 2.66/0.98  
% 2.66/0.98  --sat_mode                              false
% 2.66/0.98  --sat_fm_restart_options                ""
% 2.66/0.98  --sat_gr_def                            false
% 2.66/0.98  --sat_epr_types                         true
% 2.66/0.98  --sat_non_cyclic_types                  false
% 2.66/0.98  --sat_finite_models                     false
% 2.66/0.98  --sat_fm_lemmas                         false
% 2.66/0.98  --sat_fm_prep                           false
% 2.66/0.98  --sat_fm_uc_incr                        true
% 2.66/0.98  --sat_out_model                         small
% 2.66/0.98  --sat_out_clauses                       false
% 2.66/0.98  
% 2.66/0.98  ------ QBF Options
% 2.66/0.98  
% 2.66/0.98  --qbf_mode                              false
% 2.66/0.98  --qbf_elim_univ                         false
% 2.66/0.98  --qbf_dom_inst                          none
% 2.66/0.98  --qbf_dom_pre_inst                      false
% 2.66/0.98  --qbf_sk_in                             false
% 2.66/0.98  --qbf_pred_elim                         true
% 2.66/0.98  --qbf_split                             512
% 2.66/0.98  
% 2.66/0.98  ------ BMC1 Options
% 2.66/0.98  
% 2.66/0.98  --bmc1_incremental                      false
% 2.66/0.98  --bmc1_axioms                           reachable_all
% 2.66/0.98  --bmc1_min_bound                        0
% 2.66/0.98  --bmc1_max_bound                        -1
% 2.66/0.98  --bmc1_max_bound_default                -1
% 2.66/0.98  --bmc1_symbol_reachability              true
% 2.66/0.98  --bmc1_property_lemmas                  false
% 2.66/0.98  --bmc1_k_induction                      false
% 2.66/0.98  --bmc1_non_equiv_states                 false
% 2.66/0.98  --bmc1_deadlock                         false
% 2.66/0.98  --bmc1_ucm                              false
% 2.66/0.98  --bmc1_add_unsat_core                   none
% 2.66/0.98  --bmc1_unsat_core_children              false
% 2.66/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/0.98  --bmc1_out_stat                         full
% 2.66/0.98  --bmc1_ground_init                      false
% 2.66/0.98  --bmc1_pre_inst_next_state              false
% 2.66/0.98  --bmc1_pre_inst_state                   false
% 2.66/0.98  --bmc1_pre_inst_reach_state             false
% 2.66/0.98  --bmc1_out_unsat_core                   false
% 2.66/0.98  --bmc1_aig_witness_out                  false
% 2.66/0.98  --bmc1_verbose                          false
% 2.66/0.98  --bmc1_dump_clauses_tptp                false
% 2.66/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.66/0.98  --bmc1_dump_file                        -
% 2.66/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.66/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.66/0.98  --bmc1_ucm_extend_mode                  1
% 2.66/0.98  --bmc1_ucm_init_mode                    2
% 2.66/0.98  --bmc1_ucm_cone_mode                    none
% 2.66/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.66/0.98  --bmc1_ucm_relax_model                  4
% 2.66/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.66/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/0.98  --bmc1_ucm_layered_model                none
% 2.66/0.98  --bmc1_ucm_max_lemma_size               10
% 2.66/0.98  
% 2.66/0.98  ------ AIG Options
% 2.66/0.98  
% 2.66/0.98  --aig_mode                              false
% 2.66/0.98  
% 2.66/0.98  ------ Instantiation Options
% 2.66/0.98  
% 2.66/0.98  --instantiation_flag                    true
% 2.66/0.98  --inst_sos_flag                         false
% 2.66/0.98  --inst_sos_phase                        true
% 2.66/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/0.98  --inst_lit_sel_side                     num_symb
% 2.66/0.98  --inst_solver_per_active                1400
% 2.66/0.98  --inst_solver_calls_frac                1.
% 2.66/0.98  --inst_passive_queue_type               priority_queues
% 2.66/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/0.98  --inst_passive_queues_freq              [25;2]
% 2.66/0.98  --inst_dismatching                      true
% 2.66/0.98  --inst_eager_unprocessed_to_passive     true
% 2.66/0.98  --inst_prop_sim_given                   true
% 2.66/0.98  --inst_prop_sim_new                     false
% 2.66/0.98  --inst_subs_new                         false
% 2.66/0.98  --inst_eq_res_simp                      false
% 2.66/0.98  --inst_subs_given                       false
% 2.66/0.98  --inst_orphan_elimination               true
% 2.66/0.98  --inst_learning_loop_flag               true
% 2.66/0.98  --inst_learning_start                   3000
% 2.66/0.98  --inst_learning_factor                  2
% 2.66/0.98  --inst_start_prop_sim_after_learn       3
% 2.66/0.98  --inst_sel_renew                        solver
% 2.66/0.98  --inst_lit_activity_flag                true
% 2.66/0.98  --inst_restr_to_given                   false
% 2.66/0.98  --inst_activity_threshold               500
% 2.66/0.98  --inst_out_proof                        true
% 2.66/0.98  
% 2.66/0.98  ------ Resolution Options
% 2.66/0.98  
% 2.66/0.98  --resolution_flag                       true
% 2.66/0.98  --res_lit_sel                           adaptive
% 2.66/0.98  --res_lit_sel_side                      none
% 2.66/0.98  --res_ordering                          kbo
% 2.66/0.98  --res_to_prop_solver                    active
% 2.66/0.98  --res_prop_simpl_new                    false
% 2.66/0.98  --res_prop_simpl_given                  true
% 2.66/0.98  --res_passive_queue_type                priority_queues
% 2.66/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/0.98  --res_passive_queues_freq               [15;5]
% 2.66/0.98  --res_forward_subs                      full
% 2.66/0.98  --res_backward_subs                     full
% 2.66/0.98  --res_forward_subs_resolution           true
% 2.66/0.98  --res_backward_subs_resolution          true
% 2.66/0.98  --res_orphan_elimination                true
% 2.66/0.98  --res_time_limit                        2.
% 2.66/0.98  --res_out_proof                         true
% 2.66/0.98  
% 2.66/0.98  ------ Superposition Options
% 2.66/0.98  
% 2.66/0.98  --superposition_flag                    true
% 2.66/0.98  --sup_passive_queue_type                priority_queues
% 2.66/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.66/0.98  --demod_completeness_check              fast
% 2.66/0.98  --demod_use_ground                      true
% 2.66/0.98  --sup_to_prop_solver                    passive
% 2.66/0.98  --sup_prop_simpl_new                    true
% 2.66/0.98  --sup_prop_simpl_given                  true
% 2.66/0.98  --sup_fun_splitting                     false
% 2.66/0.98  --sup_smt_interval                      50000
% 2.66/0.98  
% 2.66/0.98  ------ Superposition Simplification Setup
% 2.66/0.98  
% 2.66/0.98  --sup_indices_passive                   []
% 2.66/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.98  --sup_full_bw                           [BwDemod]
% 2.66/0.98  --sup_immed_triv                        [TrivRules]
% 2.66/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.98  --sup_immed_bw_main                     []
% 2.66/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.98  
% 2.66/0.98  ------ Combination Options
% 2.66/0.98  
% 2.66/0.98  --comb_res_mult                         3
% 2.66/0.98  --comb_sup_mult                         2
% 2.66/0.98  --comb_inst_mult                        10
% 2.66/0.98  
% 2.66/0.98  ------ Debug Options
% 2.66/0.98  
% 2.66/0.98  --dbg_backtrace                         false
% 2.66/0.98  --dbg_dump_prop_clauses                 false
% 2.66/0.98  --dbg_dump_prop_clauses_file            -
% 2.66/0.98  --dbg_out_stat                          false
% 2.66/0.98  ------ Parsing...
% 2.66/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.66/0.98  
% 2.66/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.66/0.98  
% 2.66/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.66/0.98  
% 2.66/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.66/0.98  ------ Proving...
% 2.66/0.98  ------ Problem Properties 
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  clauses                                 37
% 2.66/0.98  conjectures                             3
% 2.66/0.98  EPR                                     4
% 2.66/0.98  Horn                                    30
% 2.66/0.98  unary                                   7
% 2.66/0.98  binary                                  12
% 2.66/0.98  lits                                    97
% 2.66/0.98  lits eq                                 34
% 2.66/0.98  fd_pure                                 0
% 2.66/0.98  fd_pseudo                               0
% 2.66/0.98  fd_cond                                 3
% 2.66/0.98  fd_pseudo_cond                          0
% 2.66/0.98  AC symbols                              0
% 2.66/0.98  
% 2.66/0.98  ------ Schedule dynamic 5 is on 
% 2.66/0.98  
% 2.66/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  ------ 
% 2.66/0.98  Current options:
% 2.66/0.98  ------ 
% 2.66/0.98  
% 2.66/0.98  ------ Input Options
% 2.66/0.98  
% 2.66/0.98  --out_options                           all
% 2.66/0.98  --tptp_safe_out                         true
% 2.66/0.98  --problem_path                          ""
% 2.66/0.98  --include_path                          ""
% 2.66/0.98  --clausifier                            res/vclausify_rel
% 2.66/0.98  --clausifier_options                    --mode clausify
% 2.66/0.98  --stdin                                 false
% 2.66/0.98  --stats_out                             all
% 2.66/0.98  
% 2.66/0.98  ------ General Options
% 2.66/0.98  
% 2.66/0.98  --fof                                   false
% 2.66/0.98  --time_out_real                         305.
% 2.66/0.98  --time_out_virtual                      -1.
% 2.66/0.98  --symbol_type_check                     false
% 2.66/0.98  --clausify_out                          false
% 2.66/0.98  --sig_cnt_out                           false
% 2.66/0.98  --trig_cnt_out                          false
% 2.66/0.98  --trig_cnt_out_tolerance                1.
% 2.66/0.98  --trig_cnt_out_sk_spl                   false
% 2.66/0.98  --abstr_cl_out                          false
% 2.66/0.98  
% 2.66/0.98  ------ Global Options
% 2.66/0.98  
% 2.66/0.98  --schedule                              default
% 2.66/0.98  --add_important_lit                     false
% 2.66/0.98  --prop_solver_per_cl                    1000
% 2.66/0.98  --min_unsat_core                        false
% 2.66/0.98  --soft_assumptions                      false
% 2.66/0.98  --soft_lemma_size                       3
% 2.66/0.98  --prop_impl_unit_size                   0
% 2.66/0.98  --prop_impl_unit                        []
% 2.66/0.98  --share_sel_clauses                     true
% 2.66/0.98  --reset_solvers                         false
% 2.66/0.98  --bc_imp_inh                            [conj_cone]
% 2.66/0.98  --conj_cone_tolerance                   3.
% 2.66/0.98  --extra_neg_conj                        none
% 2.66/0.98  --large_theory_mode                     true
% 2.66/0.98  --prolific_symb_bound                   200
% 2.66/0.98  --lt_threshold                          2000
% 2.66/0.98  --clause_weak_htbl                      true
% 2.66/0.98  --gc_record_bc_elim                     false
% 2.66/0.98  
% 2.66/0.98  ------ Preprocessing Options
% 2.66/0.98  
% 2.66/0.98  --preprocessing_flag                    true
% 2.66/0.98  --time_out_prep_mult                    0.1
% 2.66/0.98  --splitting_mode                        input
% 2.66/0.98  --splitting_grd                         true
% 2.66/0.98  --splitting_cvd                         false
% 2.66/0.98  --splitting_cvd_svl                     false
% 2.66/0.98  --splitting_nvd                         32
% 2.66/0.98  --sub_typing                            true
% 2.66/0.98  --prep_gs_sim                           true
% 2.66/0.98  --prep_unflatten                        true
% 2.66/0.98  --prep_res_sim                          true
% 2.66/0.98  --prep_upred                            true
% 2.66/0.98  --prep_sem_filter                       exhaustive
% 2.66/0.98  --prep_sem_filter_out                   false
% 2.66/0.98  --pred_elim                             true
% 2.66/0.98  --res_sim_input                         true
% 2.66/0.98  --eq_ax_congr_red                       true
% 2.66/0.98  --pure_diseq_elim                       true
% 2.66/0.98  --brand_transform                       false
% 2.66/0.98  --non_eq_to_eq                          false
% 2.66/0.98  --prep_def_merge                        true
% 2.66/0.98  --prep_def_merge_prop_impl              false
% 2.66/0.98  --prep_def_merge_mbd                    true
% 2.66/0.98  --prep_def_merge_tr_red                 false
% 2.66/0.98  --prep_def_merge_tr_cl                  false
% 2.66/0.98  --smt_preprocessing                     true
% 2.66/0.98  --smt_ac_axioms                         fast
% 2.66/0.98  --preprocessed_out                      false
% 2.66/0.98  --preprocessed_stats                    false
% 2.66/0.98  
% 2.66/0.98  ------ Abstraction refinement Options
% 2.66/0.98  
% 2.66/0.98  --abstr_ref                             []
% 2.66/0.98  --abstr_ref_prep                        false
% 2.66/0.98  --abstr_ref_until_sat                   false
% 2.66/0.98  --abstr_ref_sig_restrict                funpre
% 2.66/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/0.98  --abstr_ref_under                       []
% 2.66/0.98  
% 2.66/0.98  ------ SAT Options
% 2.66/0.98  
% 2.66/0.98  --sat_mode                              false
% 2.66/0.98  --sat_fm_restart_options                ""
% 2.66/0.98  --sat_gr_def                            false
% 2.66/0.98  --sat_epr_types                         true
% 2.66/0.98  --sat_non_cyclic_types                  false
% 2.66/0.98  --sat_finite_models                     false
% 2.66/0.98  --sat_fm_lemmas                         false
% 2.66/0.98  --sat_fm_prep                           false
% 2.66/0.98  --sat_fm_uc_incr                        true
% 2.66/0.98  --sat_out_model                         small
% 2.66/0.98  --sat_out_clauses                       false
% 2.66/0.98  
% 2.66/0.98  ------ QBF Options
% 2.66/0.98  
% 2.66/0.98  --qbf_mode                              false
% 2.66/0.98  --qbf_elim_univ                         false
% 2.66/0.98  --qbf_dom_inst                          none
% 2.66/0.98  --qbf_dom_pre_inst                      false
% 2.66/0.98  --qbf_sk_in                             false
% 2.66/0.98  --qbf_pred_elim                         true
% 2.66/0.98  --qbf_split                             512
% 2.66/0.98  
% 2.66/0.98  ------ BMC1 Options
% 2.66/0.98  
% 2.66/0.98  --bmc1_incremental                      false
% 2.66/0.98  --bmc1_axioms                           reachable_all
% 2.66/0.98  --bmc1_min_bound                        0
% 2.66/0.98  --bmc1_max_bound                        -1
% 2.66/0.98  --bmc1_max_bound_default                -1
% 2.66/0.98  --bmc1_symbol_reachability              true
% 2.66/0.98  --bmc1_property_lemmas                  false
% 2.66/0.98  --bmc1_k_induction                      false
% 2.66/0.98  --bmc1_non_equiv_states                 false
% 2.66/0.98  --bmc1_deadlock                         false
% 2.66/0.98  --bmc1_ucm                              false
% 2.66/0.98  --bmc1_add_unsat_core                   none
% 2.66/0.98  --bmc1_unsat_core_children              false
% 2.66/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/0.98  --bmc1_out_stat                         full
% 2.66/0.98  --bmc1_ground_init                      false
% 2.66/0.98  --bmc1_pre_inst_next_state              false
% 2.66/0.98  --bmc1_pre_inst_state                   false
% 2.66/0.98  --bmc1_pre_inst_reach_state             false
% 2.66/0.98  --bmc1_out_unsat_core                   false
% 2.66/0.98  --bmc1_aig_witness_out                  false
% 2.66/0.98  --bmc1_verbose                          false
% 2.66/0.98  --bmc1_dump_clauses_tptp                false
% 2.66/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.66/0.98  --bmc1_dump_file                        -
% 2.66/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.66/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.66/0.98  --bmc1_ucm_extend_mode                  1
% 2.66/0.98  --bmc1_ucm_init_mode                    2
% 2.66/0.98  --bmc1_ucm_cone_mode                    none
% 2.66/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.66/0.98  --bmc1_ucm_relax_model                  4
% 2.66/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.66/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/0.98  --bmc1_ucm_layered_model                none
% 2.66/0.98  --bmc1_ucm_max_lemma_size               10
% 2.66/0.98  
% 2.66/0.98  ------ AIG Options
% 2.66/0.98  
% 2.66/0.98  --aig_mode                              false
% 2.66/0.98  
% 2.66/0.98  ------ Instantiation Options
% 2.66/0.98  
% 2.66/0.98  --instantiation_flag                    true
% 2.66/0.98  --inst_sos_flag                         false
% 2.66/0.98  --inst_sos_phase                        true
% 2.66/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/0.98  --inst_lit_sel_side                     none
% 2.66/0.98  --inst_solver_per_active                1400
% 2.66/0.98  --inst_solver_calls_frac                1.
% 2.66/0.98  --inst_passive_queue_type               priority_queues
% 2.66/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/0.98  --inst_passive_queues_freq              [25;2]
% 2.66/0.98  --inst_dismatching                      true
% 2.66/0.98  --inst_eager_unprocessed_to_passive     true
% 2.66/0.98  --inst_prop_sim_given                   true
% 2.66/0.98  --inst_prop_sim_new                     false
% 2.66/0.98  --inst_subs_new                         false
% 2.66/0.98  --inst_eq_res_simp                      false
% 2.66/0.98  --inst_subs_given                       false
% 2.66/0.98  --inst_orphan_elimination               true
% 2.66/0.98  --inst_learning_loop_flag               true
% 2.66/0.98  --inst_learning_start                   3000
% 2.66/0.98  --inst_learning_factor                  2
% 2.66/0.98  --inst_start_prop_sim_after_learn       3
% 2.66/0.98  --inst_sel_renew                        solver
% 2.66/0.98  --inst_lit_activity_flag                true
% 2.66/0.98  --inst_restr_to_given                   false
% 2.66/0.98  --inst_activity_threshold               500
% 2.66/0.98  --inst_out_proof                        true
% 2.66/0.98  
% 2.66/0.98  ------ Resolution Options
% 2.66/0.98  
% 2.66/0.98  --resolution_flag                       false
% 2.66/0.98  --res_lit_sel                           adaptive
% 2.66/0.98  --res_lit_sel_side                      none
% 2.66/0.98  --res_ordering                          kbo
% 2.66/0.98  --res_to_prop_solver                    active
% 2.66/0.98  --res_prop_simpl_new                    false
% 2.66/0.98  --res_prop_simpl_given                  true
% 2.66/0.98  --res_passive_queue_type                priority_queues
% 2.66/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/0.98  --res_passive_queues_freq               [15;5]
% 2.66/0.98  --res_forward_subs                      full
% 2.66/0.98  --res_backward_subs                     full
% 2.66/0.98  --res_forward_subs_resolution           true
% 2.66/0.98  --res_backward_subs_resolution          true
% 2.66/0.98  --res_orphan_elimination                true
% 2.66/0.98  --res_time_limit                        2.
% 2.66/0.98  --res_out_proof                         true
% 2.66/0.98  
% 2.66/0.98  ------ Superposition Options
% 2.66/0.98  
% 2.66/0.98  --superposition_flag                    true
% 2.66/0.98  --sup_passive_queue_type                priority_queues
% 2.66/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.66/0.98  --demod_completeness_check              fast
% 2.66/0.98  --demod_use_ground                      true
% 2.66/0.98  --sup_to_prop_solver                    passive
% 2.66/0.98  --sup_prop_simpl_new                    true
% 2.66/0.98  --sup_prop_simpl_given                  true
% 2.66/0.98  --sup_fun_splitting                     false
% 2.66/0.98  --sup_smt_interval                      50000
% 2.66/0.98  
% 2.66/0.98  ------ Superposition Simplification Setup
% 2.66/0.98  
% 2.66/0.98  --sup_indices_passive                   []
% 2.66/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.98  --sup_full_bw                           [BwDemod]
% 2.66/0.98  --sup_immed_triv                        [TrivRules]
% 2.66/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.98  --sup_immed_bw_main                     []
% 2.66/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/0.98  
% 2.66/0.98  ------ Combination Options
% 2.66/0.98  
% 2.66/0.98  --comb_res_mult                         3
% 2.66/0.98  --comb_sup_mult                         2
% 2.66/0.98  --comb_inst_mult                        10
% 2.66/0.98  
% 2.66/0.98  ------ Debug Options
% 2.66/0.98  
% 2.66/0.98  --dbg_backtrace                         false
% 2.66/0.98  --dbg_dump_prop_clauses                 false
% 2.66/0.98  --dbg_dump_prop_clauses_file            -
% 2.66/0.98  --dbg_out_stat                          false
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  ------ Proving...
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  % SZS status Theorem for theBenchmark.p
% 2.66/0.98  
% 2.66/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.66/0.98  
% 2.66/0.98  fof(f15,axiom,(
% 2.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f32,plain,(
% 2.66/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.98    inference(ennf_transformation,[],[f15])).
% 2.66/0.98  
% 2.66/0.98  fof(f33,plain,(
% 2.66/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.98    inference(flattening,[],[f32])).
% 2.66/0.98  
% 2.66/0.98  fof(f47,plain,(
% 2.66/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.98    inference(nnf_transformation,[],[f33])).
% 2.66/0.98  
% 2.66/0.98  fof(f73,plain,(
% 2.66/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f47])).
% 2.66/0.98  
% 2.66/0.98  fof(f17,conjecture,(
% 2.66/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f18,negated_conjecture,(
% 2.66/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.66/0.98    inference(negated_conjecture,[],[f17])).
% 2.66/0.98  
% 2.66/0.98  fof(f36,plain,(
% 2.66/0.98    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.66/0.98    inference(ennf_transformation,[],[f18])).
% 2.66/0.98  
% 2.66/0.98  fof(f37,plain,(
% 2.66/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.66/0.98    inference(flattening,[],[f36])).
% 2.66/0.98  
% 2.66/0.98  fof(f48,plain,(
% 2.66/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.66/0.98    introduced(choice_axiom,[])).
% 2.66/0.98  
% 2.66/0.98  fof(f49,plain,(
% 2.66/0.98    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.66/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f48])).
% 2.66/0.98  
% 2.66/0.98  fof(f83,plain,(
% 2.66/0.98    v1_funct_2(sK4,sK2,sK3)),
% 2.66/0.98    inference(cnf_transformation,[],[f49])).
% 2.66/0.98  
% 2.66/0.98  fof(f84,plain,(
% 2.66/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.66/0.98    inference(cnf_transformation,[],[f49])).
% 2.66/0.98  
% 2.66/0.98  fof(f11,axiom,(
% 2.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f27,plain,(
% 2.66/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.98    inference(ennf_transformation,[],[f11])).
% 2.66/0.98  
% 2.66/0.98  fof(f68,plain,(
% 2.66/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f27])).
% 2.66/0.98  
% 2.66/0.98  fof(f9,axiom,(
% 2.66/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f24,plain,(
% 2.66/0.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.66/0.98    inference(ennf_transformation,[],[f9])).
% 2.66/0.98  
% 2.66/0.98  fof(f25,plain,(
% 2.66/0.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/0.98    inference(flattening,[],[f24])).
% 2.66/0.98  
% 2.66/0.98  fof(f66,plain,(
% 2.66/0.98    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f25])).
% 2.66/0.98  
% 2.66/0.98  fof(f85,plain,(
% 2.66/0.98    v2_funct_1(sK4)),
% 2.66/0.98    inference(cnf_transformation,[],[f49])).
% 2.66/0.98  
% 2.66/0.98  fof(f82,plain,(
% 2.66/0.98    v1_funct_1(sK4)),
% 2.66/0.98    inference(cnf_transformation,[],[f49])).
% 2.66/0.98  
% 2.66/0.98  fof(f10,axiom,(
% 2.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f26,plain,(
% 2.66/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.98    inference(ennf_transformation,[],[f10])).
% 2.66/0.98  
% 2.66/0.98  fof(f67,plain,(
% 2.66/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f26])).
% 2.66/0.98  
% 2.66/0.98  fof(f16,axiom,(
% 2.66/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f34,plain,(
% 2.66/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.66/0.98    inference(ennf_transformation,[],[f16])).
% 2.66/0.98  
% 2.66/0.98  fof(f35,plain,(
% 2.66/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/0.98    inference(flattening,[],[f34])).
% 2.66/0.98  
% 2.66/0.98  fof(f81,plain,(
% 2.66/0.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f35])).
% 2.66/0.98  
% 2.66/0.98  fof(f12,axiom,(
% 2.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f28,plain,(
% 2.66/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.98    inference(ennf_transformation,[],[f12])).
% 2.66/0.98  
% 2.66/0.98  fof(f69,plain,(
% 2.66/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f28])).
% 2.66/0.98  
% 2.66/0.98  fof(f86,plain,(
% 2.66/0.98    k2_relset_1(sK2,sK3,sK4) = sK3),
% 2.66/0.98    inference(cnf_transformation,[],[f49])).
% 2.66/0.98  
% 2.66/0.98  fof(f65,plain,(
% 2.66/0.98    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f25])).
% 2.66/0.98  
% 2.66/0.98  fof(f7,axiom,(
% 2.66/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f22,plain,(
% 2.66/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.66/0.98    inference(ennf_transformation,[],[f7])).
% 2.66/0.98  
% 2.66/0.98  fof(f23,plain,(
% 2.66/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/0.98    inference(flattening,[],[f22])).
% 2.66/0.98  
% 2.66/0.98  fof(f62,plain,(
% 2.66/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f23])).
% 2.66/0.98  
% 2.66/0.98  fof(f61,plain,(
% 2.66/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f23])).
% 2.66/0.98  
% 2.66/0.98  fof(f1,axiom,(
% 2.66/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f38,plain,(
% 2.66/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.66/0.98    inference(nnf_transformation,[],[f1])).
% 2.66/0.98  
% 2.66/0.98  fof(f39,plain,(
% 2.66/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.66/0.98    inference(rectify,[],[f38])).
% 2.66/0.98  
% 2.66/0.98  fof(f40,plain,(
% 2.66/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.66/0.98    introduced(choice_axiom,[])).
% 2.66/0.98  
% 2.66/0.98  fof(f41,plain,(
% 2.66/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.66/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 2.66/0.98  
% 2.66/0.98  fof(f50,plain,(
% 2.66/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f41])).
% 2.66/0.98  
% 2.66/0.98  fof(f80,plain,(
% 2.66/0.98    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f35])).
% 2.66/0.98  
% 2.66/0.98  fof(f87,plain,(
% 2.66/0.98    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 2.66/0.98    inference(cnf_transformation,[],[f49])).
% 2.66/0.98  
% 2.66/0.98  fof(f3,axiom,(
% 2.66/0.98    v1_xboole_0(k1_xboole_0)),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f55,plain,(
% 2.66/0.98    v1_xboole_0(k1_xboole_0)),
% 2.66/0.98    inference(cnf_transformation,[],[f3])).
% 2.66/0.98  
% 2.66/0.98  fof(f14,axiom,(
% 2.66/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f31,plain,(
% 2.66/0.98    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.66/0.98    inference(ennf_transformation,[],[f14])).
% 2.66/0.98  
% 2.66/0.98  fof(f72,plain,(
% 2.66/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f31])).
% 2.66/0.98  
% 2.66/0.98  fof(f13,axiom,(
% 2.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f29,plain,(
% 2.66/0.98    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.98    inference(ennf_transformation,[],[f13])).
% 2.66/0.98  
% 2.66/0.98  fof(f30,plain,(
% 2.66/0.98    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.66/0.98    inference(flattening,[],[f29])).
% 2.66/0.98  
% 2.66/0.98  fof(f71,plain,(
% 2.66/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.66/0.98    inference(cnf_transformation,[],[f30])).
% 2.66/0.98  
% 2.66/0.98  fof(f5,axiom,(
% 2.66/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f20,plain,(
% 2.66/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.66/0.98    inference(ennf_transformation,[],[f5])).
% 2.66/0.98  
% 2.66/0.98  fof(f21,plain,(
% 2.66/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.66/0.98    inference(flattening,[],[f20])).
% 2.66/0.98  
% 2.66/0.98  fof(f58,plain,(
% 2.66/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f21])).
% 2.66/0.98  
% 2.66/0.98  fof(f2,axiom,(
% 2.66/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f19,plain,(
% 2.66/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.66/0.98    inference(ennf_transformation,[],[f2])).
% 2.66/0.98  
% 2.66/0.98  fof(f42,plain,(
% 2.66/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.66/0.98    inference(nnf_transformation,[],[f19])).
% 2.66/0.98  
% 2.66/0.98  fof(f43,plain,(
% 2.66/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.66/0.98    inference(rectify,[],[f42])).
% 2.66/0.98  
% 2.66/0.98  fof(f44,plain,(
% 2.66/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.66/0.98    introduced(choice_axiom,[])).
% 2.66/0.98  
% 2.66/0.98  fof(f45,plain,(
% 2.66/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.66/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 2.66/0.98  
% 2.66/0.98  fof(f53,plain,(
% 2.66/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f45])).
% 2.66/0.98  
% 2.66/0.98  fof(f4,axiom,(
% 2.66/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/0.98  
% 2.66/0.98  fof(f46,plain,(
% 2.66/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.66/0.98    inference(nnf_transformation,[],[f4])).
% 2.66/0.98  
% 2.66/0.98  fof(f57,plain,(
% 2.66/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.66/0.98    inference(cnf_transformation,[],[f46])).
% 2.66/0.98  
% 2.66/0.98  cnf(c_2279,plain,
% 2.66/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.66/0.98      theory(equality) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_6400,plain,
% 2.66/0.98      ( ~ v1_xboole_0(X0)
% 2.66/0.98      | v1_xboole_0(k2_funct_1(sK4))
% 2.66/0.98      | k2_funct_1(sK4) != X0 ),
% 2.66/0.98      inference(instantiation,[status(thm)],[c_2279]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_6402,plain,
% 2.66/0.98      ( v1_xboole_0(k2_funct_1(sK4))
% 2.66/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 2.66/0.98      | k2_funct_1(sK4) != k1_xboole_0 ),
% 2.66/0.98      inference(instantiation,[status(thm)],[c_6400]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_28,plain,
% 2.66/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.66/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.66/0.98      | k1_xboole_0 = X2 ),
% 2.66/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_36,negated_conjecture,
% 2.66/0.98      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.66/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1524,plain,
% 2.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.66/0.98      | sK2 != X1
% 2.66/0.98      | sK3 != X2
% 2.66/0.98      | sK4 != X0
% 2.66/0.98      | k1_xboole_0 = X2 ),
% 2.66/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_36]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1525,plain,
% 2.66/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.66/0.98      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.66/0.98      | k1_xboole_0 = sK3 ),
% 2.66/0.98      inference(unflattening,[status(thm)],[c_1524]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_35,negated_conjecture,
% 2.66/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.66/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1527,plain,
% 2.66/0.98      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.66/0.98      inference(global_propositional_subsumption,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_1525,c_35]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3066,plain,
% 2.66/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_18,plain,
% 2.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3069,plain,
% 2.66/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.66/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4840,plain,
% 2.66/0.98      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_3066,c_3069]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_5174,plain,
% 2.66/0.98      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_1527,c_4840]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_15,plain,
% 2.66/0.98      ( ~ v2_funct_1(X0)
% 2.66/0.98      | ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_relat_1(X0)
% 2.66/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_34,negated_conjecture,
% 2.66/0.98      ( v2_funct_1(sK4) ),
% 2.66/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_498,plain,
% 2.66/0.98      ( ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_relat_1(X0)
% 2.66/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.66/0.98      | sK4 != X0 ),
% 2.66/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_34]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_499,plain,
% 2.66/0.98      ( ~ v1_funct_1(sK4)
% 2.66/0.98      | ~ v1_relat_1(sK4)
% 2.66/0.98      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 2.66/0.98      inference(unflattening,[status(thm)],[c_498]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_37,negated_conjecture,
% 2.66/0.98      ( v1_funct_1(sK4) ),
% 2.66/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_501,plain,
% 2.66/0.98      ( ~ v1_relat_1(sK4)
% 2.66/0.98      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 2.66/0.98      inference(global_propositional_subsumption,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_499,c_37]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3063,plain,
% 2.66/0.98      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 2.66/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_17,plain,
% 2.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | v1_relat_1(X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3380,plain,
% 2.66/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.66/0.98      | v1_relat_1(sK4) ),
% 2.66/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3394,plain,
% 2.66/0.98      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 2.66/0.98      inference(global_propositional_subsumption,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_3063,c_37,c_35,c_499,c_3380]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_29,plain,
% 2.66/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.66/0.98      | ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_relat_1(X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3067,plain,
% 2.66/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.66/0.98      | v1_funct_1(X0) != iProver_top
% 2.66/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_5469,plain,
% 2.66/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
% 2.66/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 2.66/0.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_3394,c_3067]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_19,plain,
% 2.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3068,plain,
% 2.66/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.66/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4378,plain,
% 2.66/0.98      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_3066,c_3068]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_33,negated_conjecture,
% 2.66/0.98      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 2.66/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4380,plain,
% 2.66/0.98      ( k2_relat_1(sK4) = sK3 ),
% 2.66/0.98      inference(light_normalisation,[status(thm)],[c_4378,c_33]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_16,plain,
% 2.66/0.98      ( ~ v2_funct_1(X0)
% 2.66/0.98      | ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_relat_1(X0)
% 2.66/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_484,plain,
% 2.66/0.98      ( ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_relat_1(X0)
% 2.66/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.66/0.98      | sK4 != X0 ),
% 2.66/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_34]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_485,plain,
% 2.66/0.98      ( ~ v1_funct_1(sK4)
% 2.66/0.98      | ~ v1_relat_1(sK4)
% 2.66/0.98      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.66/0.98      inference(unflattening,[status(thm)],[c_484]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_487,plain,
% 2.66/0.98      ( ~ v1_relat_1(sK4)
% 2.66/0.98      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.66/0.98      inference(global_propositional_subsumption,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_485,c_37]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3064,plain,
% 2.66/0.98      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 2.66/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3398,plain,
% 2.66/0.98      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.66/0.98      inference(global_propositional_subsumption,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_3064,c_37,c_35,c_485,c_3380]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4488,plain,
% 2.66/0.98      ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
% 2.66/0.98      inference(demodulation,[status(thm)],[c_4380,c_3398]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_5496,plain,
% 2.66/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
% 2.66/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 2.66/0.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 2.66/0.98      inference(light_normalisation,[status(thm)],[c_5469,c_4488]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_38,plain,
% 2.66/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_40,plain,
% 2.66/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_11,plain,
% 2.66/0.98      ( ~ v1_funct_1(X0)
% 2.66/0.98      | v1_funct_1(k2_funct_1(X0))
% 2.66/0.98      | ~ v1_relat_1(X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3360,plain,
% 2.66/0.98      ( v1_funct_1(k2_funct_1(sK4))
% 2.66/0.98      | ~ v1_funct_1(sK4)
% 2.66/0.98      | ~ v1_relat_1(sK4) ),
% 2.66/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3361,plain,
% 2.66/0.98      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 2.66/0.98      | v1_funct_1(sK4) != iProver_top
% 2.66/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_3360]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_12,plain,
% 2.66/0.98      ( ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_relat_1(X0)
% 2.66/0.98      | v1_relat_1(k2_funct_1(X0)) ),
% 2.66/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3372,plain,
% 2.66/0.98      ( ~ v1_funct_1(sK4)
% 2.66/0.98      | v1_relat_1(k2_funct_1(sK4))
% 2.66/0.98      | ~ v1_relat_1(sK4) ),
% 2.66/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3373,plain,
% 2.66/0.98      ( v1_funct_1(sK4) != iProver_top
% 2.66/0.98      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 2.66/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_3372]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3381,plain,
% 2.66/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.66/0.98      | v1_relat_1(sK4) = iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_3380]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_5846,plain,
% 2.66/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 2.66/0.98      inference(global_propositional_subsumption,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_5496,c_38,c_40,c_3361,c_3373,c_3381]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_5851,plain,
% 2.66/0.98      ( sK3 = k1_xboole_0
% 2.66/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_5174,c_5846]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1,plain,
% 2.66/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.66/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_5405,plain,
% 2.66/0.98      ( ~ r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4))
% 2.66/0.98      | ~ v1_xboole_0(k2_funct_1(sK4)) ),
% 2.66/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_30,plain,
% 2.66/0.98      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.66/0.98      | ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_relat_1(X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_32,negated_conjecture,
% 2.66/0.98      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 2.66/0.98      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.66/0.98      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 2.66/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1617,plain,
% 2.66/0.98      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.66/0.98      | ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.66/0.98      | ~ v1_relat_1(X0)
% 2.66/0.98      | k2_funct_1(sK4) != X0
% 2.66/0.98      | k1_relat_1(X0) != sK3
% 2.66/0.98      | k2_relat_1(X0) != sK2 ),
% 2.66/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1618,plain,
% 2.66/0.98      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.66/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.66/0.98      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.66/0.98      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.66/0.98      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 2.66/0.98      inference(unflattening,[status(thm)],[c_1617]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1630,plain,
% 2.66/0.98      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.66/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.66/0.98      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.66/0.98      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 2.66/0.98      inference(forward_subsumption_resolution,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_1618,c_17]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3053,plain,
% 2.66/0.98      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.66/0.98      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.66/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.66/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_1630]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1619,plain,
% 2.66/0.98      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.66/0.98      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.66/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.66/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 2.66/0.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_1618]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3694,plain,
% 2.66/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.66/0.98      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.66/0.98      | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
% 2.66/0.98      inference(global_propositional_subsumption,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_3053,c_38,c_40,c_1619,c_3361,c_3373,c_3381]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3695,plain,
% 2.66/0.98      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.66/0.98      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.66/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.66/0.98      inference(renaming,[status(thm)],[c_3694]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3698,plain,
% 2.66/0.98      ( k1_relat_1(sK4) != sK2
% 2.66/0.98      | k2_relat_1(sK4) != sK3
% 2.66/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.66/0.98      inference(light_normalisation,[status(thm)],[c_3695,c_3394,c_3398]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4487,plain,
% 2.66/0.98      ( k1_relat_1(sK4) != sK2
% 2.66/0.98      | sK3 != sK3
% 2.66/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.66/0.98      inference(demodulation,[status(thm)],[c_4380,c_3698]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4491,plain,
% 2.66/0.98      ( k1_relat_1(sK4) != sK2
% 2.66/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.66/0.98      inference(equality_resolution_simp,[status(thm)],[c_4487]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_5180,plain,
% 2.66/0.98      ( sK3 = k1_xboole_0
% 2.66/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_5174,c_4491]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_5,plain,
% 2.66/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_22,plain,
% 2.66/0.98      ( v1_partfun1(X0,X1)
% 2.66/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | ~ v1_xboole_0(X1) ),
% 2.66/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_20,plain,
% 2.66/0.98      ( v1_funct_2(X0,X1,X2)
% 2.66/0.98      | ~ v1_partfun1(X0,X1)
% 2.66/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | ~ v1_funct_1(X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_458,plain,
% 2.66/0.98      ( v1_funct_2(X0,X1,X2)
% 2.66/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.66/0.98      | ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_xboole_0(X1) ),
% 2.66/0.98      inference(resolution,[status(thm)],[c_22,c_20]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_462,plain,
% 2.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | v1_funct_2(X0,X1,X2)
% 2.66/0.98      | ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_xboole_0(X1) ),
% 2.66/0.98      inference(global_propositional_subsumption,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_458,c_22,c_20]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_463,plain,
% 2.66/0.98      ( v1_funct_2(X0,X1,X2)
% 2.66/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_xboole_0(X1) ),
% 2.66/0.98      inference(renaming,[status(thm)],[c_462]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1495,plain,
% 2.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.66/0.98      | ~ v1_funct_1(X0)
% 2.66/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.66/0.98      | ~ v1_xboole_0(X1)
% 2.66/0.98      | k2_funct_1(sK4) != X0
% 2.66/0.98      | sK2 != X2
% 2.66/0.98      | sK3 != X1 ),
% 2.66/0.98      inference(resolution_lifted,[status(thm)],[c_463,c_32]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1496,plain,
% 2.66/0.98      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.66/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.66/0.98      | ~ v1_xboole_0(sK3) ),
% 2.66/0.98      inference(unflattening,[status(thm)],[c_1495]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1789,plain,
% 2.66/0.98      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.66/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.66/0.98      | sK3 != k1_xboole_0 ),
% 2.66/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_1496]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_1790,plain,
% 2.66/0.98      ( sK3 != k1_xboole_0
% 2.66/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.66/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_1789]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_5276,plain,
% 2.66/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.66/0.98      inference(global_propositional_subsumption,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_5180,c_38,c_40,c_1790,c_3361,c_3381]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_5278,plain,
% 2.66/0.98      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 2.66/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_5276]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_9,plain,
% 2.66/0.98      ( ~ v1_relat_1(X0)
% 2.66/0.98      | k1_relat_1(X0) != k1_xboole_0
% 2.66/0.98      | k1_xboole_0 = X0 ),
% 2.66/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3075,plain,
% 2.66/0.98      ( k1_relat_1(X0) != k1_xboole_0
% 2.66/0.98      | k1_xboole_0 = X0
% 2.66/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.66/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4502,plain,
% 2.66/0.98      ( k2_funct_1(sK4) = k1_xboole_0
% 2.66/0.98      | sK3 != k1_xboole_0
% 2.66/0.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 2.66/0.98      inference(superposition,[status(thm)],[c_4488,c_3075]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4503,plain,
% 2.66/0.98      ( ~ v1_relat_1(k2_funct_1(sK4))
% 2.66/0.98      | k2_funct_1(sK4) = k1_xboole_0
% 2.66/0.98      | sK3 != k1_xboole_0 ),
% 2.66/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4502]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4719,plain,
% 2.66/0.98      ( sK3 != k1_xboole_0 | k2_funct_1(sK4) = k1_xboole_0 ),
% 2.66/0.98      inference(global_propositional_subsumption,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_4502,c_37,c_35,c_3372,c_3380,c_4503]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4720,plain,
% 2.66/0.98      ( k2_funct_1(sK4) = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 2.66/0.98      inference(renaming,[status(thm)],[c_4719]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3,plain,
% 2.66/0.98      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.66/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3662,plain,
% 2.66/0.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 2.66/0.98      | r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0) ),
% 2.66/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4676,plain,
% 2.66/0.98      ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2))
% 2.66/0.98      | r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4)) ),
% 2.66/0.98      inference(instantiation,[status(thm)],[c_3662]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_6,plain,
% 2.66/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.66/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_3375,plain,
% 2.66/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/0.98      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 2.66/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(c_4184,plain,
% 2.66/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.66/0.98      | ~ r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) ),
% 2.66/0.98      inference(instantiation,[status(thm)],[c_3375]) ).
% 2.66/0.98  
% 2.66/0.98  cnf(contradiction,plain,
% 2.66/0.98      ( $false ),
% 2.66/0.98      inference(minisat,
% 2.66/0.98                [status(thm)],
% 2.66/0.98                [c_6402,c_5851,c_5405,c_5278,c_5276,c_4720,c_4676,c_4184,
% 2.66/0.98                 c_5]) ).
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.66/0.98  
% 2.66/0.98  ------                               Statistics
% 2.66/0.98  
% 2.66/0.98  ------ General
% 2.66/0.98  
% 2.66/0.98  abstr_ref_over_cycles:                  0
% 2.66/0.98  abstr_ref_under_cycles:                 0
% 2.66/0.98  gc_basic_clause_elim:                   0
% 2.66/0.98  forced_gc_time:                         0
% 2.66/0.98  parsing_time:                           0.01
% 2.66/0.98  unif_index_cands_time:                  0.
% 2.66/0.98  unif_index_add_time:                    0.
% 2.66/0.98  orderings_time:                         0.
% 2.66/0.98  out_proof_time:                         0.009
% 2.66/0.98  total_time:                             0.177
% 2.66/0.98  num_of_symbols:                         54
% 2.66/0.98  num_of_terms:                           3970
% 2.66/0.98  
% 2.66/0.98  ------ Preprocessing
% 2.66/0.98  
% 2.66/0.98  num_of_splits:                          0
% 2.66/0.98  num_of_split_atoms:                     0
% 2.66/0.98  num_of_reused_defs:                     0
% 2.66/0.98  num_eq_ax_congr_red:                    22
% 2.66/0.98  num_of_sem_filtered_clauses:            1
% 2.66/0.98  num_of_subtypes:                        0
% 2.66/0.98  monotx_restored_types:                  0
% 2.66/0.98  sat_num_of_epr_types:                   0
% 2.66/0.98  sat_num_of_non_cyclic_types:            0
% 2.66/0.98  sat_guarded_non_collapsed_types:        0
% 2.66/0.98  num_pure_diseq_elim:                    0
% 2.66/0.98  simp_replaced_by:                       0
% 2.66/0.98  res_preprocessed:                       178
% 2.66/0.98  prep_upred:                             0
% 2.66/0.98  prep_unflattend:                        103
% 2.66/0.98  smt_new_axioms:                         0
% 2.66/0.98  pred_elim_cands:                        6
% 2.66/0.98  pred_elim:                              3
% 2.66/0.98  pred_elim_cl:                           -1
% 2.66/0.98  pred_elim_cycles:                       10
% 2.66/0.98  merged_defs:                            8
% 2.66/0.98  merged_defs_ncl:                        0
% 2.66/0.98  bin_hyper_res:                          8
% 2.66/0.98  prep_cycles:                            4
% 2.66/0.98  pred_elim_time:                         0.029
% 2.66/0.98  splitting_time:                         0.
% 2.66/0.98  sem_filter_time:                        0.
% 2.66/0.98  monotx_time:                            0.
% 2.66/0.98  subtype_inf_time:                       0.
% 2.66/0.98  
% 2.66/0.98  ------ Problem properties
% 2.66/0.98  
% 2.66/0.98  clauses:                                37
% 2.66/0.98  conjectures:                            3
% 2.66/0.98  epr:                                    4
% 2.66/0.98  horn:                                   30
% 2.66/0.98  ground:                                 16
% 2.66/0.98  unary:                                  7
% 2.66/0.98  binary:                                 12
% 2.66/0.98  lits:                                   97
% 2.66/0.98  lits_eq:                                34
% 2.66/0.98  fd_pure:                                0
% 2.66/0.98  fd_pseudo:                              0
% 2.66/0.98  fd_cond:                                3
% 2.66/0.98  fd_pseudo_cond:                         0
% 2.66/0.98  ac_symbols:                             0
% 2.66/0.98  
% 2.66/0.98  ------ Propositional Solver
% 2.66/0.98  
% 2.66/0.98  prop_solver_calls:                      28
% 2.66/0.98  prop_fast_solver_calls:                 1431
% 2.66/0.98  smt_solver_calls:                       0
% 2.66/0.98  smt_fast_solver_calls:                  0
% 2.66/0.98  prop_num_of_clauses:                    1806
% 2.66/0.98  prop_preprocess_simplified:             6622
% 2.66/0.98  prop_fo_subsumed:                       31
% 2.66/0.98  prop_solver_time:                       0.
% 2.66/0.98  smt_solver_time:                        0.
% 2.66/0.98  smt_fast_solver_time:                   0.
% 2.66/0.98  prop_fast_solver_time:                  0.
% 2.66/0.98  prop_unsat_core_time:                   0.
% 2.66/0.98  
% 2.66/0.98  ------ QBF
% 2.66/0.98  
% 2.66/0.98  qbf_q_res:                              0
% 2.66/0.98  qbf_num_tautologies:                    0
% 2.66/0.98  qbf_prep_cycles:                        0
% 2.66/0.98  
% 2.66/0.98  ------ BMC1
% 2.66/0.98  
% 2.66/0.98  bmc1_current_bound:                     -1
% 2.66/0.98  bmc1_last_solved_bound:                 -1
% 2.66/0.98  bmc1_unsat_core_size:                   -1
% 2.66/0.98  bmc1_unsat_core_parents_size:           -1
% 2.66/0.98  bmc1_merge_next_fun:                    0
% 2.66/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.66/0.98  
% 2.66/0.98  ------ Instantiation
% 2.66/0.98  
% 2.66/0.98  inst_num_of_clauses:                    513
% 2.66/0.98  inst_num_in_passive:                    164
% 2.66/0.98  inst_num_in_active:                     285
% 2.66/0.98  inst_num_in_unprocessed:                63
% 2.66/0.98  inst_num_of_loops:                      377
% 2.66/0.98  inst_num_of_learning_restarts:          0
% 2.66/0.98  inst_num_moves_active_passive:          88
% 2.66/0.98  inst_lit_activity:                      0
% 2.66/0.98  inst_lit_activity_moves:                0
% 2.66/0.98  inst_num_tautologies:                   0
% 2.66/0.98  inst_num_prop_implied:                  0
% 2.66/0.98  inst_num_existing_simplified:           0
% 2.66/0.98  inst_num_eq_res_simplified:             0
% 2.66/0.98  inst_num_child_elim:                    0
% 2.66/0.98  inst_num_of_dismatching_blockings:      107
% 2.66/0.98  inst_num_of_non_proper_insts:           470
% 2.66/0.98  inst_num_of_duplicates:                 0
% 2.66/0.98  inst_inst_num_from_inst_to_res:         0
% 2.66/0.98  inst_dismatching_checking_time:         0.
% 2.66/0.98  
% 2.66/0.98  ------ Resolution
% 2.66/0.98  
% 2.66/0.98  res_num_of_clauses:                     0
% 2.66/0.98  res_num_in_passive:                     0
% 2.66/0.98  res_num_in_active:                      0
% 2.66/0.98  res_num_of_loops:                       182
% 2.66/0.98  res_forward_subset_subsumed:            26
% 2.66/0.98  res_backward_subset_subsumed:           0
% 2.66/0.98  res_forward_subsumed:                   1
% 2.66/0.98  res_backward_subsumed:                  1
% 2.66/0.98  res_forward_subsumption_resolution:     2
% 2.66/0.98  res_backward_subsumption_resolution:    0
% 2.66/0.98  res_clause_to_clause_subsumption:       205
% 2.66/0.98  res_orphan_elimination:                 0
% 2.66/0.98  res_tautology_del:                      76
% 2.66/0.98  res_num_eq_res_simplified:              0
% 2.66/0.98  res_num_sel_changes:                    0
% 2.66/0.98  res_moves_from_active_to_pass:          0
% 2.66/0.98  
% 2.66/0.98  ------ Superposition
% 2.66/0.98  
% 2.66/0.98  sup_time_total:                         0.
% 2.66/0.98  sup_time_generating:                    0.
% 2.66/0.98  sup_time_sim_full:                      0.
% 2.66/0.98  sup_time_sim_immed:                     0.
% 2.66/0.98  
% 2.66/0.98  sup_num_of_clauses:                     79
% 2.66/0.98  sup_num_in_active:                      41
% 2.66/0.98  sup_num_in_passive:                     38
% 2.66/0.98  sup_num_of_loops:                       74
% 2.66/0.98  sup_fw_superposition:                   41
% 2.66/0.98  sup_bw_superposition:                   38
% 2.66/0.98  sup_immediate_simplified:               47
% 2.66/0.98  sup_given_eliminated:                   0
% 2.66/0.98  comparisons_done:                       0
% 2.66/0.98  comparisons_avoided:                    7
% 2.66/0.98  
% 2.66/0.98  ------ Simplifications
% 2.66/0.98  
% 2.66/0.98  
% 2.66/0.98  sim_fw_subset_subsumed:                 11
% 2.66/0.98  sim_bw_subset_subsumed:                 5
% 2.66/0.98  sim_fw_subsumed:                        5
% 2.66/0.98  sim_bw_subsumed:                        1
% 2.66/0.98  sim_fw_subsumption_res:                 1
% 2.66/0.98  sim_bw_subsumption_res:                 0
% 2.66/0.98  sim_tautology_del:                      4
% 2.66/0.98  sim_eq_tautology_del:                   3
% 2.66/0.98  sim_eq_res_simp:                        5
% 2.66/0.98  sim_fw_demodulated:                     1
% 2.66/0.98  sim_bw_demodulated:                     41
% 2.66/0.98  sim_light_normalised:                   23
% 2.66/0.98  sim_joinable_taut:                      0
% 2.66/0.98  sim_joinable_simp:                      0
% 2.66/0.98  sim_ac_normalised:                      0
% 2.66/0.98  sim_smt_subsumption:                    0
% 2.66/0.98  
%------------------------------------------------------------------------------

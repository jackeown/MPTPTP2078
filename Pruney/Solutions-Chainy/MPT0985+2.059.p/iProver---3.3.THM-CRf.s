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
% DateTime   : Thu Dec  3 12:02:31 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  163 (1856 expanded)
%              Number of clauses        :  105 ( 598 expanded)
%              Number of leaves         :   15 ( 365 expanded)
%              Depth                    :   18
%              Number of atoms          :  555 (9990 expanded)
%              Number of equality atoms :  282 (2164 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

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
    inference(ennf_transformation,[],[f21])).

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

fof(f83,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f75,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

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
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_408,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_409,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_411,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_37])).

cnf(c_1329,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1663,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1668,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1329,c_37,c_35,c_409,c_1663])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_366,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_29])).

cnf(c_367,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_1331,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_4031,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1331])).

cnf(c_1333,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1335,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2545,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1333,c_1335])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2557,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2545,c_33])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_394,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_34])).

cnf(c_395,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_397,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_37])).

cnf(c_1330,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_1672,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1330,c_37,c_35,c_395,c_1663])).

cnf(c_2571,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2557,c_1672])).

cnf(c_4036,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4031,c_2571])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1643,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1644,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1643])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1646,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1647,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1646])).

cnf(c_1664,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1663])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k2_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_479,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_463,c_367])).

cnf(c_1327,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_3375,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2557,c_1327])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_105,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_106,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_795,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1811,plain,
    ( k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_2045,plain,
    ( k1_relat_1(sK2) != k1_relat_1(X0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1811])).

cnf(c_2047,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2045])).

cnf(c_802,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_2046,plain,
    ( k1_relat_1(sK2) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_2048,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2046])).

cnf(c_3035,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_3036,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3035])).

cnf(c_3398,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3375])).

cnf(c_3880,plain,
    ( sK1 != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3375,c_37,c_35,c_11,c_105,c_106,c_1663,c_2047,c_2048,c_3036,c_3398])).

cnf(c_3881,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3880])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_659,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_661,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_659,c_35])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1336,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2792,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1333,c_1336])).

cnf(c_2883,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_661,c_2792])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_669,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_670,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_682,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_670,c_17])).

cnf(c_1318,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_671,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_1927,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1318,c_38,c_40,c_671,c_1644,c_1647,c_1664])).

cnf(c_1928,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1927])).

cnf(c_1931,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1928,c_1668,c_1672])).

cnf(c_2569,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2557,c_1931])).

cnf(c_2579,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2569])).

cnf(c_3366,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2883,c_2579])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_348,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_30])).

cnf(c_349,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_688,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_349,c_32])).

cnf(c_689,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_701,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_689,c_17])).

cnf(c_1317,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_690,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_1743,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1317,c_38,c_40,c_690,c_1644,c_1647,c_1664])).

cnf(c_1744,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1743])).

cnf(c_1747,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1744,c_1668,c_1672])).

cnf(c_3885,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3366,c_1747,c_2557,c_3881])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1334,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4153,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1334])).

cnf(c_4182,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4153,c_2571])).

cnf(c_4723,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4182,c_38,c_40,c_1644,c_1647,c_1664])).

cnf(c_4728,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2883,c_4723])).

cnf(c_5223,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4036,c_37,c_38,c_35,c_40,c_11,c_105,c_106,c_1644,c_1647,c_1663,c_1664,c_1747,c_2047,c_2048,c_2557,c_3036,c_3366,c_3398,c_3881,c_4728])).

cnf(c_5237,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_5223,c_3885])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.84/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.00  
% 2.84/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.84/1.00  
% 2.84/1.00  ------  iProver source info
% 2.84/1.00  
% 2.84/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.84/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.84/1.00  git: non_committed_changes: false
% 2.84/1.00  git: last_make_outside_of_git: false
% 2.84/1.00  
% 2.84/1.00  ------ 
% 2.84/1.00  
% 2.84/1.00  ------ Input Options
% 2.84/1.00  
% 2.84/1.00  --out_options                           all
% 2.84/1.00  --tptp_safe_out                         true
% 2.84/1.00  --problem_path                          ""
% 2.84/1.00  --include_path                          ""
% 2.84/1.00  --clausifier                            res/vclausify_rel
% 2.84/1.00  --clausifier_options                    --mode clausify
% 2.84/1.00  --stdin                                 false
% 2.84/1.00  --stats_out                             all
% 2.84/1.00  
% 2.84/1.00  ------ General Options
% 2.84/1.00  
% 2.84/1.00  --fof                                   false
% 2.84/1.00  --time_out_real                         305.
% 2.84/1.00  --time_out_virtual                      -1.
% 2.84/1.00  --symbol_type_check                     false
% 2.84/1.00  --clausify_out                          false
% 2.84/1.00  --sig_cnt_out                           false
% 2.84/1.00  --trig_cnt_out                          false
% 2.84/1.00  --trig_cnt_out_tolerance                1.
% 2.84/1.00  --trig_cnt_out_sk_spl                   false
% 2.84/1.00  --abstr_cl_out                          false
% 2.84/1.00  
% 2.84/1.00  ------ Global Options
% 2.84/1.00  
% 2.84/1.00  --schedule                              default
% 2.84/1.00  --add_important_lit                     false
% 2.84/1.00  --prop_solver_per_cl                    1000
% 2.84/1.00  --min_unsat_core                        false
% 2.84/1.00  --soft_assumptions                      false
% 2.84/1.00  --soft_lemma_size                       3
% 2.84/1.00  --prop_impl_unit_size                   0
% 2.84/1.00  --prop_impl_unit                        []
% 2.84/1.00  --share_sel_clauses                     true
% 2.84/1.00  --reset_solvers                         false
% 2.84/1.00  --bc_imp_inh                            [conj_cone]
% 2.84/1.00  --conj_cone_tolerance                   3.
% 2.84/1.00  --extra_neg_conj                        none
% 2.84/1.00  --large_theory_mode                     true
% 2.84/1.00  --prolific_symb_bound                   200
% 2.84/1.00  --lt_threshold                          2000
% 2.84/1.00  --clause_weak_htbl                      true
% 2.84/1.00  --gc_record_bc_elim                     false
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing Options
% 2.84/1.00  
% 2.84/1.00  --preprocessing_flag                    true
% 2.84/1.00  --time_out_prep_mult                    0.1
% 2.84/1.00  --splitting_mode                        input
% 2.84/1.00  --splitting_grd                         true
% 2.84/1.00  --splitting_cvd                         false
% 2.84/1.00  --splitting_cvd_svl                     false
% 2.84/1.00  --splitting_nvd                         32
% 2.84/1.00  --sub_typing                            true
% 2.84/1.00  --prep_gs_sim                           true
% 2.84/1.00  --prep_unflatten                        true
% 2.84/1.00  --prep_res_sim                          true
% 2.84/1.00  --prep_upred                            true
% 2.84/1.00  --prep_sem_filter                       exhaustive
% 2.84/1.00  --prep_sem_filter_out                   false
% 2.84/1.00  --pred_elim                             true
% 2.84/1.00  --res_sim_input                         true
% 2.84/1.00  --eq_ax_congr_red                       true
% 2.84/1.00  --pure_diseq_elim                       true
% 2.84/1.00  --brand_transform                       false
% 2.84/1.00  --non_eq_to_eq                          false
% 2.84/1.00  --prep_def_merge                        true
% 2.84/1.00  --prep_def_merge_prop_impl              false
% 2.84/1.00  --prep_def_merge_mbd                    true
% 2.84/1.00  --prep_def_merge_tr_red                 false
% 2.84/1.00  --prep_def_merge_tr_cl                  false
% 2.84/1.00  --smt_preprocessing                     true
% 2.84/1.00  --smt_ac_axioms                         fast
% 2.84/1.00  --preprocessed_out                      false
% 2.84/1.00  --preprocessed_stats                    false
% 2.84/1.00  
% 2.84/1.00  ------ Abstraction refinement Options
% 2.84/1.00  
% 2.84/1.00  --abstr_ref                             []
% 2.84/1.00  --abstr_ref_prep                        false
% 2.84/1.00  --abstr_ref_until_sat                   false
% 2.84/1.00  --abstr_ref_sig_restrict                funpre
% 2.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/1.00  --abstr_ref_under                       []
% 2.84/1.00  
% 2.84/1.00  ------ SAT Options
% 2.84/1.00  
% 2.84/1.00  --sat_mode                              false
% 2.84/1.00  --sat_fm_restart_options                ""
% 2.84/1.00  --sat_gr_def                            false
% 2.84/1.00  --sat_epr_types                         true
% 2.84/1.00  --sat_non_cyclic_types                  false
% 2.84/1.00  --sat_finite_models                     false
% 2.84/1.00  --sat_fm_lemmas                         false
% 2.84/1.00  --sat_fm_prep                           false
% 2.84/1.00  --sat_fm_uc_incr                        true
% 2.84/1.00  --sat_out_model                         small
% 2.84/1.00  --sat_out_clauses                       false
% 2.84/1.00  
% 2.84/1.00  ------ QBF Options
% 2.84/1.00  
% 2.84/1.00  --qbf_mode                              false
% 2.84/1.00  --qbf_elim_univ                         false
% 2.84/1.00  --qbf_dom_inst                          none
% 2.84/1.00  --qbf_dom_pre_inst                      false
% 2.84/1.00  --qbf_sk_in                             false
% 2.84/1.00  --qbf_pred_elim                         true
% 2.84/1.00  --qbf_split                             512
% 2.84/1.00  
% 2.84/1.00  ------ BMC1 Options
% 2.84/1.00  
% 2.84/1.00  --bmc1_incremental                      false
% 2.84/1.00  --bmc1_axioms                           reachable_all
% 2.84/1.00  --bmc1_min_bound                        0
% 2.84/1.00  --bmc1_max_bound                        -1
% 2.84/1.00  --bmc1_max_bound_default                -1
% 2.84/1.00  --bmc1_symbol_reachability              true
% 2.84/1.00  --bmc1_property_lemmas                  false
% 2.84/1.00  --bmc1_k_induction                      false
% 2.84/1.00  --bmc1_non_equiv_states                 false
% 2.84/1.00  --bmc1_deadlock                         false
% 2.84/1.00  --bmc1_ucm                              false
% 2.84/1.00  --bmc1_add_unsat_core                   none
% 2.84/1.00  --bmc1_unsat_core_children              false
% 2.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/1.00  --bmc1_out_stat                         full
% 2.84/1.00  --bmc1_ground_init                      false
% 2.84/1.00  --bmc1_pre_inst_next_state              false
% 2.84/1.00  --bmc1_pre_inst_state                   false
% 2.84/1.00  --bmc1_pre_inst_reach_state             false
% 2.84/1.00  --bmc1_out_unsat_core                   false
% 2.84/1.00  --bmc1_aig_witness_out                  false
% 2.84/1.00  --bmc1_verbose                          false
% 2.84/1.00  --bmc1_dump_clauses_tptp                false
% 2.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.84/1.00  --bmc1_dump_file                        -
% 2.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.84/1.00  --bmc1_ucm_extend_mode                  1
% 2.84/1.00  --bmc1_ucm_init_mode                    2
% 2.84/1.00  --bmc1_ucm_cone_mode                    none
% 2.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.84/1.00  --bmc1_ucm_relax_model                  4
% 2.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/1.00  --bmc1_ucm_layered_model                none
% 2.84/1.00  --bmc1_ucm_max_lemma_size               10
% 2.84/1.00  
% 2.84/1.00  ------ AIG Options
% 2.84/1.00  
% 2.84/1.00  --aig_mode                              false
% 2.84/1.00  
% 2.84/1.00  ------ Instantiation Options
% 2.84/1.00  
% 2.84/1.00  --instantiation_flag                    true
% 2.84/1.00  --inst_sos_flag                         false
% 2.84/1.00  --inst_sos_phase                        true
% 2.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/1.00  --inst_lit_sel_side                     num_symb
% 2.84/1.00  --inst_solver_per_active                1400
% 2.84/1.00  --inst_solver_calls_frac                1.
% 2.84/1.00  --inst_passive_queue_type               priority_queues
% 2.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/1.00  --inst_passive_queues_freq              [25;2]
% 2.84/1.00  --inst_dismatching                      true
% 2.84/1.00  --inst_eager_unprocessed_to_passive     true
% 2.84/1.00  --inst_prop_sim_given                   true
% 2.84/1.00  --inst_prop_sim_new                     false
% 2.84/1.00  --inst_subs_new                         false
% 2.84/1.00  --inst_eq_res_simp                      false
% 2.84/1.00  --inst_subs_given                       false
% 2.84/1.00  --inst_orphan_elimination               true
% 2.84/1.00  --inst_learning_loop_flag               true
% 2.84/1.00  --inst_learning_start                   3000
% 2.84/1.00  --inst_learning_factor                  2
% 2.84/1.00  --inst_start_prop_sim_after_learn       3
% 2.84/1.00  --inst_sel_renew                        solver
% 2.84/1.00  --inst_lit_activity_flag                true
% 2.84/1.00  --inst_restr_to_given                   false
% 2.84/1.00  --inst_activity_threshold               500
% 2.84/1.00  --inst_out_proof                        true
% 2.84/1.00  
% 2.84/1.00  ------ Resolution Options
% 2.84/1.00  
% 2.84/1.00  --resolution_flag                       true
% 2.84/1.00  --res_lit_sel                           adaptive
% 2.84/1.00  --res_lit_sel_side                      none
% 2.84/1.00  --res_ordering                          kbo
% 2.84/1.00  --res_to_prop_solver                    active
% 2.84/1.00  --res_prop_simpl_new                    false
% 2.84/1.00  --res_prop_simpl_given                  true
% 2.84/1.00  --res_passive_queue_type                priority_queues
% 2.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/1.00  --res_passive_queues_freq               [15;5]
% 2.84/1.00  --res_forward_subs                      full
% 2.84/1.00  --res_backward_subs                     full
% 2.84/1.00  --res_forward_subs_resolution           true
% 2.84/1.00  --res_backward_subs_resolution          true
% 2.84/1.00  --res_orphan_elimination                true
% 2.84/1.00  --res_time_limit                        2.
% 2.84/1.00  --res_out_proof                         true
% 2.84/1.00  
% 2.84/1.00  ------ Superposition Options
% 2.84/1.00  
% 2.84/1.00  --superposition_flag                    true
% 2.84/1.00  --sup_passive_queue_type                priority_queues
% 2.84/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.84/1.00  --demod_completeness_check              fast
% 2.84/1.00  --demod_use_ground                      true
% 2.84/1.00  --sup_to_prop_solver                    passive
% 2.84/1.00  --sup_prop_simpl_new                    true
% 2.84/1.00  --sup_prop_simpl_given                  true
% 2.84/1.00  --sup_fun_splitting                     false
% 2.84/1.00  --sup_smt_interval                      50000
% 2.84/1.00  
% 2.84/1.00  ------ Superposition Simplification Setup
% 2.84/1.00  
% 2.84/1.00  --sup_indices_passive                   []
% 2.84/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_full_bw                           [BwDemod]
% 2.84/1.00  --sup_immed_triv                        [TrivRules]
% 2.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_immed_bw_main                     []
% 2.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.00  
% 2.84/1.00  ------ Combination Options
% 2.84/1.00  
% 2.84/1.00  --comb_res_mult                         3
% 2.84/1.00  --comb_sup_mult                         2
% 2.84/1.00  --comb_inst_mult                        10
% 2.84/1.00  
% 2.84/1.00  ------ Debug Options
% 2.84/1.00  
% 2.84/1.00  --dbg_backtrace                         false
% 2.84/1.00  --dbg_dump_prop_clauses                 false
% 2.84/1.00  --dbg_dump_prop_clauses_file            -
% 2.84/1.00  --dbg_out_stat                          false
% 2.84/1.00  ------ Parsing...
% 2.84/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.84/1.00  ------ Proving...
% 2.84/1.00  ------ Problem Properties 
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  clauses                                 38
% 2.84/1.00  conjectures                             3
% 2.84/1.00  EPR                                     3
% 2.84/1.00  Horn                                    32
% 2.84/1.00  unary                                   10
% 2.84/1.00  binary                                  6
% 2.84/1.00  lits                                    107
% 2.84/1.00  lits eq                                 47
% 2.84/1.00  fd_pure                                 0
% 2.84/1.00  fd_pseudo                               0
% 2.84/1.00  fd_cond                                 3
% 2.84/1.00  fd_pseudo_cond                          1
% 2.84/1.00  AC symbols                              0
% 2.84/1.00  
% 2.84/1.00  ------ Schedule dynamic 5 is on 
% 2.84/1.00  
% 2.84/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  ------ 
% 2.84/1.00  Current options:
% 2.84/1.00  ------ 
% 2.84/1.00  
% 2.84/1.00  ------ Input Options
% 2.84/1.00  
% 2.84/1.00  --out_options                           all
% 2.84/1.00  --tptp_safe_out                         true
% 2.84/1.00  --problem_path                          ""
% 2.84/1.00  --include_path                          ""
% 2.84/1.00  --clausifier                            res/vclausify_rel
% 2.84/1.00  --clausifier_options                    --mode clausify
% 2.84/1.00  --stdin                                 false
% 2.84/1.00  --stats_out                             all
% 2.84/1.00  
% 2.84/1.00  ------ General Options
% 2.84/1.00  
% 2.84/1.00  --fof                                   false
% 2.84/1.00  --time_out_real                         305.
% 2.84/1.00  --time_out_virtual                      -1.
% 2.84/1.00  --symbol_type_check                     false
% 2.84/1.00  --clausify_out                          false
% 2.84/1.00  --sig_cnt_out                           false
% 2.84/1.00  --trig_cnt_out                          false
% 2.84/1.00  --trig_cnt_out_tolerance                1.
% 2.84/1.00  --trig_cnt_out_sk_spl                   false
% 2.84/1.00  --abstr_cl_out                          false
% 2.84/1.00  
% 2.84/1.00  ------ Global Options
% 2.84/1.00  
% 2.84/1.00  --schedule                              default
% 2.84/1.00  --add_important_lit                     false
% 2.84/1.00  --prop_solver_per_cl                    1000
% 2.84/1.00  --min_unsat_core                        false
% 2.84/1.00  --soft_assumptions                      false
% 2.84/1.00  --soft_lemma_size                       3
% 2.84/1.00  --prop_impl_unit_size                   0
% 2.84/1.00  --prop_impl_unit                        []
% 2.84/1.00  --share_sel_clauses                     true
% 2.84/1.00  --reset_solvers                         false
% 2.84/1.00  --bc_imp_inh                            [conj_cone]
% 2.84/1.00  --conj_cone_tolerance                   3.
% 2.84/1.00  --extra_neg_conj                        none
% 2.84/1.00  --large_theory_mode                     true
% 2.84/1.00  --prolific_symb_bound                   200
% 2.84/1.00  --lt_threshold                          2000
% 2.84/1.00  --clause_weak_htbl                      true
% 2.84/1.00  --gc_record_bc_elim                     false
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing Options
% 2.84/1.00  
% 2.84/1.00  --preprocessing_flag                    true
% 2.84/1.00  --time_out_prep_mult                    0.1
% 2.84/1.00  --splitting_mode                        input
% 2.84/1.00  --splitting_grd                         true
% 2.84/1.00  --splitting_cvd                         false
% 2.84/1.00  --splitting_cvd_svl                     false
% 2.84/1.00  --splitting_nvd                         32
% 2.84/1.00  --sub_typing                            true
% 2.84/1.00  --prep_gs_sim                           true
% 2.84/1.00  --prep_unflatten                        true
% 2.84/1.00  --prep_res_sim                          true
% 2.84/1.00  --prep_upred                            true
% 2.84/1.00  --prep_sem_filter                       exhaustive
% 2.84/1.00  --prep_sem_filter_out                   false
% 2.84/1.00  --pred_elim                             true
% 2.84/1.00  --res_sim_input                         true
% 2.84/1.00  --eq_ax_congr_red                       true
% 2.84/1.00  --pure_diseq_elim                       true
% 2.84/1.00  --brand_transform                       false
% 2.84/1.00  --non_eq_to_eq                          false
% 2.84/1.00  --prep_def_merge                        true
% 2.84/1.00  --prep_def_merge_prop_impl              false
% 2.84/1.00  --prep_def_merge_mbd                    true
% 2.84/1.00  --prep_def_merge_tr_red                 false
% 2.84/1.00  --prep_def_merge_tr_cl                  false
% 2.84/1.00  --smt_preprocessing                     true
% 2.84/1.00  --smt_ac_axioms                         fast
% 2.84/1.00  --preprocessed_out                      false
% 2.84/1.00  --preprocessed_stats                    false
% 2.84/1.00  
% 2.84/1.00  ------ Abstraction refinement Options
% 2.84/1.00  
% 2.84/1.00  --abstr_ref                             []
% 2.84/1.00  --abstr_ref_prep                        false
% 2.84/1.00  --abstr_ref_until_sat                   false
% 2.84/1.00  --abstr_ref_sig_restrict                funpre
% 2.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/1.00  --abstr_ref_under                       []
% 2.84/1.00  
% 2.84/1.00  ------ SAT Options
% 2.84/1.00  
% 2.84/1.00  --sat_mode                              false
% 2.84/1.00  --sat_fm_restart_options                ""
% 2.84/1.00  --sat_gr_def                            false
% 2.84/1.00  --sat_epr_types                         true
% 2.84/1.00  --sat_non_cyclic_types                  false
% 2.84/1.00  --sat_finite_models                     false
% 2.84/1.00  --sat_fm_lemmas                         false
% 2.84/1.00  --sat_fm_prep                           false
% 2.84/1.00  --sat_fm_uc_incr                        true
% 2.84/1.00  --sat_out_model                         small
% 2.84/1.00  --sat_out_clauses                       false
% 2.84/1.00  
% 2.84/1.00  ------ QBF Options
% 2.84/1.00  
% 2.84/1.00  --qbf_mode                              false
% 2.84/1.00  --qbf_elim_univ                         false
% 2.84/1.00  --qbf_dom_inst                          none
% 2.84/1.00  --qbf_dom_pre_inst                      false
% 2.84/1.00  --qbf_sk_in                             false
% 2.84/1.00  --qbf_pred_elim                         true
% 2.84/1.00  --qbf_split                             512
% 2.84/1.00  
% 2.84/1.00  ------ BMC1 Options
% 2.84/1.00  
% 2.84/1.00  --bmc1_incremental                      false
% 2.84/1.00  --bmc1_axioms                           reachable_all
% 2.84/1.00  --bmc1_min_bound                        0
% 2.84/1.00  --bmc1_max_bound                        -1
% 2.84/1.00  --bmc1_max_bound_default                -1
% 2.84/1.00  --bmc1_symbol_reachability              true
% 2.84/1.00  --bmc1_property_lemmas                  false
% 2.84/1.00  --bmc1_k_induction                      false
% 2.84/1.00  --bmc1_non_equiv_states                 false
% 2.84/1.00  --bmc1_deadlock                         false
% 2.84/1.00  --bmc1_ucm                              false
% 2.84/1.00  --bmc1_add_unsat_core                   none
% 2.84/1.00  --bmc1_unsat_core_children              false
% 2.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/1.00  --bmc1_out_stat                         full
% 2.84/1.00  --bmc1_ground_init                      false
% 2.84/1.00  --bmc1_pre_inst_next_state              false
% 2.84/1.00  --bmc1_pre_inst_state                   false
% 2.84/1.00  --bmc1_pre_inst_reach_state             false
% 2.84/1.00  --bmc1_out_unsat_core                   false
% 2.84/1.00  --bmc1_aig_witness_out                  false
% 2.84/1.00  --bmc1_verbose                          false
% 2.84/1.00  --bmc1_dump_clauses_tptp                false
% 2.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.84/1.00  --bmc1_dump_file                        -
% 2.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.84/1.00  --bmc1_ucm_extend_mode                  1
% 2.84/1.00  --bmc1_ucm_init_mode                    2
% 2.84/1.00  --bmc1_ucm_cone_mode                    none
% 2.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.84/1.00  --bmc1_ucm_relax_model                  4
% 2.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/1.00  --bmc1_ucm_layered_model                none
% 2.84/1.00  --bmc1_ucm_max_lemma_size               10
% 2.84/1.00  
% 2.84/1.00  ------ AIG Options
% 2.84/1.00  
% 2.84/1.00  --aig_mode                              false
% 2.84/1.00  
% 2.84/1.00  ------ Instantiation Options
% 2.84/1.00  
% 2.84/1.00  --instantiation_flag                    true
% 2.84/1.00  --inst_sos_flag                         false
% 2.84/1.00  --inst_sos_phase                        true
% 2.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/1.00  --inst_lit_sel_side                     none
% 2.84/1.00  --inst_solver_per_active                1400
% 2.84/1.00  --inst_solver_calls_frac                1.
% 2.84/1.00  --inst_passive_queue_type               priority_queues
% 2.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/1.00  --inst_passive_queues_freq              [25;2]
% 2.84/1.00  --inst_dismatching                      true
% 2.84/1.00  --inst_eager_unprocessed_to_passive     true
% 2.84/1.00  --inst_prop_sim_given                   true
% 2.84/1.00  --inst_prop_sim_new                     false
% 2.84/1.00  --inst_subs_new                         false
% 2.84/1.00  --inst_eq_res_simp                      false
% 2.84/1.00  --inst_subs_given                       false
% 2.84/1.00  --inst_orphan_elimination               true
% 2.84/1.00  --inst_learning_loop_flag               true
% 2.84/1.00  --inst_learning_start                   3000
% 2.84/1.00  --inst_learning_factor                  2
% 2.84/1.00  --inst_start_prop_sim_after_learn       3
% 2.84/1.00  --inst_sel_renew                        solver
% 2.84/1.00  --inst_lit_activity_flag                true
% 2.84/1.00  --inst_restr_to_given                   false
% 2.84/1.00  --inst_activity_threshold               500
% 2.84/1.00  --inst_out_proof                        true
% 2.84/1.00  
% 2.84/1.00  ------ Resolution Options
% 2.84/1.00  
% 2.84/1.00  --resolution_flag                       false
% 2.84/1.00  --res_lit_sel                           adaptive
% 2.84/1.00  --res_lit_sel_side                      none
% 2.84/1.00  --res_ordering                          kbo
% 2.84/1.00  --res_to_prop_solver                    active
% 2.84/1.00  --res_prop_simpl_new                    false
% 2.84/1.00  --res_prop_simpl_given                  true
% 2.84/1.00  --res_passive_queue_type                priority_queues
% 2.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/1.00  --res_passive_queues_freq               [15;5]
% 2.84/1.00  --res_forward_subs                      full
% 2.84/1.00  --res_backward_subs                     full
% 2.84/1.00  --res_forward_subs_resolution           true
% 2.84/1.00  --res_backward_subs_resolution          true
% 2.84/1.00  --res_orphan_elimination                true
% 2.84/1.00  --res_time_limit                        2.
% 2.84/1.00  --res_out_proof                         true
% 2.84/1.00  
% 2.84/1.00  ------ Superposition Options
% 2.84/1.00  
% 2.84/1.00  --superposition_flag                    true
% 2.84/1.00  --sup_passive_queue_type                priority_queues
% 2.84/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.84/1.00  --demod_completeness_check              fast
% 2.84/1.00  --demod_use_ground                      true
% 2.84/1.00  --sup_to_prop_solver                    passive
% 2.84/1.00  --sup_prop_simpl_new                    true
% 2.84/1.00  --sup_prop_simpl_given                  true
% 2.84/1.00  --sup_fun_splitting                     false
% 2.84/1.00  --sup_smt_interval                      50000
% 2.84/1.00  
% 2.84/1.00  ------ Superposition Simplification Setup
% 2.84/1.00  
% 2.84/1.00  --sup_indices_passive                   []
% 2.84/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_full_bw                           [BwDemod]
% 2.84/1.00  --sup_immed_triv                        [TrivRules]
% 2.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_immed_bw_main                     []
% 2.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.00  
% 2.84/1.00  ------ Combination Options
% 2.84/1.00  
% 2.84/1.00  --comb_res_mult                         3
% 2.84/1.00  --comb_sup_mult                         2
% 2.84/1.00  --comb_inst_mult                        10
% 2.84/1.00  
% 2.84/1.00  ------ Debug Options
% 2.84/1.00  
% 2.84/1.00  --dbg_backtrace                         false
% 2.84/1.00  --dbg_dump_prop_clauses                 false
% 2.84/1.00  --dbg_dump_prop_clauses_file            -
% 2.84/1.00  --dbg_out_stat                          false
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  ------ Proving...
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  % SZS status Theorem for theBenchmark.p
% 2.84/1.00  
% 2.84/1.00   Resolution empty clause
% 2.84/1.00  
% 2.84/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.84/1.00  
% 2.84/1.00  fof(f13,axiom,(
% 2.84/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f30,plain,(
% 2.84/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.84/1.00    inference(ennf_transformation,[],[f13])).
% 2.84/1.00  
% 2.84/1.00  fof(f31,plain,(
% 2.84/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.84/1.00    inference(flattening,[],[f30])).
% 2.84/1.00  
% 2.84/1.00  fof(f64,plain,(
% 2.84/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f31])).
% 2.84/1.00  
% 2.84/1.00  fof(f20,conjecture,(
% 2.84/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f21,negated_conjecture,(
% 2.84/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.84/1.00    inference(negated_conjecture,[],[f20])).
% 2.84/1.00  
% 2.84/1.00  fof(f41,plain,(
% 2.84/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.84/1.00    inference(ennf_transformation,[],[f21])).
% 2.84/1.00  
% 2.84/1.00  fof(f42,plain,(
% 2.84/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.84/1.00    inference(flattening,[],[f41])).
% 2.84/1.00  
% 2.84/1.00  fof(f46,plain,(
% 2.84/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.84/1.00    introduced(choice_axiom,[])).
% 2.84/1.00  
% 2.84/1.00  fof(f47,plain,(
% 2.84/1.00    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f46])).
% 2.84/1.00  
% 2.84/1.00  fof(f83,plain,(
% 2.84/1.00    v2_funct_1(sK2)),
% 2.84/1.00    inference(cnf_transformation,[],[f47])).
% 2.84/1.00  
% 2.84/1.00  fof(f80,plain,(
% 2.84/1.00    v1_funct_1(sK2)),
% 2.84/1.00    inference(cnf_transformation,[],[f47])).
% 2.84/1.00  
% 2.84/1.00  fof(f82,plain,(
% 2.84/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.84/1.00    inference(cnf_transformation,[],[f47])).
% 2.84/1.00  
% 2.84/1.00  fof(f14,axiom,(
% 2.84/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f32,plain,(
% 2.84/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.00    inference(ennf_transformation,[],[f14])).
% 2.84/1.00  
% 2.84/1.00  fof(f65,plain,(
% 2.84/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/1.00    inference(cnf_transformation,[],[f32])).
% 2.84/1.00  
% 2.84/1.00  fof(f2,axiom,(
% 2.84/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f49,plain,(
% 2.84/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f2])).
% 2.84/1.00  
% 2.84/1.00  fof(f19,axiom,(
% 2.84/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f39,plain,(
% 2.84/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.84/1.00    inference(ennf_transformation,[],[f19])).
% 2.84/1.00  
% 2.84/1.00  fof(f40,plain,(
% 2.84/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.84/1.00    inference(flattening,[],[f39])).
% 2.84/1.00  
% 2.84/1.00  fof(f79,plain,(
% 2.84/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f40])).
% 2.84/1.00  
% 2.84/1.00  fof(f16,axiom,(
% 2.84/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f34,plain,(
% 2.84/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.00    inference(ennf_transformation,[],[f16])).
% 2.84/1.00  
% 2.84/1.00  fof(f67,plain,(
% 2.84/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/1.00    inference(cnf_transformation,[],[f34])).
% 2.84/1.00  
% 2.84/1.00  fof(f84,plain,(
% 2.84/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.84/1.00    inference(cnf_transformation,[],[f47])).
% 2.84/1.00  
% 2.84/1.00  fof(f63,plain,(
% 2.84/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f31])).
% 2.84/1.00  
% 2.84/1.00  fof(f12,axiom,(
% 2.84/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f28,plain,(
% 2.84/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.84/1.00    inference(ennf_transformation,[],[f12])).
% 2.84/1.00  
% 2.84/1.00  fof(f29,plain,(
% 2.84/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.84/1.00    inference(flattening,[],[f28])).
% 2.84/1.00  
% 2.84/1.00  fof(f62,plain,(
% 2.84/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f29])).
% 2.84/1.00  
% 2.84/1.00  fof(f61,plain,(
% 2.84/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f29])).
% 2.84/1.00  
% 2.84/1.00  fof(f17,axiom,(
% 2.84/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f35,plain,(
% 2.84/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.00    inference(ennf_transformation,[],[f17])).
% 2.84/1.00  
% 2.84/1.00  fof(f36,plain,(
% 2.84/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.00    inference(flattening,[],[f35])).
% 2.84/1.00  
% 2.84/1.00  fof(f45,plain,(
% 2.84/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.00    inference(nnf_transformation,[],[f36])).
% 2.84/1.00  
% 2.84/1.00  fof(f72,plain,(
% 2.84/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/1.00    inference(cnf_transformation,[],[f45])).
% 2.84/1.00  
% 2.84/1.00  fof(f90,plain,(
% 2.84/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.84/1.00    inference(equality_resolution,[],[f72])).
% 2.84/1.00  
% 2.84/1.00  fof(f18,axiom,(
% 2.84/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f37,plain,(
% 2.84/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.84/1.00    inference(ennf_transformation,[],[f18])).
% 2.84/1.00  
% 2.84/1.00  fof(f38,plain,(
% 2.84/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.84/1.00    inference(flattening,[],[f37])).
% 2.84/1.00  
% 2.84/1.00  fof(f75,plain,(
% 2.84/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f38])).
% 2.84/1.00  
% 2.84/1.00  fof(f10,axiom,(
% 2.84/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f58,plain,(
% 2.84/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.84/1.00    inference(cnf_transformation,[],[f10])).
% 2.84/1.00  
% 2.84/1.00  fof(f4,axiom,(
% 2.84/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f43,plain,(
% 2.84/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.84/1.00    inference(nnf_transformation,[],[f4])).
% 2.84/1.00  
% 2.84/1.00  fof(f44,plain,(
% 2.84/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.84/1.00    inference(flattening,[],[f43])).
% 2.84/1.00  
% 2.84/1.00  fof(f51,plain,(
% 2.84/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f44])).
% 2.84/1.00  
% 2.84/1.00  fof(f52,plain,(
% 2.84/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.84/1.00    inference(cnf_transformation,[],[f44])).
% 2.84/1.00  
% 2.84/1.00  fof(f87,plain,(
% 2.84/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.84/1.00    inference(equality_resolution,[],[f52])).
% 2.84/1.00  
% 2.84/1.00  fof(f68,plain,(
% 2.84/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/1.00    inference(cnf_transformation,[],[f45])).
% 2.84/1.00  
% 2.84/1.00  fof(f81,plain,(
% 2.84/1.00    v1_funct_2(sK2,sK0,sK1)),
% 2.84/1.00    inference(cnf_transformation,[],[f47])).
% 2.84/1.00  
% 2.84/1.00  fof(f15,axiom,(
% 2.84/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.84/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.84/1.00  
% 2.84/1.00  fof(f33,plain,(
% 2.84/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.00    inference(ennf_transformation,[],[f15])).
% 2.84/1.00  
% 2.84/1.00  fof(f66,plain,(
% 2.84/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/1.00    inference(cnf_transformation,[],[f33])).
% 2.84/1.00  
% 2.84/1.00  fof(f85,plain,(
% 2.84/1.00    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.84/1.00    inference(cnf_transformation,[],[f47])).
% 2.84/1.00  
% 2.84/1.00  fof(f78,plain,(
% 2.84/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f40])).
% 2.84/1.00  
% 2.84/1.00  fof(f76,plain,(
% 2.84/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.84/1.00    inference(cnf_transformation,[],[f38])).
% 2.84/1.00  
% 2.84/1.00  cnf(c_15,plain,
% 2.84/1.00      ( ~ v2_funct_1(X0)
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0)
% 2.84/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_34,negated_conjecture,
% 2.84/1.00      ( v2_funct_1(sK2) ),
% 2.84/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_408,plain,
% 2.84/1.00      ( ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0)
% 2.84/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.84/1.00      | sK2 != X0 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_34]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_409,plain,
% 2.84/1.00      ( ~ v1_funct_1(sK2)
% 2.84/1.00      | ~ v1_relat_1(sK2)
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_408]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_37,negated_conjecture,
% 2.84/1.00      ( v1_funct_1(sK2) ),
% 2.84/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_411,plain,
% 2.84/1.00      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_409,c_37]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1329,plain,
% 2.84/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.84/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_35,negated_conjecture,
% 2.84/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.84/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_17,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1663,plain,
% 2.84/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.84/1.00      | v1_relat_1(sK2) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1668,plain,
% 2.84/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_1329,c_37,c_35,c_409,c_1663]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1,plain,
% 2.84/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_29,plain,
% 2.84/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.84/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_366,plain,
% 2.84/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0)
% 2.84/1.00      | X1 != X2
% 2.84/1.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_29]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_367,plain,
% 2.84/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0)
% 2.84/1.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_366]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1331,plain,
% 2.84/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 2.84/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 2.84/1.00      | v1_funct_1(X0) != iProver_top
% 2.84/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4031,plain,
% 2.84/1.00      ( k1_relat_1(sK2) != k1_xboole_0
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) = iProver_top
% 2.84/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.84/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_1668,c_1331]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1333,plain,
% 2.84/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_19,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1335,plain,
% 2.84/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.84/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2545,plain,
% 2.84/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_1333,c_1335]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_33,negated_conjecture,
% 2.84/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.84/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2557,plain,
% 2.84/1.00      ( k2_relat_1(sK2) = sK1 ),
% 2.84/1.00      inference(light_normalisation,[status(thm)],[c_2545,c_33]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_16,plain,
% 2.84/1.00      ( ~ v2_funct_1(X0)
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0)
% 2.84/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_394,plain,
% 2.84/1.00      ( ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0)
% 2.84/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.84/1.00      | sK2 != X0 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_34]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_395,plain,
% 2.84/1.00      ( ~ v1_funct_1(sK2)
% 2.84/1.00      | ~ v1_relat_1(sK2)
% 2.84/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_394]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_397,plain,
% 2.84/1.00      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_395,c_37]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1330,plain,
% 2.84/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.84/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1672,plain,
% 2.84/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_1330,c_37,c_35,c_395,c_1663]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2571,plain,
% 2.84/1.00      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 2.84/1.00      inference(demodulation,[status(thm)],[c_2557,c_1672]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4036,plain,
% 2.84/1.00      ( k1_relat_1(sK2) != k1_xboole_0
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 2.84/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.84/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.84/1.00      inference(light_normalisation,[status(thm)],[c_4031,c_2571]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_38,plain,
% 2.84/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_40,plain,
% 2.84/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_13,plain,
% 2.84/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1643,plain,
% 2.84/1.00      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1644,plain,
% 2.84/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.84/1.00      | v1_funct_1(sK2) != iProver_top
% 2.84/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_1643]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_14,plain,
% 2.84/1.00      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.84/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1646,plain,
% 2.84/1.00      ( ~ v1_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1647,plain,
% 2.84/1.00      ( v1_funct_1(sK2) != iProver_top
% 2.84/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.84/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_1646]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1664,plain,
% 2.84/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.84/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_1663]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_21,plain,
% 2.84/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.84/1.00      | k1_xboole_0 = X1
% 2.84/1.00      | k1_xboole_0 = X0 ),
% 2.84/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_27,plain,
% 2.84/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_462,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.84/1.00      | ~ v1_funct_1(X2)
% 2.84/1.00      | ~ v1_relat_1(X2)
% 2.84/1.00      | X2 != X0
% 2.84/1.00      | k1_relat_1(X2) != X1
% 2.84/1.00      | k2_relat_1(X2) != k1_xboole_0
% 2.84/1.00      | k1_xboole_0 = X1
% 2.84/1.00      | k1_xboole_0 = X0 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_463,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0)
% 2.84/1.00      | k2_relat_1(X0) != k1_xboole_0
% 2.84/1.00      | k1_xboole_0 = X0
% 2.84/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_462]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_479,plain,
% 2.84/1.00      ( ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0)
% 2.84/1.00      | k2_relat_1(X0) != k1_xboole_0
% 2.84/1.00      | k1_xboole_0 = X0
% 2.84/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.84/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_463,c_367]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1327,plain,
% 2.84/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 2.84/1.00      | k1_xboole_0 = X0
% 2.84/1.00      | k1_xboole_0 = k1_relat_1(X0)
% 2.84/1.00      | v1_funct_1(X0) != iProver_top
% 2.84/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3375,plain,
% 2.84/1.00      ( k1_relat_1(sK2) = k1_xboole_0
% 2.84/1.00      | sK1 != k1_xboole_0
% 2.84/1.00      | sK2 = k1_xboole_0
% 2.84/1.00      | v1_funct_1(sK2) != iProver_top
% 2.84/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_2557,c_1327]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_11,plain,
% 2.84/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.84/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_5,plain,
% 2.84/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.84/1.00      | k1_xboole_0 = X1
% 2.84/1.00      | k1_xboole_0 = X0 ),
% 2.84/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_105,plain,
% 2.84/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.84/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4,plain,
% 2.84/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.84/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_106,plain,
% 2.84/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_795,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1811,plain,
% 2.84/1.00      ( k1_relat_1(sK2) != X0
% 2.84/1.00      | k1_relat_1(sK2) = k1_xboole_0
% 2.84/1.00      | k1_xboole_0 != X0 ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_795]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2045,plain,
% 2.84/1.00      ( k1_relat_1(sK2) != k1_relat_1(X0)
% 2.84/1.00      | k1_relat_1(sK2) = k1_xboole_0
% 2.84/1.00      | k1_xboole_0 != k1_relat_1(X0) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_1811]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2047,plain,
% 2.84/1.00      ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
% 2.84/1.00      | k1_relat_1(sK2) = k1_xboole_0
% 2.84/1.00      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_2045]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_802,plain,
% 2.84/1.00      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 2.84/1.00      theory(equality) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2046,plain,
% 2.84/1.00      ( k1_relat_1(sK2) = k1_relat_1(X0) | sK2 != X0 ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_802]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2048,plain,
% 2.84/1.00      ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_2046]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3035,plain,
% 2.84/1.00      ( k1_relat_1(X0) != X1
% 2.84/1.00      | k1_xboole_0 != X1
% 2.84/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_795]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3036,plain,
% 2.84/1.00      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.84/1.00      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 2.84/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.84/1.00      inference(instantiation,[status(thm)],[c_3035]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3398,plain,
% 2.84/1.00      ( ~ v1_funct_1(sK2)
% 2.84/1.00      | ~ v1_relat_1(sK2)
% 2.84/1.00      | k1_relat_1(sK2) = k1_xboole_0
% 2.84/1.00      | sK1 != k1_xboole_0
% 2.84/1.00      | sK2 = k1_xboole_0 ),
% 2.84/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3375]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3880,plain,
% 2.84/1.00      ( sK1 != k1_xboole_0 | k1_relat_1(sK2) = k1_xboole_0 ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_3375,c_37,c_35,c_11,c_105,c_106,c_1663,c_2047,c_2048,
% 2.84/1.00                 c_3036,c_3398]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3881,plain,
% 2.84/1.00      ( k1_relat_1(sK2) = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 2.84/1.00      inference(renaming,[status(thm)],[c_3880]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_25,plain,
% 2.84/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.84/1.00      | k1_xboole_0 = X2 ),
% 2.84/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_36,negated_conjecture,
% 2.84/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.84/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_658,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.84/1.00      | sK0 != X1
% 2.84/1.00      | sK1 != X2
% 2.84/1.00      | sK2 != X0
% 2.84/1.00      | k1_xboole_0 = X2 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_659,plain,
% 2.84/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.84/1.00      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.84/1.00      | k1_xboole_0 = sK1 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_658]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_661,plain,
% 2.84/1.00      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_659,c_35]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_18,plain,
% 2.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1336,plain,
% 2.84/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.84/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2792,plain,
% 2.84/1.00      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_1333,c_1336]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2883,plain,
% 2.84/1.00      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_661,c_2792]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_32,negated_conjecture,
% 2.84/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.84/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.84/1.00      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.84/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_669,plain,
% 2.84/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.84/1.00      | ~ v1_relat_1(X0)
% 2.84/1.00      | k2_funct_1(sK2) != X0
% 2.84/1.00      | k1_relat_1(X0) != sK1
% 2.84/1.00      | k2_relat_1(X0) != sK0 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_670,plain,
% 2.84/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.84/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.84/1.00      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.84/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_669]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_682,plain,
% 2.84/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.84/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.84/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.84/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_670,c_17]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1318,plain,
% 2.84/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.84/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_671,plain,
% 2.84/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.84/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.84/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1927,plain,
% 2.84/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.84/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_1318,c_38,c_40,c_671,c_1644,c_1647,c_1664]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1928,plain,
% 2.84/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.84/1.00      inference(renaming,[status(thm)],[c_1927]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1931,plain,
% 2.84/1.00      ( k1_relat_1(sK2) != sK0
% 2.84/1.00      | k2_relat_1(sK2) != sK1
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.84/1.00      inference(light_normalisation,[status(thm)],[c_1928,c_1668,c_1672]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2569,plain,
% 2.84/1.00      ( k1_relat_1(sK2) != sK0
% 2.84/1.00      | sK1 != sK1
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.84/1.00      inference(demodulation,[status(thm)],[c_2557,c_1931]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_2579,plain,
% 2.84/1.00      ( k1_relat_1(sK2) != sK0
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.84/1.00      inference(equality_resolution_simp,[status(thm)],[c_2569]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3366,plain,
% 2.84/1.00      ( sK1 = k1_xboole_0
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_2883,c_2579]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_30,plain,
% 2.84/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.84/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_348,plain,
% 2.84/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0)
% 2.84/1.00      | X1 != X2
% 2.84/1.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_30]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_349,plain,
% 2.84/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0)
% 2.84/1.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_348]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_688,plain,
% 2.84/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.84/1.00      | ~ v1_relat_1(X0)
% 2.84/1.00      | k2_funct_1(sK2) != X0
% 2.84/1.00      | k1_relat_1(X0) != sK1
% 2.84/1.00      | k2_relat_1(X0) != k1_xboole_0
% 2.84/1.00      | sK0 != X1 ),
% 2.84/1.00      inference(resolution_lifted,[status(thm)],[c_349,c_32]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_689,plain,
% 2.84/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.84/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.84/1.00      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.84/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.84/1.00      inference(unflattening,[status(thm)],[c_688]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_701,plain,
% 2.84/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.84/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.84/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.84/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_689,c_17]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1317,plain,
% 2.84/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.84/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_690,plain,
% 2.84/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.84/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.84/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1743,plain,
% 2.84/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.84/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_1317,c_38,c_40,c_690,c_1644,c_1647,c_1664]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1744,plain,
% 2.84/1.00      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.84/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.84/1.00      inference(renaming,[status(thm)],[c_1743]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1747,plain,
% 2.84/1.00      ( k1_relat_1(sK2) != k1_xboole_0
% 2.84/1.00      | k2_relat_1(sK2) != sK1
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.84/1.00      inference(light_normalisation,[status(thm)],[c_1744,c_1668,c_1672]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_3885,plain,
% 2.84/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_3366,c_1747,c_2557,c_3881]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_26,plain,
% 2.84/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.84/1.00      | ~ v1_funct_1(X0)
% 2.84/1.00      | ~ v1_relat_1(X0) ),
% 2.84/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_1334,plain,
% 2.84/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.84/1.00      | v1_funct_1(X0) != iProver_top
% 2.84/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.84/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4153,plain,
% 2.84/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 2.84/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.84/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_1668,c_1334]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4182,plain,
% 2.84/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.84/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.84/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.84/1.00      inference(light_normalisation,[status(thm)],[c_4153,c_2571]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4723,plain,
% 2.84/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_4182,c_38,c_40,c_1644,c_1647,c_1664]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_4728,plain,
% 2.84/1.00      ( sK1 = k1_xboole_0
% 2.84/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_2883,c_4723]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_5223,plain,
% 2.84/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
% 2.84/1.00      inference(global_propositional_subsumption,
% 2.84/1.00                [status(thm)],
% 2.84/1.00                [c_4036,c_37,c_38,c_35,c_40,c_11,c_105,c_106,c_1644,c_1647,
% 2.84/1.00                 c_1663,c_1664,c_1747,c_2047,c_2048,c_2557,c_3036,c_3366,
% 2.84/1.00                 c_3398,c_3881,c_4728]) ).
% 2.84/1.00  
% 2.84/1.00  cnf(c_5237,plain,
% 2.84/1.00      ( $false ),
% 2.84/1.00      inference(superposition,[status(thm)],[c_5223,c_3885]) ).
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.84/1.00  
% 2.84/1.00  ------                               Statistics
% 2.84/1.00  
% 2.84/1.00  ------ General
% 2.84/1.00  
% 2.84/1.00  abstr_ref_over_cycles:                  0
% 2.84/1.00  abstr_ref_under_cycles:                 0
% 2.84/1.00  gc_basic_clause_elim:                   0
% 2.84/1.00  forced_gc_time:                         0
% 2.84/1.00  parsing_time:                           0.009
% 2.84/1.00  unif_index_cands_time:                  0.
% 2.84/1.00  unif_index_add_time:                    0.
% 2.84/1.00  orderings_time:                         0.
% 2.84/1.00  out_proof_time:                         0.011
% 2.84/1.00  total_time:                             0.172
% 2.84/1.00  num_of_symbols:                         49
% 2.84/1.00  num_of_terms:                           2925
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing
% 2.84/1.00  
% 2.84/1.00  num_of_splits:                          0
% 2.84/1.00  num_of_split_atoms:                     0
% 2.84/1.00  num_of_reused_defs:                     0
% 2.84/1.00  num_eq_ax_congr_red:                    3
% 2.84/1.00  num_of_sem_filtered_clauses:            1
% 2.84/1.00  num_of_subtypes:                        0
% 2.84/1.00  monotx_restored_types:                  0
% 2.84/1.00  sat_num_of_epr_types:                   0
% 2.84/1.00  sat_num_of_non_cyclic_types:            0
% 2.84/1.00  sat_guarded_non_collapsed_types:        0
% 2.84/1.00  num_pure_diseq_elim:                    0
% 2.84/1.00  simp_replaced_by:                       0
% 2.84/1.00  res_preprocessed:                       139
% 2.84/1.00  prep_upred:                             0
% 2.84/1.00  prep_unflattend:                        55
% 2.84/1.00  smt_new_axioms:                         0
% 2.84/1.00  pred_elim_cands:                        7
% 2.84/1.00  pred_elim:                              3
% 2.84/1.00  pred_elim_cl:                           -2
% 2.84/1.00  pred_elim_cycles:                       4
% 2.84/1.00  merged_defs:                            0
% 2.84/1.00  merged_defs_ncl:                        0
% 2.84/1.00  bin_hyper_res:                          0
% 2.84/1.00  prep_cycles:                            3
% 2.84/1.00  pred_elim_time:                         0.023
% 2.84/1.00  splitting_time:                         0.
% 2.84/1.00  sem_filter_time:                        0.
% 2.84/1.00  monotx_time:                            0.
% 2.84/1.00  subtype_inf_time:                       0.
% 2.84/1.00  
% 2.84/1.00  ------ Problem properties
% 2.84/1.00  
% 2.84/1.00  clauses:                                38
% 2.84/1.00  conjectures:                            3
% 2.84/1.00  epr:                                    3
% 2.84/1.00  horn:                                   32
% 2.84/1.00  ground:                                 17
% 2.84/1.00  unary:                                  10
% 2.84/1.00  binary:                                 6
% 2.84/1.00  lits:                                   107
% 2.84/1.00  lits_eq:                                47
% 2.84/1.00  fd_pure:                                0
% 2.84/1.00  fd_pseudo:                              0
% 2.84/1.00  fd_cond:                                3
% 2.84/1.00  fd_pseudo_cond:                         1
% 2.84/1.00  ac_symbols:                             0
% 2.84/1.00  
% 2.84/1.00  ------ Propositional Solver
% 2.84/1.00  
% 2.84/1.00  prop_solver_calls:                      23
% 2.84/1.00  prop_fast_solver_calls:                 1107
% 2.84/1.00  smt_solver_calls:                       0
% 2.84/1.00  smt_fast_solver_calls:                  0
% 2.84/1.00  prop_num_of_clauses:                    1768
% 2.84/1.00  prop_preprocess_simplified:             5805
% 2.84/1.00  prop_fo_subsumed:                       43
% 2.84/1.00  prop_solver_time:                       0.
% 2.84/1.00  smt_solver_time:                        0.
% 2.84/1.00  smt_fast_solver_time:                   0.
% 2.84/1.00  prop_fast_solver_time:                  0.
% 2.84/1.00  prop_unsat_core_time:                   0.
% 2.84/1.00  
% 2.84/1.00  ------ QBF
% 2.84/1.00  
% 2.84/1.00  qbf_q_res:                              0
% 2.84/1.00  qbf_num_tautologies:                    0
% 2.84/1.00  qbf_prep_cycles:                        0
% 2.84/1.00  
% 2.84/1.00  ------ BMC1
% 2.84/1.00  
% 2.84/1.00  bmc1_current_bound:                     -1
% 2.84/1.00  bmc1_last_solved_bound:                 -1
% 2.84/1.00  bmc1_unsat_core_size:                   -1
% 2.84/1.00  bmc1_unsat_core_parents_size:           -1
% 2.84/1.00  bmc1_merge_next_fun:                    0
% 2.84/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.84/1.00  
% 2.84/1.00  ------ Instantiation
% 2.84/1.00  
% 2.84/1.00  inst_num_of_clauses:                    648
% 2.84/1.00  inst_num_in_passive:                    123
% 2.84/1.00  inst_num_in_active:                     309
% 2.84/1.00  inst_num_in_unprocessed:                216
% 2.84/1.00  inst_num_of_loops:                      390
% 2.84/1.00  inst_num_of_learning_restarts:          0
% 2.84/1.00  inst_num_moves_active_passive:          79
% 2.84/1.00  inst_lit_activity:                      0
% 2.84/1.00  inst_lit_activity_moves:                0
% 2.84/1.00  inst_num_tautologies:                   0
% 2.84/1.00  inst_num_prop_implied:                  0
% 2.84/1.00  inst_num_existing_simplified:           0
% 2.84/1.00  inst_num_eq_res_simplified:             0
% 2.84/1.00  inst_num_child_elim:                    0
% 2.84/1.00  inst_num_of_dismatching_blockings:      124
% 2.84/1.00  inst_num_of_non_proper_insts:           599
% 2.84/1.00  inst_num_of_duplicates:                 0
% 2.84/1.00  inst_inst_num_from_inst_to_res:         0
% 2.84/1.00  inst_dismatching_checking_time:         0.
% 2.84/1.00  
% 2.84/1.00  ------ Resolution
% 2.84/1.00  
% 2.84/1.00  res_num_of_clauses:                     0
% 2.84/1.00  res_num_in_passive:                     0
% 2.84/1.00  res_num_in_active:                      0
% 2.84/1.00  res_num_of_loops:                       142
% 2.84/1.00  res_forward_subset_subsumed:            26
% 2.84/1.00  res_backward_subset_subsumed:           0
% 2.84/1.00  res_forward_subsumed:                   0
% 2.84/1.00  res_backward_subsumed:                  0
% 2.84/1.00  res_forward_subsumption_resolution:     6
% 2.84/1.00  res_backward_subsumption_resolution:    0
% 2.84/1.00  res_clause_to_clause_subsumption:       167
% 2.84/1.00  res_orphan_elimination:                 0
% 2.84/1.00  res_tautology_del:                      45
% 2.84/1.00  res_num_eq_res_simplified:              0
% 2.84/1.00  res_num_sel_changes:                    0
% 2.84/1.00  res_moves_from_active_to_pass:          0
% 2.84/1.00  
% 2.84/1.00  ------ Superposition
% 2.84/1.00  
% 2.84/1.00  sup_time_total:                         0.
% 2.84/1.00  sup_time_generating:                    0.
% 2.84/1.00  sup_time_sim_full:                      0.
% 2.84/1.00  sup_time_sim_immed:                     0.
% 2.84/1.00  
% 2.84/1.00  sup_num_of_clauses:                     85
% 2.84/1.00  sup_num_in_active:                      72
% 2.84/1.00  sup_num_in_passive:                     13
% 2.84/1.00  sup_num_of_loops:                       76
% 2.84/1.00  sup_fw_superposition:                   66
% 2.84/1.00  sup_bw_superposition:                   27
% 2.84/1.00  sup_immediate_simplified:               38
% 2.84/1.00  sup_given_eliminated:                   0
% 2.84/1.00  comparisons_done:                       0
% 2.84/1.00  comparisons_avoided:                    10
% 2.84/1.00  
% 2.84/1.00  ------ Simplifications
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  sim_fw_subset_subsumed:                 12
% 2.84/1.00  sim_bw_subset_subsumed:                 1
% 2.84/1.00  sim_fw_subsumed:                        9
% 2.84/1.00  sim_bw_subsumed:                        0
% 2.84/1.00  sim_fw_subsumption_res:                 0
% 2.84/1.00  sim_bw_subsumption_res:                 0
% 2.84/1.00  sim_tautology_del:                      3
% 2.84/1.00  sim_eq_tautology_del:                   5
% 2.84/1.00  sim_eq_res_simp:                        3
% 2.84/1.00  sim_fw_demodulated:                     11
% 2.84/1.00  sim_bw_demodulated:                     4
% 2.84/1.00  sim_light_normalised:                   28
% 2.84/1.00  sim_joinable_taut:                      0
% 2.84/1.00  sim_joinable_simp:                      0
% 2.84/1.00  sim_ac_normalised:                      0
% 2.84/1.00  sim_smt_subsumption:                    0
% 2.84/1.00  
%------------------------------------------------------------------------------

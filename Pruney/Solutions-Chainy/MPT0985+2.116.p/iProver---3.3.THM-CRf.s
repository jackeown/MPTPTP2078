%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:43 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  167 (4804 expanded)
%              Number of clauses        :  108 (1477 expanded)
%              Number of leaves         :   13 ( 935 expanded)
%              Depth                    :   24
%              Number of atoms          :  500 (26235 expanded)
%              Number of equality atoms :  255 (5230 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f34,plain,(
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

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f42])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

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

fof(f57,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
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

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f48])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f49])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1646,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1649,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3608,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1646,c_1649])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_624,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_626,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_31])).

cnf(c_3745,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3608,c_626])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1648,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2957,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1646,c_1648])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2969,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2957,c_29])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_393,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_394,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_396,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_33])).

cnf(c_1644,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1922,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1930,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1644,c_33,c_31,c_394,c_1922])).

cnf(c_2994,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2969,c_1930])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1647,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3129,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2994,c_1647])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_407,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_408,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_410,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_33])).

cnf(c_1643,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_1926,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1643,c_33,c_31,c_408,c_1922])).

cnf(c_3130,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3129,c_1926])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1901,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1902,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1901])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1904,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1905,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1904])).

cnf(c_1923,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1922])).

cnf(c_3388,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3130,c_34,c_36,c_1902,c_1905,c_1923])).

cnf(c_3830,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3745,c_3388])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_28,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_634,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k2_relat_1(X0) != sK0
    | k1_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_635,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_647,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_635,c_15])).

cnf(c_1633,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_636,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_1996,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1633,c_34,c_36,c_636,c_1902,c_1905,c_1923])).

cnf(c_1997,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1996])).

cnf(c_2000,plain,
    ( k2_relat_1(sK2) != sK1
    | k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1997,c_1926,c_1930])).

cnf(c_2993,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2969,c_2000])).

cnf(c_2997,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2993])).

cnf(c_3831,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3745,c_2997])).

cnf(c_3846,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3830,c_3831])).

cnf(c_4289,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3846,c_3388])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4367,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4289,c_4])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_552,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_1637,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_1826,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1637,c_4])).

cnf(c_2212,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1826,c_34,c_36,c_1902,c_1923])).

cnf(c_2213,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2212])).

cnf(c_4299,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3846,c_2213])).

cnf(c_4332,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4299])).

cnf(c_4336,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4332,c_4])).

cnf(c_4370,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4367,c_4336])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1655,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2352,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1646,c_1655])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1659,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4058,plain,
    ( k2_zfmisc_1(sK0,sK1) = sK2
    | r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2352,c_1659])).

cnf(c_4284,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) = sK2
    | r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3846,c_4058])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4390,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4284,c_3])).

cnf(c_2246,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2247,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2246])).

cnf(c_2249,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2247])).

cnf(c_2257,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2258,plain,
    ( sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2257])).

cnf(c_2260,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2795,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2798,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2795])).

cnf(c_3555,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3556,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3555])).

cnf(c_3558,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3556])).

cnf(c_4305,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3846,c_1646])).

cnf(c_4310,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4305,c_3])).

cnf(c_5098,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4390,c_2249,c_2260,c_2798,c_3558,c_4310])).

cnf(c_8107,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4370,c_5098])).

cnf(c_3612,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1649])).

cnf(c_4908,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4367,c_3612])).

cnf(c_4295,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3846,c_2994])).

cnf(c_4928,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4908,c_4295])).

cnf(c_6864,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4928,c_5098])).

cnf(c_8108,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8107,c_6864])).

cnf(c_8109,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8108])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.79/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.00  
% 2.79/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/1.00  
% 2.79/1.00  ------  iProver source info
% 2.79/1.00  
% 2.79/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.79/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/1.00  git: non_committed_changes: false
% 2.79/1.00  git: last_make_outside_of_git: false
% 2.79/1.00  
% 2.79/1.00  ------ 
% 2.79/1.00  
% 2.79/1.00  ------ Input Options
% 2.79/1.00  
% 2.79/1.00  --out_options                           all
% 2.79/1.00  --tptp_safe_out                         true
% 2.79/1.00  --problem_path                          ""
% 2.79/1.00  --include_path                          ""
% 2.79/1.00  --clausifier                            res/vclausify_rel
% 2.79/1.00  --clausifier_options                    --mode clausify
% 2.79/1.00  --stdin                                 false
% 2.79/1.00  --stats_out                             all
% 2.79/1.00  
% 2.79/1.00  ------ General Options
% 2.79/1.00  
% 2.79/1.00  --fof                                   false
% 2.79/1.00  --time_out_real                         305.
% 2.79/1.00  --time_out_virtual                      -1.
% 2.79/1.00  --symbol_type_check                     false
% 2.79/1.00  --clausify_out                          false
% 2.79/1.00  --sig_cnt_out                           false
% 2.79/1.00  --trig_cnt_out                          false
% 2.79/1.00  --trig_cnt_out_tolerance                1.
% 2.79/1.00  --trig_cnt_out_sk_spl                   false
% 2.79/1.00  --abstr_cl_out                          false
% 2.79/1.00  
% 2.79/1.00  ------ Global Options
% 2.79/1.00  
% 2.79/1.00  --schedule                              default
% 2.79/1.00  --add_important_lit                     false
% 2.79/1.00  --prop_solver_per_cl                    1000
% 2.79/1.00  --min_unsat_core                        false
% 2.79/1.00  --soft_assumptions                      false
% 2.79/1.00  --soft_lemma_size                       3
% 2.79/1.00  --prop_impl_unit_size                   0
% 2.79/1.00  --prop_impl_unit                        []
% 2.79/1.00  --share_sel_clauses                     true
% 2.79/1.00  --reset_solvers                         false
% 2.79/1.00  --bc_imp_inh                            [conj_cone]
% 2.79/1.00  --conj_cone_tolerance                   3.
% 2.79/1.00  --extra_neg_conj                        none
% 2.79/1.00  --large_theory_mode                     true
% 2.79/1.00  --prolific_symb_bound                   200
% 2.79/1.00  --lt_threshold                          2000
% 2.79/1.00  --clause_weak_htbl                      true
% 2.79/1.00  --gc_record_bc_elim                     false
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing Options
% 2.79/1.00  
% 2.79/1.00  --preprocessing_flag                    true
% 2.79/1.00  --time_out_prep_mult                    0.1
% 2.79/1.00  --splitting_mode                        input
% 2.79/1.00  --splitting_grd                         true
% 2.79/1.00  --splitting_cvd                         false
% 2.79/1.00  --splitting_cvd_svl                     false
% 2.79/1.00  --splitting_nvd                         32
% 2.79/1.00  --sub_typing                            true
% 2.79/1.00  --prep_gs_sim                           true
% 2.79/1.00  --prep_unflatten                        true
% 2.79/1.00  --prep_res_sim                          true
% 2.79/1.00  --prep_upred                            true
% 2.79/1.00  --prep_sem_filter                       exhaustive
% 2.79/1.00  --prep_sem_filter_out                   false
% 2.79/1.00  --pred_elim                             true
% 2.79/1.00  --res_sim_input                         true
% 2.79/1.00  --eq_ax_congr_red                       true
% 2.79/1.00  --pure_diseq_elim                       true
% 2.79/1.00  --brand_transform                       false
% 2.79/1.00  --non_eq_to_eq                          false
% 2.79/1.00  --prep_def_merge                        true
% 2.79/1.00  --prep_def_merge_prop_impl              false
% 2.79/1.00  --prep_def_merge_mbd                    true
% 2.79/1.00  --prep_def_merge_tr_red                 false
% 2.79/1.00  --prep_def_merge_tr_cl                  false
% 2.79/1.00  --smt_preprocessing                     true
% 2.79/1.00  --smt_ac_axioms                         fast
% 2.79/1.00  --preprocessed_out                      false
% 2.79/1.00  --preprocessed_stats                    false
% 2.79/1.00  
% 2.79/1.00  ------ Abstraction refinement Options
% 2.79/1.00  
% 2.79/1.00  --abstr_ref                             []
% 2.79/1.00  --abstr_ref_prep                        false
% 2.79/1.00  --abstr_ref_until_sat                   false
% 2.79/1.00  --abstr_ref_sig_restrict                funpre
% 2.79/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/1.00  --abstr_ref_under                       []
% 2.79/1.00  
% 2.79/1.00  ------ SAT Options
% 2.79/1.00  
% 2.79/1.00  --sat_mode                              false
% 2.79/1.00  --sat_fm_restart_options                ""
% 2.79/1.00  --sat_gr_def                            false
% 2.79/1.00  --sat_epr_types                         true
% 2.79/1.00  --sat_non_cyclic_types                  false
% 2.79/1.00  --sat_finite_models                     false
% 2.79/1.00  --sat_fm_lemmas                         false
% 2.79/1.00  --sat_fm_prep                           false
% 2.79/1.00  --sat_fm_uc_incr                        true
% 2.79/1.00  --sat_out_model                         small
% 2.79/1.00  --sat_out_clauses                       false
% 2.79/1.00  
% 2.79/1.00  ------ QBF Options
% 2.79/1.00  
% 2.79/1.00  --qbf_mode                              false
% 2.79/1.00  --qbf_elim_univ                         false
% 2.79/1.00  --qbf_dom_inst                          none
% 2.79/1.00  --qbf_dom_pre_inst                      false
% 2.79/1.00  --qbf_sk_in                             false
% 2.79/1.00  --qbf_pred_elim                         true
% 2.79/1.00  --qbf_split                             512
% 2.79/1.00  
% 2.79/1.00  ------ BMC1 Options
% 2.79/1.00  
% 2.79/1.00  --bmc1_incremental                      false
% 2.79/1.00  --bmc1_axioms                           reachable_all
% 2.79/1.00  --bmc1_min_bound                        0
% 2.79/1.00  --bmc1_max_bound                        -1
% 2.79/1.00  --bmc1_max_bound_default                -1
% 2.79/1.00  --bmc1_symbol_reachability              true
% 2.79/1.00  --bmc1_property_lemmas                  false
% 2.79/1.00  --bmc1_k_induction                      false
% 2.79/1.00  --bmc1_non_equiv_states                 false
% 2.79/1.00  --bmc1_deadlock                         false
% 2.79/1.00  --bmc1_ucm                              false
% 2.79/1.00  --bmc1_add_unsat_core                   none
% 2.79/1.00  --bmc1_unsat_core_children              false
% 2.79/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/1.00  --bmc1_out_stat                         full
% 2.79/1.00  --bmc1_ground_init                      false
% 2.79/1.00  --bmc1_pre_inst_next_state              false
% 2.79/1.00  --bmc1_pre_inst_state                   false
% 2.79/1.00  --bmc1_pre_inst_reach_state             false
% 2.79/1.00  --bmc1_out_unsat_core                   false
% 2.79/1.00  --bmc1_aig_witness_out                  false
% 2.79/1.00  --bmc1_verbose                          false
% 2.79/1.00  --bmc1_dump_clauses_tptp                false
% 2.79/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.79/1.00  --bmc1_dump_file                        -
% 2.79/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.79/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.79/1.00  --bmc1_ucm_extend_mode                  1
% 2.79/1.00  --bmc1_ucm_init_mode                    2
% 2.79/1.00  --bmc1_ucm_cone_mode                    none
% 2.79/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.79/1.00  --bmc1_ucm_relax_model                  4
% 2.79/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.79/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/1.00  --bmc1_ucm_layered_model                none
% 2.79/1.00  --bmc1_ucm_max_lemma_size               10
% 2.79/1.00  
% 2.79/1.00  ------ AIG Options
% 2.79/1.00  
% 2.79/1.00  --aig_mode                              false
% 2.79/1.00  
% 2.79/1.00  ------ Instantiation Options
% 2.79/1.00  
% 2.79/1.00  --instantiation_flag                    true
% 2.79/1.00  --inst_sos_flag                         false
% 2.79/1.00  --inst_sos_phase                        true
% 2.79/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/1.00  --inst_lit_sel_side                     num_symb
% 2.79/1.00  --inst_solver_per_active                1400
% 2.79/1.00  --inst_solver_calls_frac                1.
% 2.79/1.00  --inst_passive_queue_type               priority_queues
% 2.79/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/1.00  --inst_passive_queues_freq              [25;2]
% 2.79/1.00  --inst_dismatching                      true
% 2.79/1.00  --inst_eager_unprocessed_to_passive     true
% 2.79/1.00  --inst_prop_sim_given                   true
% 2.79/1.00  --inst_prop_sim_new                     false
% 2.79/1.00  --inst_subs_new                         false
% 2.79/1.00  --inst_eq_res_simp                      false
% 2.79/1.00  --inst_subs_given                       false
% 2.79/1.00  --inst_orphan_elimination               true
% 2.79/1.00  --inst_learning_loop_flag               true
% 2.79/1.00  --inst_learning_start                   3000
% 2.79/1.00  --inst_learning_factor                  2
% 2.79/1.00  --inst_start_prop_sim_after_learn       3
% 2.79/1.00  --inst_sel_renew                        solver
% 2.79/1.00  --inst_lit_activity_flag                true
% 2.79/1.00  --inst_restr_to_given                   false
% 2.79/1.00  --inst_activity_threshold               500
% 2.79/1.00  --inst_out_proof                        true
% 2.79/1.00  
% 2.79/1.00  ------ Resolution Options
% 2.79/1.00  
% 2.79/1.00  --resolution_flag                       true
% 2.79/1.00  --res_lit_sel                           adaptive
% 2.79/1.00  --res_lit_sel_side                      none
% 2.79/1.00  --res_ordering                          kbo
% 2.79/1.00  --res_to_prop_solver                    active
% 2.79/1.00  --res_prop_simpl_new                    false
% 2.79/1.00  --res_prop_simpl_given                  true
% 2.79/1.00  --res_passive_queue_type                priority_queues
% 2.79/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/1.00  --res_passive_queues_freq               [15;5]
% 2.79/1.00  --res_forward_subs                      full
% 2.79/1.00  --res_backward_subs                     full
% 2.79/1.00  --res_forward_subs_resolution           true
% 2.79/1.00  --res_backward_subs_resolution          true
% 2.79/1.00  --res_orphan_elimination                true
% 2.79/1.00  --res_time_limit                        2.
% 2.79/1.00  --res_out_proof                         true
% 2.79/1.00  
% 2.79/1.00  ------ Superposition Options
% 2.79/1.00  
% 2.79/1.00  --superposition_flag                    true
% 2.79/1.00  --sup_passive_queue_type                priority_queues
% 2.79/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.79/1.00  --demod_completeness_check              fast
% 2.79/1.00  --demod_use_ground                      true
% 2.79/1.00  --sup_to_prop_solver                    passive
% 2.79/1.00  --sup_prop_simpl_new                    true
% 2.79/1.00  --sup_prop_simpl_given                  true
% 2.79/1.00  --sup_fun_splitting                     false
% 2.79/1.00  --sup_smt_interval                      50000
% 2.79/1.00  
% 2.79/1.00  ------ Superposition Simplification Setup
% 2.79/1.00  
% 2.79/1.00  --sup_indices_passive                   []
% 2.79/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_full_bw                           [BwDemod]
% 2.79/1.00  --sup_immed_triv                        [TrivRules]
% 2.79/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_immed_bw_main                     []
% 2.79/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.00  
% 2.79/1.00  ------ Combination Options
% 2.79/1.00  
% 2.79/1.00  --comb_res_mult                         3
% 2.79/1.00  --comb_sup_mult                         2
% 2.79/1.00  --comb_inst_mult                        10
% 2.79/1.00  
% 2.79/1.00  ------ Debug Options
% 2.79/1.00  
% 2.79/1.00  --dbg_backtrace                         false
% 2.79/1.00  --dbg_dump_prop_clauses                 false
% 2.79/1.00  --dbg_dump_prop_clauses_file            -
% 2.79/1.00  --dbg_out_stat                          false
% 2.79/1.00  ------ Parsing...
% 2.79/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.79/1.00  ------ Proving...
% 2.79/1.00  ------ Problem Properties 
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  clauses                                 33
% 2.79/1.00  conjectures                             3
% 2.79/1.00  EPR                                     3
% 2.79/1.00  Horn                                    28
% 2.79/1.00  unary                                   7
% 2.79/1.00  binary                                  11
% 2.79/1.00  lits                                    86
% 2.79/1.00  lits eq                                 38
% 2.79/1.00  fd_pure                                 0
% 2.79/1.00  fd_pseudo                               0
% 2.79/1.00  fd_cond                                 2
% 2.79/1.00  fd_pseudo_cond                          1
% 2.79/1.00  AC symbols                              0
% 2.79/1.00  
% 2.79/1.00  ------ Schedule dynamic 5 is on 
% 2.79/1.00  
% 2.79/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  ------ 
% 2.79/1.00  Current options:
% 2.79/1.00  ------ 
% 2.79/1.00  
% 2.79/1.00  ------ Input Options
% 2.79/1.00  
% 2.79/1.00  --out_options                           all
% 2.79/1.00  --tptp_safe_out                         true
% 2.79/1.00  --problem_path                          ""
% 2.79/1.00  --include_path                          ""
% 2.79/1.00  --clausifier                            res/vclausify_rel
% 2.79/1.00  --clausifier_options                    --mode clausify
% 2.79/1.00  --stdin                                 false
% 2.79/1.00  --stats_out                             all
% 2.79/1.00  
% 2.79/1.00  ------ General Options
% 2.79/1.00  
% 2.79/1.00  --fof                                   false
% 2.79/1.00  --time_out_real                         305.
% 2.79/1.00  --time_out_virtual                      -1.
% 2.79/1.00  --symbol_type_check                     false
% 2.79/1.00  --clausify_out                          false
% 2.79/1.00  --sig_cnt_out                           false
% 2.79/1.00  --trig_cnt_out                          false
% 2.79/1.00  --trig_cnt_out_tolerance                1.
% 2.79/1.00  --trig_cnt_out_sk_spl                   false
% 2.79/1.00  --abstr_cl_out                          false
% 2.79/1.00  
% 2.79/1.00  ------ Global Options
% 2.79/1.00  
% 2.79/1.00  --schedule                              default
% 2.79/1.00  --add_important_lit                     false
% 2.79/1.00  --prop_solver_per_cl                    1000
% 2.79/1.00  --min_unsat_core                        false
% 2.79/1.00  --soft_assumptions                      false
% 2.79/1.00  --soft_lemma_size                       3
% 2.79/1.00  --prop_impl_unit_size                   0
% 2.79/1.00  --prop_impl_unit                        []
% 2.79/1.00  --share_sel_clauses                     true
% 2.79/1.00  --reset_solvers                         false
% 2.79/1.00  --bc_imp_inh                            [conj_cone]
% 2.79/1.00  --conj_cone_tolerance                   3.
% 2.79/1.00  --extra_neg_conj                        none
% 2.79/1.00  --large_theory_mode                     true
% 2.79/1.00  --prolific_symb_bound                   200
% 2.79/1.00  --lt_threshold                          2000
% 2.79/1.00  --clause_weak_htbl                      true
% 2.79/1.00  --gc_record_bc_elim                     false
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing Options
% 2.79/1.00  
% 2.79/1.00  --preprocessing_flag                    true
% 2.79/1.00  --time_out_prep_mult                    0.1
% 2.79/1.00  --splitting_mode                        input
% 2.79/1.00  --splitting_grd                         true
% 2.79/1.00  --splitting_cvd                         false
% 2.79/1.00  --splitting_cvd_svl                     false
% 2.79/1.00  --splitting_nvd                         32
% 2.79/1.00  --sub_typing                            true
% 2.79/1.00  --prep_gs_sim                           true
% 2.79/1.00  --prep_unflatten                        true
% 2.79/1.00  --prep_res_sim                          true
% 2.79/1.00  --prep_upred                            true
% 2.79/1.00  --prep_sem_filter                       exhaustive
% 2.79/1.00  --prep_sem_filter_out                   false
% 2.79/1.00  --pred_elim                             true
% 2.79/1.00  --res_sim_input                         true
% 2.79/1.00  --eq_ax_congr_red                       true
% 2.79/1.00  --pure_diseq_elim                       true
% 2.79/1.00  --brand_transform                       false
% 2.79/1.00  --non_eq_to_eq                          false
% 2.79/1.00  --prep_def_merge                        true
% 2.79/1.00  --prep_def_merge_prop_impl              false
% 2.79/1.00  --prep_def_merge_mbd                    true
% 2.79/1.00  --prep_def_merge_tr_red                 false
% 2.79/1.00  --prep_def_merge_tr_cl                  false
% 2.79/1.00  --smt_preprocessing                     true
% 2.79/1.00  --smt_ac_axioms                         fast
% 2.79/1.00  --preprocessed_out                      false
% 2.79/1.00  --preprocessed_stats                    false
% 2.79/1.00  
% 2.79/1.00  ------ Abstraction refinement Options
% 2.79/1.00  
% 2.79/1.00  --abstr_ref                             []
% 2.79/1.00  --abstr_ref_prep                        false
% 2.79/1.00  --abstr_ref_until_sat                   false
% 2.79/1.00  --abstr_ref_sig_restrict                funpre
% 2.79/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/1.00  --abstr_ref_under                       []
% 2.79/1.00  
% 2.79/1.00  ------ SAT Options
% 2.79/1.00  
% 2.79/1.00  --sat_mode                              false
% 2.79/1.00  --sat_fm_restart_options                ""
% 2.79/1.00  --sat_gr_def                            false
% 2.79/1.00  --sat_epr_types                         true
% 2.79/1.00  --sat_non_cyclic_types                  false
% 2.79/1.00  --sat_finite_models                     false
% 2.79/1.00  --sat_fm_lemmas                         false
% 2.79/1.00  --sat_fm_prep                           false
% 2.79/1.00  --sat_fm_uc_incr                        true
% 2.79/1.00  --sat_out_model                         small
% 2.79/1.00  --sat_out_clauses                       false
% 2.79/1.00  
% 2.79/1.00  ------ QBF Options
% 2.79/1.00  
% 2.79/1.00  --qbf_mode                              false
% 2.79/1.00  --qbf_elim_univ                         false
% 2.79/1.00  --qbf_dom_inst                          none
% 2.79/1.00  --qbf_dom_pre_inst                      false
% 2.79/1.00  --qbf_sk_in                             false
% 2.79/1.00  --qbf_pred_elim                         true
% 2.79/1.00  --qbf_split                             512
% 2.79/1.00  
% 2.79/1.00  ------ BMC1 Options
% 2.79/1.00  
% 2.79/1.00  --bmc1_incremental                      false
% 2.79/1.00  --bmc1_axioms                           reachable_all
% 2.79/1.00  --bmc1_min_bound                        0
% 2.79/1.00  --bmc1_max_bound                        -1
% 2.79/1.00  --bmc1_max_bound_default                -1
% 2.79/1.00  --bmc1_symbol_reachability              true
% 2.79/1.00  --bmc1_property_lemmas                  false
% 2.79/1.00  --bmc1_k_induction                      false
% 2.79/1.00  --bmc1_non_equiv_states                 false
% 2.79/1.00  --bmc1_deadlock                         false
% 2.79/1.00  --bmc1_ucm                              false
% 2.79/1.00  --bmc1_add_unsat_core                   none
% 2.79/1.00  --bmc1_unsat_core_children              false
% 2.79/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/1.00  --bmc1_out_stat                         full
% 2.79/1.00  --bmc1_ground_init                      false
% 2.79/1.00  --bmc1_pre_inst_next_state              false
% 2.79/1.00  --bmc1_pre_inst_state                   false
% 2.79/1.00  --bmc1_pre_inst_reach_state             false
% 2.79/1.00  --bmc1_out_unsat_core                   false
% 2.79/1.00  --bmc1_aig_witness_out                  false
% 2.79/1.00  --bmc1_verbose                          false
% 2.79/1.00  --bmc1_dump_clauses_tptp                false
% 2.79/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.79/1.00  --bmc1_dump_file                        -
% 2.79/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.79/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.79/1.00  --bmc1_ucm_extend_mode                  1
% 2.79/1.00  --bmc1_ucm_init_mode                    2
% 2.79/1.00  --bmc1_ucm_cone_mode                    none
% 2.79/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.79/1.00  --bmc1_ucm_relax_model                  4
% 2.79/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.79/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/1.00  --bmc1_ucm_layered_model                none
% 2.79/1.00  --bmc1_ucm_max_lemma_size               10
% 2.79/1.00  
% 2.79/1.00  ------ AIG Options
% 2.79/1.00  
% 2.79/1.00  --aig_mode                              false
% 2.79/1.00  
% 2.79/1.00  ------ Instantiation Options
% 2.79/1.00  
% 2.79/1.00  --instantiation_flag                    true
% 2.79/1.00  --inst_sos_flag                         false
% 2.79/1.00  --inst_sos_phase                        true
% 2.79/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/1.00  --inst_lit_sel_side                     none
% 2.79/1.00  --inst_solver_per_active                1400
% 2.79/1.00  --inst_solver_calls_frac                1.
% 2.79/1.00  --inst_passive_queue_type               priority_queues
% 2.79/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/1.00  --inst_passive_queues_freq              [25;2]
% 2.79/1.00  --inst_dismatching                      true
% 2.79/1.00  --inst_eager_unprocessed_to_passive     true
% 2.79/1.00  --inst_prop_sim_given                   true
% 2.79/1.00  --inst_prop_sim_new                     false
% 2.79/1.00  --inst_subs_new                         false
% 2.79/1.00  --inst_eq_res_simp                      false
% 2.79/1.00  --inst_subs_given                       false
% 2.79/1.00  --inst_orphan_elimination               true
% 2.79/1.00  --inst_learning_loop_flag               true
% 2.79/1.00  --inst_learning_start                   3000
% 2.79/1.00  --inst_learning_factor                  2
% 2.79/1.00  --inst_start_prop_sim_after_learn       3
% 2.79/1.00  --inst_sel_renew                        solver
% 2.79/1.00  --inst_lit_activity_flag                true
% 2.79/1.00  --inst_restr_to_given                   false
% 2.79/1.00  --inst_activity_threshold               500
% 2.79/1.00  --inst_out_proof                        true
% 2.79/1.00  
% 2.79/1.00  ------ Resolution Options
% 2.79/1.00  
% 2.79/1.00  --resolution_flag                       false
% 2.79/1.00  --res_lit_sel                           adaptive
% 2.79/1.00  --res_lit_sel_side                      none
% 2.79/1.00  --res_ordering                          kbo
% 2.79/1.00  --res_to_prop_solver                    active
% 2.79/1.00  --res_prop_simpl_new                    false
% 2.79/1.00  --res_prop_simpl_given                  true
% 2.79/1.00  --res_passive_queue_type                priority_queues
% 2.79/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/1.00  --res_passive_queues_freq               [15;5]
% 2.79/1.00  --res_forward_subs                      full
% 2.79/1.00  --res_backward_subs                     full
% 2.79/1.00  --res_forward_subs_resolution           true
% 2.79/1.00  --res_backward_subs_resolution          true
% 2.79/1.00  --res_orphan_elimination                true
% 2.79/1.00  --res_time_limit                        2.
% 2.79/1.00  --res_out_proof                         true
% 2.79/1.00  
% 2.79/1.00  ------ Superposition Options
% 2.79/1.00  
% 2.79/1.00  --superposition_flag                    true
% 2.79/1.00  --sup_passive_queue_type                priority_queues
% 2.79/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.79/1.00  --demod_completeness_check              fast
% 2.79/1.00  --demod_use_ground                      true
% 2.79/1.00  --sup_to_prop_solver                    passive
% 2.79/1.00  --sup_prop_simpl_new                    true
% 2.79/1.00  --sup_prop_simpl_given                  true
% 2.79/1.00  --sup_fun_splitting                     false
% 2.79/1.00  --sup_smt_interval                      50000
% 2.79/1.00  
% 2.79/1.00  ------ Superposition Simplification Setup
% 2.79/1.00  
% 2.79/1.00  --sup_indices_passive                   []
% 2.79/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_full_bw                           [BwDemod]
% 2.79/1.00  --sup_immed_triv                        [TrivRules]
% 2.79/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_immed_bw_main                     []
% 2.79/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.00  
% 2.79/1.00  ------ Combination Options
% 2.79/1.00  
% 2.79/1.00  --comb_res_mult                         3
% 2.79/1.00  --comb_sup_mult                         2
% 2.79/1.00  --comb_inst_mult                        10
% 2.79/1.00  
% 2.79/1.00  ------ Debug Options
% 2.79/1.00  
% 2.79/1.00  --dbg_backtrace                         false
% 2.79/1.00  --dbg_dump_prop_clauses                 false
% 2.79/1.00  --dbg_dump_prop_clauses_file            -
% 2.79/1.00  --dbg_out_stat                          false
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  ------ Proving...
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  % SZS status Theorem for theBenchmark.p
% 2.79/1.00  
% 2.79/1.00   Resolution empty clause
% 2.79/1.00  
% 2.79/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.79/1.00  
% 2.79/1.00  fof(f16,conjecture,(
% 2.79/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f17,negated_conjecture,(
% 2.79/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.79/1.00    inference(negated_conjecture,[],[f16])).
% 2.79/1.00  
% 2.79/1.00  fof(f34,plain,(
% 2.79/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.79/1.00    inference(ennf_transformation,[],[f17])).
% 2.79/1.00  
% 2.79/1.00  fof(f35,plain,(
% 2.79/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.79/1.00    inference(flattening,[],[f34])).
% 2.79/1.00  
% 2.79/1.00  fof(f42,plain,(
% 2.79/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.79/1.00    introduced(choice_axiom,[])).
% 2.79/1.00  
% 2.79/1.00  fof(f43,plain,(
% 2.79/1.00    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f42])).
% 2.79/1.00  
% 2.79/1.00  fof(f74,plain,(
% 2.79/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.79/1.00    inference(cnf_transformation,[],[f43])).
% 2.79/1.00  
% 2.79/1.00  fof(f12,axiom,(
% 2.79/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f28,plain,(
% 2.79/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/1.00    inference(ennf_transformation,[],[f12])).
% 2.79/1.00  
% 2.79/1.00  fof(f61,plain,(
% 2.79/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f28])).
% 2.79/1.00  
% 2.79/1.00  fof(f14,axiom,(
% 2.79/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f30,plain,(
% 2.79/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/1.00    inference(ennf_transformation,[],[f14])).
% 2.79/1.00  
% 2.79/1.00  fof(f31,plain,(
% 2.79/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/1.00    inference(flattening,[],[f30])).
% 2.79/1.00  
% 2.79/1.00  fof(f41,plain,(
% 2.79/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/1.00    inference(nnf_transformation,[],[f31])).
% 2.79/1.00  
% 2.79/1.00  fof(f63,plain,(
% 2.79/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f41])).
% 2.79/1.00  
% 2.79/1.00  fof(f73,plain,(
% 2.79/1.00    v1_funct_2(sK2,sK0,sK1)),
% 2.79/1.00    inference(cnf_transformation,[],[f43])).
% 2.79/1.00  
% 2.79/1.00  fof(f13,axiom,(
% 2.79/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f29,plain,(
% 2.79/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/1.00    inference(ennf_transformation,[],[f13])).
% 2.79/1.00  
% 2.79/1.00  fof(f62,plain,(
% 2.79/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f29])).
% 2.79/1.00  
% 2.79/1.00  fof(f76,plain,(
% 2.79/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.79/1.00    inference(cnf_transformation,[],[f43])).
% 2.79/1.00  
% 2.79/1.00  fof(f9,axiom,(
% 2.79/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f24,plain,(
% 2.79/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.79/1.00    inference(ennf_transformation,[],[f9])).
% 2.79/1.00  
% 2.79/1.00  fof(f25,plain,(
% 2.79/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.79/1.00    inference(flattening,[],[f24])).
% 2.79/1.00  
% 2.79/1.00  fof(f57,plain,(
% 2.79/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f25])).
% 2.79/1.00  
% 2.79/1.00  fof(f75,plain,(
% 2.79/1.00    v2_funct_1(sK2)),
% 2.79/1.00    inference(cnf_transformation,[],[f43])).
% 2.79/1.00  
% 2.79/1.00  fof(f72,plain,(
% 2.79/1.00    v1_funct_1(sK2)),
% 2.79/1.00    inference(cnf_transformation,[],[f43])).
% 2.79/1.00  
% 2.79/1.00  fof(f10,axiom,(
% 2.79/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f26,plain,(
% 2.79/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/1.00    inference(ennf_transformation,[],[f10])).
% 2.79/1.00  
% 2.79/1.00  fof(f59,plain,(
% 2.79/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f26])).
% 2.79/1.00  
% 2.79/1.00  fof(f15,axiom,(
% 2.79/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f32,plain,(
% 2.79/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.79/1.00    inference(ennf_transformation,[],[f15])).
% 2.79/1.00  
% 2.79/1.00  fof(f33,plain,(
% 2.79/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.79/1.00    inference(flattening,[],[f32])).
% 2.79/1.00  
% 2.79/1.00  fof(f71,plain,(
% 2.79/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f33])).
% 2.79/1.00  
% 2.79/1.00  fof(f58,plain,(
% 2.79/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f25])).
% 2.79/1.00  
% 2.79/1.00  fof(f7,axiom,(
% 2.79/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f20,plain,(
% 2.79/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.79/1.00    inference(ennf_transformation,[],[f7])).
% 2.79/1.00  
% 2.79/1.00  fof(f21,plain,(
% 2.79/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.79/1.00    inference(flattening,[],[f20])).
% 2.79/1.00  
% 2.79/1.00  fof(f55,plain,(
% 2.79/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f21])).
% 2.79/1.00  
% 2.79/1.00  fof(f54,plain,(
% 2.79/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f21])).
% 2.79/1.00  
% 2.79/1.00  fof(f70,plain,(
% 2.79/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f33])).
% 2.79/1.00  
% 2.79/1.00  fof(f77,plain,(
% 2.79/1.00    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.79/1.00    inference(cnf_transformation,[],[f43])).
% 2.79/1.00  
% 2.79/1.00  fof(f2,axiom,(
% 2.79/1.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f38,plain,(
% 2.79/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.79/1.00    inference(nnf_transformation,[],[f2])).
% 2.79/1.00  
% 2.79/1.00  fof(f39,plain,(
% 2.79/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.79/1.00    inference(flattening,[],[f38])).
% 2.79/1.00  
% 2.79/1.00  fof(f48,plain,(
% 2.79/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.79/1.00    inference(cnf_transformation,[],[f39])).
% 2.79/1.00  
% 2.79/1.00  fof(f81,plain,(
% 2.79/1.00    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 2.79/1.00    inference(equality_resolution,[],[f48])).
% 2.79/1.00  
% 2.79/1.00  fof(f66,plain,(
% 2.79/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f41])).
% 2.79/1.00  
% 2.79/1.00  fof(f85,plain,(
% 2.79/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.79/1.00    inference(equality_resolution,[],[f66])).
% 2.79/1.00  
% 2.79/1.00  fof(f4,axiom,(
% 2.79/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f40,plain,(
% 2.79/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.79/1.00    inference(nnf_transformation,[],[f4])).
% 2.79/1.00  
% 2.79/1.00  fof(f51,plain,(
% 2.79/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f40])).
% 2.79/1.00  
% 2.79/1.00  fof(f1,axiom,(
% 2.79/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f36,plain,(
% 2.79/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.79/1.00    inference(nnf_transformation,[],[f1])).
% 2.79/1.00  
% 2.79/1.00  fof(f37,plain,(
% 2.79/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.79/1.00    inference(flattening,[],[f36])).
% 2.79/1.00  
% 2.79/1.00  fof(f46,plain,(
% 2.79/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f37])).
% 2.79/1.00  
% 2.79/1.00  fof(f49,plain,(
% 2.79/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.79/1.00    inference(cnf_transformation,[],[f39])).
% 2.79/1.00  
% 2.79/1.00  fof(f80,plain,(
% 2.79/1.00    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.79/1.00    inference(equality_resolution,[],[f49])).
% 2.79/1.00  
% 2.79/1.00  fof(f3,axiom,(
% 2.79/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f50,plain,(
% 2.79/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f3])).
% 2.79/1.00  
% 2.79/1.00  cnf(c_31,negated_conjecture,
% 2.79/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.79/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1646,plain,
% 2.79/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_17,plain,
% 2.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.79/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1649,plain,
% 2.79/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.79/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3608,plain,
% 2.79/1.00      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_1646,c_1649]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_24,plain,
% 2.79/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.79/1.00      | k1_xboole_0 = X2 ),
% 2.79/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_32,negated_conjecture,
% 2.79/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.79/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_623,plain,
% 2.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.79/1.00      | sK0 != X1
% 2.79/1.00      | sK1 != X2
% 2.79/1.00      | sK2 != X0
% 2.79/1.00      | k1_xboole_0 = X2 ),
% 2.79/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_624,plain,
% 2.79/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.79/1.00      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.79/1.00      | k1_xboole_0 = sK1 ),
% 2.79/1.00      inference(unflattening,[status(thm)],[c_623]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_626,plain,
% 2.79/1.00      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.79/1.00      inference(global_propositional_subsumption,[status(thm)],[c_624,c_31]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3745,plain,
% 2.79/1.00      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_3608,c_626]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_18,plain,
% 2.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.79/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1648,plain,
% 2.79/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.79/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2957,plain,
% 2.79/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_1646,c_1648]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_29,negated_conjecture,
% 2.79/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.79/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2969,plain,
% 2.79/1.00      ( k2_relat_1(sK2) = sK1 ),
% 2.79/1.00      inference(light_normalisation,[status(thm)],[c_2957,c_29]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_14,plain,
% 2.79/1.00      ( ~ v2_funct_1(X0)
% 2.79/1.00      | ~ v1_funct_1(X0)
% 2.79/1.00      | ~ v1_relat_1(X0)
% 2.79/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.79/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_30,negated_conjecture,
% 2.79/1.00      ( v2_funct_1(sK2) ),
% 2.79/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_393,plain,
% 2.79/1.00      ( ~ v1_funct_1(X0)
% 2.79/1.00      | ~ v1_relat_1(X0)
% 2.79/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.79/1.00      | sK2 != X0 ),
% 2.79/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_394,plain,
% 2.79/1.00      ( ~ v1_funct_1(sK2)
% 2.79/1.00      | ~ v1_relat_1(sK2)
% 2.79/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.79/1.00      inference(unflattening,[status(thm)],[c_393]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_33,negated_conjecture,
% 2.79/1.00      ( v1_funct_1(sK2) ),
% 2.79/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_396,plain,
% 2.79/1.00      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.79/1.00      inference(global_propositional_subsumption,[status(thm)],[c_394,c_33]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1644,plain,
% 2.79/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.79/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_15,plain,
% 2.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.79/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1922,plain,
% 2.79/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.79/1.00      | v1_relat_1(sK2) ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1930,plain,
% 2.79/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.79/1.00      inference(global_propositional_subsumption,
% 2.79/1.00                [status(thm)],
% 2.79/1.00                [c_1644,c_33,c_31,c_394,c_1922]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2994,plain,
% 2.79/1.00      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_2969,c_1930]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_25,plain,
% 2.79/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.79/1.00      | ~ v1_funct_1(X0)
% 2.79/1.00      | ~ v1_relat_1(X0) ),
% 2.79/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1647,plain,
% 2.79/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.79/1.00      | v1_funct_1(X0) != iProver_top
% 2.79/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3129,plain,
% 2.79/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 2.79/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.79/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_2994,c_1647]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_13,plain,
% 2.79/1.00      ( ~ v2_funct_1(X0)
% 2.79/1.00      | ~ v1_funct_1(X0)
% 2.79/1.00      | ~ v1_relat_1(X0)
% 2.79/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.79/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_407,plain,
% 2.79/1.00      ( ~ v1_funct_1(X0)
% 2.79/1.00      | ~ v1_relat_1(X0)
% 2.79/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.79/1.00      | sK2 != X0 ),
% 2.79/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_408,plain,
% 2.79/1.00      ( ~ v1_funct_1(sK2)
% 2.79/1.00      | ~ v1_relat_1(sK2)
% 2.79/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.79/1.00      inference(unflattening,[status(thm)],[c_407]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_410,plain,
% 2.79/1.00      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.79/1.00      inference(global_propositional_subsumption,[status(thm)],[c_408,c_33]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1643,plain,
% 2.79/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.79/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1926,plain,
% 2.79/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.79/1.00      inference(global_propositional_subsumption,
% 2.79/1.00                [status(thm)],
% 2.79/1.00                [c_1643,c_33,c_31,c_408,c_1922]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3130,plain,
% 2.79/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.79/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.79/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.79/1.00      inference(light_normalisation,[status(thm)],[c_3129,c_1926]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_34,plain,
% 2.79/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_36,plain,
% 2.79/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_10,plain,
% 2.79/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.79/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1901,plain,
% 2.79/1.00      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1902,plain,
% 2.79/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.79/1.00      | v1_funct_1(sK2) != iProver_top
% 2.79/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1901]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_11,plain,
% 2.79/1.00      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.79/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1904,plain,
% 2.79/1.00      ( ~ v1_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1905,plain,
% 2.79/1.00      ( v1_funct_1(sK2) != iProver_top
% 2.79/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.79/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1904]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1923,plain,
% 2.79/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.79/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1922]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3388,plain,
% 2.79/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 2.79/1.00      inference(global_propositional_subsumption,
% 2.79/1.00                [status(thm)],
% 2.79/1.00                [c_3130,c_34,c_36,c_1902,c_1905,c_1923]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3830,plain,
% 2.79/1.00      ( sK1 = k1_xboole_0
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_3745,c_3388]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_26,plain,
% 2.79/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.79/1.00      | ~ v1_funct_1(X0)
% 2.79/1.00      | ~ v1_relat_1(X0) ),
% 2.79/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_28,negated_conjecture,
% 2.79/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.79/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.79/1.00      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.79/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_634,plain,
% 2.79/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.79/1.00      | ~ v1_funct_1(X0)
% 2.79/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.79/1.00      | ~ v1_relat_1(X0)
% 2.79/1.00      | k2_funct_1(sK2) != X0
% 2.79/1.00      | k2_relat_1(X0) != sK0
% 2.79/1.00      | k1_relat_1(X0) != sK1 ),
% 2.79/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_28]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_635,plain,
% 2.79/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.79/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.79/1.00      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.79/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.79/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.79/1.00      inference(unflattening,[status(thm)],[c_634]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_647,plain,
% 2.79/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.79/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.79/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.79/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.79/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_635,c_15]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1633,plain,
% 2.79/1.00      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.79/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.79/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_636,plain,
% 2.79/1.00      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.79/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.79/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.79/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1996,plain,
% 2.79/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.79/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.79/1.00      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.79/1.00      inference(global_propositional_subsumption,
% 2.79/1.00                [status(thm)],
% 2.79/1.00                [c_1633,c_34,c_36,c_636,c_1902,c_1905,c_1923]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1997,plain,
% 2.79/1.00      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.79/1.00      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.79/1.00      inference(renaming,[status(thm)],[c_1996]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2000,plain,
% 2.79/1.00      ( k2_relat_1(sK2) != sK1
% 2.79/1.00      | k1_relat_1(sK2) != sK0
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.79/1.00      inference(light_normalisation,[status(thm)],[c_1997,c_1926,c_1930]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2993,plain,
% 2.79/1.00      ( k1_relat_1(sK2) != sK0
% 2.79/1.00      | sK1 != sK1
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_2969,c_2000]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2997,plain,
% 2.79/1.00      ( k1_relat_1(sK2) != sK0
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.79/1.00      inference(equality_resolution_simp,[status(thm)],[c_2993]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3831,plain,
% 2.79/1.00      ( sK1 = k1_xboole_0
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_3745,c_2997]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3846,plain,
% 2.79/1.00      ( sK1 = k1_xboole_0 ),
% 2.79/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3830,c_3831]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4289,plain,
% 2.79/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_3846,c_3388]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4,plain,
% 2.79/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.79/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4367,plain,
% 2.79/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_4289,c_4]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_21,plain,
% 2.79/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.79/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.79/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_551,plain,
% 2.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.79/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.79/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.79/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.79/1.00      | k2_funct_1(sK2) != X0
% 2.79/1.00      | sK0 != X1
% 2.79/1.00      | sK1 != k1_xboole_0 ),
% 2.79/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_552,plain,
% 2.79/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.79/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.79/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.79/1.00      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.79/1.00      | sK1 != k1_xboole_0 ),
% 2.79/1.00      inference(unflattening,[status(thm)],[c_551]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1637,plain,
% 2.79/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.79/1.00      | sK1 != k1_xboole_0
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.79/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1826,plain,
% 2.79/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.79/1.00      | sK1 != k1_xboole_0
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.79/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_1637,c_4]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2212,plain,
% 2.79/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.79/1.00      | sK1 != k1_xboole_0
% 2.79/1.00      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.79/1.00      inference(global_propositional_subsumption,
% 2.79/1.00                [status(thm)],
% 2.79/1.00                [c_1826,c_34,c_36,c_1902,c_1923]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2213,plain,
% 2.79/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.79/1.00      | sK1 != k1_xboole_0
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.79/1.00      inference(renaming,[status(thm)],[c_2212]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4299,plain,
% 2.79/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.79/1.00      | k1_xboole_0 != k1_xboole_0
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_3846,c_2213]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4332,plain,
% 2.79/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.79/1.00      inference(equality_resolution_simp,[status(thm)],[c_4299]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4336,plain,
% 2.79/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.79/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_4332,c_4]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4370,plain,
% 2.79/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.79/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_4367,c_4336]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_8,plain,
% 2.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.79/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1655,plain,
% 2.79/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.79/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2352,plain,
% 2.79/1.00      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_1646,c_1655]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_0,plain,
% 2.79/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.79/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1659,plain,
% 2.79/1.00      ( X0 = X1
% 2.79/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.79/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4058,plain,
% 2.79/1.00      ( k2_zfmisc_1(sK0,sK1) = sK2
% 2.79/1.00      | r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) != iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_2352,c_1659]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4284,plain,
% 2.79/1.00      ( k2_zfmisc_1(sK0,k1_xboole_0) = sK2
% 2.79/1.00      | r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) != iProver_top ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_3846,c_4058]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3,plain,
% 2.79/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.79/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4390,plain,
% 2.79/1.00      ( sK2 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_4284,c_3]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2246,plain,
% 2.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | r1_tarski(X0,sK2) ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2247,plain,
% 2.79/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 2.79/1.00      | r1_tarski(X0,sK2) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_2246]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2249,plain,
% 2.79/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) != iProver_top
% 2.79/1.00      | r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_2247]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2257,plain,
% 2.79/1.00      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2258,plain,
% 2.79/1.00      ( sK2 = X0
% 2.79/1.00      | r1_tarski(X0,sK2) != iProver_top
% 2.79/1.00      | r1_tarski(sK2,X0) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_2257]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2260,plain,
% 2.79/1.00      ( sK2 = k1_xboole_0
% 2.79/1.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 2.79/1.00      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_2258]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_6,plain,
% 2.79/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.79/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2795,plain,
% 2.79/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2798,plain,
% 2.79/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_2795]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3555,plain,
% 2.79/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(sK2,X0) ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3556,plain,
% 2.79/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 2.79/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_3555]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3558,plain,
% 2.79/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.79/1.00      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_3556]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4305,plain,
% 2.79/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_3846,c_1646]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4310,plain,
% 2.79/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_4305,c_3]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_5098,plain,
% 2.79/1.00      ( sK2 = k1_xboole_0 ),
% 2.79/1.00      inference(global_propositional_subsumption,
% 2.79/1.00                [status(thm)],
% 2.79/1.00                [c_4390,c_2249,c_2260,c_2798,c_3558,c_4310]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_8107,plain,
% 2.79/1.00      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 2.79/1.00      inference(light_normalisation,[status(thm)],[c_4370,c_5098]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3612,plain,
% 2.79/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 2.79/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_4,c_1649]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4908,plain,
% 2.79/1.00      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_4367,c_3612]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4295,plain,
% 2.79/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_3846,c_2994]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4928,plain,
% 2.79/1.00      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0 ),
% 2.79/1.00      inference(light_normalisation,[status(thm)],[c_4908,c_4295]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_6864,plain,
% 2.79/1.00      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.79/1.00      inference(light_normalisation,[status(thm)],[c_4928,c_5098]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_8108,plain,
% 2.79/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 2.79/1.00      inference(demodulation,[status(thm)],[c_8107,c_6864]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_8109,plain,
% 2.79/1.00      ( $false ),
% 2.79/1.00      inference(equality_resolution_simp,[status(thm)],[c_8108]) ).
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.79/1.00  
% 2.79/1.00  ------                               Statistics
% 2.79/1.00  
% 2.79/1.00  ------ General
% 2.79/1.00  
% 2.79/1.00  abstr_ref_over_cycles:                  0
% 2.79/1.00  abstr_ref_under_cycles:                 0
% 2.79/1.00  gc_basic_clause_elim:                   0
% 2.79/1.00  forced_gc_time:                         0
% 2.79/1.00  parsing_time:                           0.009
% 2.79/1.00  unif_index_cands_time:                  0.
% 2.79/1.00  unif_index_add_time:                    0.
% 2.79/1.00  orderings_time:                         0.
% 2.79/1.00  out_proof_time:                         0.021
% 2.79/1.00  total_time:                             0.328
% 2.79/1.00  num_of_symbols:                         50
% 2.79/1.00  num_of_terms:                           7125
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing
% 2.79/1.00  
% 2.79/1.00  num_of_splits:                          0
% 2.79/1.00  num_of_split_atoms:                     0
% 2.79/1.00  num_of_reused_defs:                     0
% 2.79/1.00  num_eq_ax_congr_red:                    12
% 2.79/1.00  num_of_sem_filtered_clauses:            1
% 2.79/1.00  num_of_subtypes:                        0
% 2.79/1.00  monotx_restored_types:                  0
% 2.79/1.00  sat_num_of_epr_types:                   0
% 2.79/1.00  sat_num_of_non_cyclic_types:            0
% 2.79/1.00  sat_guarded_non_collapsed_types:        0
% 2.79/1.00  num_pure_diseq_elim:                    0
% 2.79/1.00  simp_replaced_by:                       0
% 2.79/1.00  res_preprocessed:                       160
% 2.79/1.00  prep_upred:                             0
% 2.79/1.00  prep_unflattend:                        44
% 2.79/1.00  smt_new_axioms:                         0
% 2.79/1.00  pred_elim_cands:                        4
% 2.79/1.00  pred_elim:                              2
% 2.79/1.00  pred_elim_cl:                           -1
% 2.79/1.00  pred_elim_cycles:                       4
% 2.79/1.00  merged_defs:                            8
% 2.79/1.00  merged_defs_ncl:                        0
% 2.79/1.00  bin_hyper_res:                          8
% 2.79/1.00  prep_cycles:                            4
% 2.79/1.00  pred_elim_time:                         0.009
% 2.79/1.00  splitting_time:                         0.
% 2.79/1.00  sem_filter_time:                        0.
% 2.79/1.00  monotx_time:                            0.
% 2.79/1.00  subtype_inf_time:                       0.
% 2.79/1.00  
% 2.79/1.00  ------ Problem properties
% 2.79/1.00  
% 2.79/1.00  clauses:                                33
% 2.79/1.00  conjectures:                            3
% 2.79/1.00  epr:                                    3
% 2.79/1.00  horn:                                   28
% 2.79/1.00  ground:                                 13
% 2.79/1.00  unary:                                  7
% 2.79/1.00  binary:                                 11
% 2.79/1.00  lits:                                   86
% 2.79/1.00  lits_eq:                                38
% 2.79/1.00  fd_pure:                                0
% 2.79/1.00  fd_pseudo:                              0
% 2.79/1.00  fd_cond:                                2
% 2.79/1.00  fd_pseudo_cond:                         1
% 2.79/1.00  ac_symbols:                             0
% 2.79/1.00  
% 2.79/1.00  ------ Propositional Solver
% 2.79/1.00  
% 2.79/1.00  prop_solver_calls:                      29
% 2.79/1.00  prop_fast_solver_calls:                 1191
% 2.79/1.00  smt_solver_calls:                       0
% 2.79/1.00  smt_fast_solver_calls:                  0
% 2.79/1.00  prop_num_of_clauses:                    2924
% 2.79/1.00  prop_preprocess_simplified:             8619
% 2.79/1.00  prop_fo_subsumed:                       32
% 2.79/1.00  prop_solver_time:                       0.
% 2.79/1.00  smt_solver_time:                        0.
% 2.79/1.00  smt_fast_solver_time:                   0.
% 2.79/1.00  prop_fast_solver_time:                  0.
% 2.79/1.00  prop_unsat_core_time:                   0.
% 2.79/1.00  
% 2.79/1.00  ------ QBF
% 2.79/1.00  
% 2.79/1.00  qbf_q_res:                              0
% 2.79/1.00  qbf_num_tautologies:                    0
% 2.79/1.00  qbf_prep_cycles:                        0
% 2.79/1.00  
% 2.79/1.00  ------ BMC1
% 2.79/1.00  
% 2.79/1.00  bmc1_current_bound:                     -1
% 2.79/1.00  bmc1_last_solved_bound:                 -1
% 2.79/1.00  bmc1_unsat_core_size:                   -1
% 2.79/1.00  bmc1_unsat_core_parents_size:           -1
% 2.79/1.00  bmc1_merge_next_fun:                    0
% 2.79/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.79/1.00  
% 2.79/1.00  ------ Instantiation
% 2.79/1.00  
% 2.79/1.00  inst_num_of_clauses:                    1171
% 2.79/1.00  inst_num_in_passive:                    345
% 2.79/1.00  inst_num_in_active:                     478
% 2.79/1.00  inst_num_in_unprocessed:                351
% 2.79/1.00  inst_num_of_loops:                      610
% 2.79/1.00  inst_num_of_learning_restarts:          0
% 2.79/1.00  inst_num_moves_active_passive:          129
% 2.79/1.00  inst_lit_activity:                      0
% 2.79/1.00  inst_lit_activity_moves:                0
% 2.79/1.00  inst_num_tautologies:                   0
% 2.79/1.00  inst_num_prop_implied:                  0
% 2.79/1.00  inst_num_existing_simplified:           0
% 2.79/1.00  inst_num_eq_res_simplified:             0
% 2.79/1.00  inst_num_child_elim:                    0
% 2.79/1.00  inst_num_of_dismatching_blockings:      282
% 2.79/1.00  inst_num_of_non_proper_insts:           1011
% 2.79/1.00  inst_num_of_duplicates:                 0
% 2.79/1.00  inst_inst_num_from_inst_to_res:         0
% 2.79/1.00  inst_dismatching_checking_time:         0.
% 2.79/1.00  
% 2.79/1.00  ------ Resolution
% 2.79/1.00  
% 2.79/1.00  res_num_of_clauses:                     0
% 2.79/1.00  res_num_in_passive:                     0
% 2.79/1.00  res_num_in_active:                      0
% 2.79/1.00  res_num_of_loops:                       164
% 2.79/1.00  res_forward_subset_subsumed:            74
% 2.79/1.00  res_backward_subset_subsumed:           8
% 2.79/1.00  res_forward_subsumed:                   0
% 2.79/1.00  res_backward_subsumed:                  0
% 2.79/1.00  res_forward_subsumption_resolution:     4
% 2.79/1.00  res_backward_subsumption_resolution:    0
% 2.79/1.00  res_clause_to_clause_subsumption:       635
% 2.79/1.00  res_orphan_elimination:                 0
% 2.79/1.00  res_tautology_del:                      75
% 2.79/1.00  res_num_eq_res_simplified:              0
% 2.79/1.00  res_num_sel_changes:                    0
% 2.79/1.00  res_moves_from_active_to_pass:          0
% 2.79/1.00  
% 2.79/1.00  ------ Superposition
% 2.79/1.00  
% 2.79/1.00  sup_time_total:                         0.
% 2.79/1.00  sup_time_generating:                    0.
% 2.79/1.00  sup_time_sim_full:                      0.
% 2.79/1.00  sup_time_sim_immed:                     0.
% 2.79/1.00  
% 2.79/1.00  sup_num_of_clauses:                     153
% 2.79/1.00  sup_num_in_active:                      78
% 2.79/1.00  sup_num_in_passive:                     75
% 2.79/1.00  sup_num_of_loops:                       120
% 2.79/1.00  sup_fw_superposition:                   113
% 2.79/1.00  sup_bw_superposition:                   98
% 2.79/1.00  sup_immediate_simplified:               109
% 2.79/1.00  sup_given_eliminated:                   1
% 2.79/1.00  comparisons_done:                       0
% 2.79/1.00  comparisons_avoided:                    11
% 2.79/1.00  
% 2.79/1.00  ------ Simplifications
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  sim_fw_subset_subsumed:                 19
% 2.79/1.00  sim_bw_subset_subsumed:                 4
% 2.79/1.00  sim_fw_subsumed:                        12
% 2.79/1.00  sim_bw_subsumed:                        3
% 2.79/1.00  sim_fw_subsumption_res:                 3
% 2.79/1.00  sim_bw_subsumption_res:                 3
% 2.79/1.00  sim_tautology_del:                      2
% 2.79/1.00  sim_eq_tautology_del:                   12
% 2.79/1.00  sim_eq_res_simp:                        3
% 2.79/1.00  sim_fw_demodulated:                     68
% 2.79/1.00  sim_bw_demodulated:                     44
% 2.79/1.00  sim_light_normalised:                   54
% 2.79/1.00  sim_joinable_taut:                      0
% 2.79/1.00  sim_joinable_simp:                      0
% 2.79/1.00  sim_ac_normalised:                      0
% 2.79/1.00  sim_smt_subsumption:                    0
% 2.79/1.00  
%------------------------------------------------------------------------------

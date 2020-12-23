%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:44 EST 2020

% Result     : Theorem 0.34s
% Output     : CNFRefutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  174 (5084 expanded)
%              Number of clauses        :  110 (1555 expanded)
%              Number of leaves         :   14 ( 989 expanded)
%              Depth                    :   24
%              Number of atoms          :  542 (27993 expanded)
%              Number of equality atoms :  277 (5800 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f27,plain,(
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

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,
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

fof(f36,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f35])).

fof(f64,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f49,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_576,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_578,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_576,c_29])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1561,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3491,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_1561])).

cnf(c_1557,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1560,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2981,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1557,c_1560])).

cnf(c_3126,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_578,c_2981])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1559,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2488,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1557,c_1559])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2500,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2488,c_27])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_586,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0
    | k2_funct_1(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_26])).

cnf(c_587,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_599,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_587,c_13])).

cnf(c_1545,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_588,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_1812,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1813,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1812])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1871,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1872,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1871])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1870,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1874,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1870])).

cnf(c_1890,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1545,c_32,c_34,c_588,c_1813,c_1872,c_1874])).

cnf(c_1891,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1890])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_380,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_381,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_383,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_31])).

cnf(c_1554,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_1821,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1554,c_31,c_29,c_381,c_1812])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_366,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_367,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_369,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_31])).

cnf(c_1555,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_1825,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1555,c_31,c_29,c_367,c_1812])).

cnf(c_1894,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1891,c_1821,c_1825])).

cnf(c_2514,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2500,c_1894])).

cnf(c_2518,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2514])).

cnf(c_3346,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3126,c_2518])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1558,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2869,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1821,c_1558])).

cnf(c_2515,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2500,c_1825])).

cnf(c_2888,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2869,c_2515])).

cnf(c_3460,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2888,c_32,c_34,c_1813,c_1872,c_1874])).

cnf(c_3465,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3126,c_3460])).

cnf(c_3760,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3491,c_3346,c_3465])).

cnf(c_3763,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3760,c_3460])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3848,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3763,c_5])).

cnf(c_19,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_504,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_1549,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_1718,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1549,c_5])).

cnf(c_2128,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1718,c_32,c_34,c_1813,c_1872])).

cnf(c_2129,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2128])).

cnf(c_3775,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3760,c_2129])).

cnf(c_3811,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3775])).

cnf(c_3815,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3811,c_5])).

cnf(c_3851,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3848,c_3815])).

cnf(c_3771,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3760,c_2500])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k2_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_435,c_13])).

cnf(c_1552,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1707,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1552,c_4])).

cnf(c_4849,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3771,c_1707])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2083,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2086,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2083])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2091,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2092,plain,
    ( sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2091])).

cnf(c_2094,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2092])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2413,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2414,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2413])).

cnf(c_2416,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2414])).

cnf(c_3780,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3760,c_1557])).

cnf(c_3785,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3780,c_4])).

cnf(c_5196,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4849,c_2086,c_2094,c_2416,c_3785])).

cnf(c_7323,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3851,c_5196])).

cnf(c_2983,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1560])).

cnf(c_4190,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3848,c_2983])).

cnf(c_3770,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3760,c_2515])).

cnf(c_4204,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4190,c_3770])).

cnf(c_6170,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4204,c_5196])).

cnf(c_7324,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7323,c_6170])).

cnf(c_7325,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7324])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:55:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.34/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.34/1.04  
% 0.34/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.34/1.04  
% 0.34/1.04  ------  iProver source info
% 0.34/1.04  
% 0.34/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.34/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.34/1.04  git: non_committed_changes: false
% 0.34/1.04  git: last_make_outside_of_git: false
% 0.34/1.04  
% 0.34/1.04  ------ 
% 0.34/1.04  
% 0.34/1.04  ------ Input Options
% 0.34/1.04  
% 0.34/1.04  --out_options                           all
% 0.34/1.04  --tptp_safe_out                         true
% 0.34/1.04  --problem_path                          ""
% 0.34/1.04  --include_path                          ""
% 0.34/1.04  --clausifier                            res/vclausify_rel
% 0.34/1.04  --clausifier_options                    --mode clausify
% 0.34/1.04  --stdin                                 false
% 0.34/1.04  --stats_out                             all
% 0.34/1.04  
% 0.34/1.04  ------ General Options
% 0.34/1.04  
% 0.34/1.04  --fof                                   false
% 0.34/1.04  --time_out_real                         305.
% 0.34/1.04  --time_out_virtual                      -1.
% 0.34/1.04  --symbol_type_check                     false
% 0.34/1.04  --clausify_out                          false
% 0.34/1.04  --sig_cnt_out                           false
% 0.34/1.04  --trig_cnt_out                          false
% 0.34/1.04  --trig_cnt_out_tolerance                1.
% 0.34/1.04  --trig_cnt_out_sk_spl                   false
% 0.34/1.04  --abstr_cl_out                          false
% 0.34/1.04  
% 0.34/1.04  ------ Global Options
% 0.34/1.04  
% 0.34/1.04  --schedule                              default
% 0.34/1.04  --add_important_lit                     false
% 0.34/1.04  --prop_solver_per_cl                    1000
% 0.34/1.04  --min_unsat_core                        false
% 0.34/1.04  --soft_assumptions                      false
% 0.34/1.04  --soft_lemma_size                       3
% 0.34/1.04  --prop_impl_unit_size                   0
% 0.34/1.04  --prop_impl_unit                        []
% 0.34/1.04  --share_sel_clauses                     true
% 0.34/1.04  --reset_solvers                         false
% 0.34/1.04  --bc_imp_inh                            [conj_cone]
% 0.34/1.04  --conj_cone_tolerance                   3.
% 0.34/1.04  --extra_neg_conj                        none
% 0.34/1.04  --large_theory_mode                     true
% 0.34/1.04  --prolific_symb_bound                   200
% 0.34/1.04  --lt_threshold                          2000
% 0.34/1.04  --clause_weak_htbl                      true
% 0.34/1.04  --gc_record_bc_elim                     false
% 0.34/1.04  
% 0.34/1.04  ------ Preprocessing Options
% 0.34/1.04  
% 0.34/1.04  --preprocessing_flag                    true
% 0.34/1.04  --time_out_prep_mult                    0.1
% 0.34/1.04  --splitting_mode                        input
% 0.34/1.04  --splitting_grd                         true
% 0.34/1.04  --splitting_cvd                         false
% 0.34/1.04  --splitting_cvd_svl                     false
% 0.34/1.04  --splitting_nvd                         32
% 0.34/1.04  --sub_typing                            true
% 0.34/1.04  --prep_gs_sim                           true
% 0.34/1.04  --prep_unflatten                        true
% 0.34/1.04  --prep_res_sim                          true
% 0.34/1.04  --prep_upred                            true
% 0.34/1.04  --prep_sem_filter                       exhaustive
% 0.34/1.04  --prep_sem_filter_out                   false
% 0.34/1.04  --pred_elim                             true
% 0.34/1.04  --res_sim_input                         true
% 0.34/1.04  --eq_ax_congr_red                       true
% 0.34/1.04  --pure_diseq_elim                       true
% 0.34/1.04  --brand_transform                       false
% 0.34/1.04  --non_eq_to_eq                          false
% 0.34/1.04  --prep_def_merge                        true
% 0.34/1.04  --prep_def_merge_prop_impl              false
% 0.34/1.04  --prep_def_merge_mbd                    true
% 0.34/1.04  --prep_def_merge_tr_red                 false
% 0.34/1.04  --prep_def_merge_tr_cl                  false
% 0.34/1.04  --smt_preprocessing                     true
% 0.34/1.04  --smt_ac_axioms                         fast
% 0.34/1.04  --preprocessed_out                      false
% 0.34/1.04  --preprocessed_stats                    false
% 0.34/1.04  
% 0.34/1.04  ------ Abstraction refinement Options
% 0.34/1.04  
% 0.34/1.04  --abstr_ref                             []
% 0.34/1.04  --abstr_ref_prep                        false
% 0.34/1.04  --abstr_ref_until_sat                   false
% 0.34/1.04  --abstr_ref_sig_restrict                funpre
% 0.34/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.34/1.04  --abstr_ref_under                       []
% 0.34/1.04  
% 0.34/1.04  ------ SAT Options
% 0.34/1.04  
% 0.34/1.04  --sat_mode                              false
% 0.34/1.04  --sat_fm_restart_options                ""
% 0.34/1.04  --sat_gr_def                            false
% 0.34/1.04  --sat_epr_types                         true
% 0.34/1.04  --sat_non_cyclic_types                  false
% 0.34/1.04  --sat_finite_models                     false
% 0.34/1.04  --sat_fm_lemmas                         false
% 0.34/1.04  --sat_fm_prep                           false
% 0.34/1.04  --sat_fm_uc_incr                        true
% 0.34/1.04  --sat_out_model                         small
% 0.34/1.04  --sat_out_clauses                       false
% 0.34/1.04  
% 0.34/1.04  ------ QBF Options
% 0.34/1.04  
% 0.34/1.04  --qbf_mode                              false
% 0.34/1.04  --qbf_elim_univ                         false
% 0.34/1.04  --qbf_dom_inst                          none
% 0.34/1.04  --qbf_dom_pre_inst                      false
% 0.34/1.04  --qbf_sk_in                             false
% 0.34/1.04  --qbf_pred_elim                         true
% 0.34/1.04  --qbf_split                             512
% 0.34/1.04  
% 0.34/1.04  ------ BMC1 Options
% 0.34/1.04  
% 0.34/1.04  --bmc1_incremental                      false
% 0.34/1.04  --bmc1_axioms                           reachable_all
% 0.34/1.04  --bmc1_min_bound                        0
% 0.34/1.04  --bmc1_max_bound                        -1
% 0.34/1.04  --bmc1_max_bound_default                -1
% 0.34/1.04  --bmc1_symbol_reachability              true
% 0.34/1.04  --bmc1_property_lemmas                  false
% 0.34/1.04  --bmc1_k_induction                      false
% 0.34/1.04  --bmc1_non_equiv_states                 false
% 0.34/1.04  --bmc1_deadlock                         false
% 0.34/1.04  --bmc1_ucm                              false
% 0.34/1.04  --bmc1_add_unsat_core                   none
% 0.34/1.04  --bmc1_unsat_core_children              false
% 0.34/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.34/1.04  --bmc1_out_stat                         full
% 0.34/1.04  --bmc1_ground_init                      false
% 0.34/1.04  --bmc1_pre_inst_next_state              false
% 0.34/1.04  --bmc1_pre_inst_state                   false
% 0.34/1.04  --bmc1_pre_inst_reach_state             false
% 0.34/1.04  --bmc1_out_unsat_core                   false
% 0.34/1.04  --bmc1_aig_witness_out                  false
% 0.34/1.04  --bmc1_verbose                          false
% 0.34/1.04  --bmc1_dump_clauses_tptp                false
% 0.34/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.34/1.04  --bmc1_dump_file                        -
% 0.34/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.34/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.34/1.04  --bmc1_ucm_extend_mode                  1
% 0.34/1.04  --bmc1_ucm_init_mode                    2
% 0.34/1.04  --bmc1_ucm_cone_mode                    none
% 0.34/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.34/1.04  --bmc1_ucm_relax_model                  4
% 0.34/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.34/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.34/1.04  --bmc1_ucm_layered_model                none
% 0.34/1.04  --bmc1_ucm_max_lemma_size               10
% 0.34/1.04  
% 0.34/1.04  ------ AIG Options
% 0.34/1.04  
% 0.34/1.04  --aig_mode                              false
% 0.34/1.04  
% 0.34/1.04  ------ Instantiation Options
% 0.34/1.04  
% 0.34/1.04  --instantiation_flag                    true
% 0.34/1.04  --inst_sos_flag                         false
% 0.34/1.04  --inst_sos_phase                        true
% 0.34/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.34/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.34/1.04  --inst_lit_sel_side                     num_symb
% 0.34/1.04  --inst_solver_per_active                1400
% 0.34/1.04  --inst_solver_calls_frac                1.
% 0.34/1.04  --inst_passive_queue_type               priority_queues
% 0.34/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.34/1.04  --inst_passive_queues_freq              [25;2]
% 0.34/1.04  --inst_dismatching                      true
% 0.34/1.04  --inst_eager_unprocessed_to_passive     true
% 0.34/1.04  --inst_prop_sim_given                   true
% 0.34/1.04  --inst_prop_sim_new                     false
% 0.34/1.04  --inst_subs_new                         false
% 0.34/1.04  --inst_eq_res_simp                      false
% 0.34/1.04  --inst_subs_given                       false
% 0.34/1.04  --inst_orphan_elimination               true
% 0.34/1.04  --inst_learning_loop_flag               true
% 0.34/1.04  --inst_learning_start                   3000
% 0.34/1.04  --inst_learning_factor                  2
% 0.34/1.04  --inst_start_prop_sim_after_learn       3
% 0.34/1.04  --inst_sel_renew                        solver
% 0.34/1.04  --inst_lit_activity_flag                true
% 0.34/1.04  --inst_restr_to_given                   false
% 0.34/1.04  --inst_activity_threshold               500
% 0.34/1.04  --inst_out_proof                        true
% 0.34/1.04  
% 0.34/1.04  ------ Resolution Options
% 0.34/1.04  
% 0.34/1.04  --resolution_flag                       true
% 0.34/1.04  --res_lit_sel                           adaptive
% 0.34/1.04  --res_lit_sel_side                      none
% 0.34/1.04  --res_ordering                          kbo
% 0.34/1.04  --res_to_prop_solver                    active
% 0.34/1.04  --res_prop_simpl_new                    false
% 0.34/1.04  --res_prop_simpl_given                  true
% 0.34/1.04  --res_passive_queue_type                priority_queues
% 0.34/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.34/1.04  --res_passive_queues_freq               [15;5]
% 0.34/1.04  --res_forward_subs                      full
% 0.34/1.04  --res_backward_subs                     full
% 0.34/1.04  --res_forward_subs_resolution           true
% 0.34/1.04  --res_backward_subs_resolution          true
% 0.34/1.04  --res_orphan_elimination                true
% 0.34/1.04  --res_time_limit                        2.
% 0.34/1.04  --res_out_proof                         true
% 0.34/1.04  
% 0.34/1.04  ------ Superposition Options
% 0.34/1.04  
% 0.34/1.04  --superposition_flag                    true
% 0.34/1.04  --sup_passive_queue_type                priority_queues
% 0.34/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.34/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.34/1.04  --demod_completeness_check              fast
% 0.34/1.04  --demod_use_ground                      true
% 0.34/1.04  --sup_to_prop_solver                    passive
% 0.34/1.04  --sup_prop_simpl_new                    true
% 0.34/1.04  --sup_prop_simpl_given                  true
% 0.34/1.04  --sup_fun_splitting                     false
% 0.34/1.04  --sup_smt_interval                      50000
% 0.34/1.04  
% 0.34/1.04  ------ Superposition Simplification Setup
% 0.34/1.04  
% 0.34/1.04  --sup_indices_passive                   []
% 0.34/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.34/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.34/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.34/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.34/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.34/1.04  --sup_full_bw                           [BwDemod]
% 0.34/1.04  --sup_immed_triv                        [TrivRules]
% 0.34/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.34/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.34/1.04  --sup_immed_bw_main                     []
% 0.34/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.34/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.34/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.34/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.34/1.04  
% 0.34/1.04  ------ Combination Options
% 0.34/1.04  
% 0.34/1.04  --comb_res_mult                         3
% 0.34/1.04  --comb_sup_mult                         2
% 0.34/1.04  --comb_inst_mult                        10
% 0.34/1.04  
% 0.34/1.04  ------ Debug Options
% 0.34/1.04  
% 0.34/1.04  --dbg_backtrace                         false
% 0.34/1.04  --dbg_dump_prop_clauses                 false
% 0.34/1.04  --dbg_dump_prop_clauses_file            -
% 0.34/1.04  --dbg_out_stat                          false
% 0.34/1.04  ------ Parsing...
% 0.34/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.34/1.04  
% 0.34/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.34/1.04  
% 0.34/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.34/1.04  
% 0.34/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.34/1.04  ------ Proving...
% 0.34/1.04  ------ Problem Properties 
% 0.34/1.04  
% 0.34/1.04  
% 0.34/1.04  clauses                                 31
% 0.34/1.04  conjectures                             3
% 0.34/1.04  EPR                                     4
% 0.34/1.04  Horn                                    26
% 0.34/1.04  unary                                   7
% 0.34/1.04  binary                                  9
% 0.34/1.04  lits                                    83
% 0.34/1.04  lits eq                                 36
% 0.34/1.04  fd_pure                                 0
% 0.34/1.04  fd_pseudo                               0
% 0.34/1.04  fd_cond                                 2
% 0.34/1.04  fd_pseudo_cond                          1
% 0.34/1.04  AC symbols                              0
% 0.34/1.04  
% 0.34/1.04  ------ Schedule dynamic 5 is on 
% 0.34/1.04  
% 0.34/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.34/1.04  
% 0.34/1.04  
% 0.34/1.04  ------ 
% 0.34/1.04  Current options:
% 0.34/1.04  ------ 
% 0.34/1.04  
% 0.34/1.04  ------ Input Options
% 0.34/1.04  
% 0.34/1.04  --out_options                           all
% 0.34/1.04  --tptp_safe_out                         true
% 0.34/1.04  --problem_path                          ""
% 0.34/1.04  --include_path                          ""
% 0.34/1.04  --clausifier                            res/vclausify_rel
% 0.34/1.04  --clausifier_options                    --mode clausify
% 0.34/1.04  --stdin                                 false
% 0.34/1.04  --stats_out                             all
% 0.34/1.04  
% 0.34/1.04  ------ General Options
% 0.34/1.04  
% 0.34/1.04  --fof                                   false
% 0.34/1.04  --time_out_real                         305.
% 0.34/1.04  --time_out_virtual                      -1.
% 0.34/1.04  --symbol_type_check                     false
% 0.34/1.04  --clausify_out                          false
% 0.34/1.04  --sig_cnt_out                           false
% 0.34/1.04  --trig_cnt_out                          false
% 0.34/1.04  --trig_cnt_out_tolerance                1.
% 0.34/1.04  --trig_cnt_out_sk_spl                   false
% 0.34/1.04  --abstr_cl_out                          false
% 0.34/1.04  
% 0.34/1.04  ------ Global Options
% 0.34/1.04  
% 0.34/1.04  --schedule                              default
% 0.34/1.04  --add_important_lit                     false
% 0.34/1.04  --prop_solver_per_cl                    1000
% 0.34/1.04  --min_unsat_core                        false
% 0.34/1.04  --soft_assumptions                      false
% 0.34/1.04  --soft_lemma_size                       3
% 0.34/1.04  --prop_impl_unit_size                   0
% 0.34/1.04  --prop_impl_unit                        []
% 0.34/1.04  --share_sel_clauses                     true
% 0.34/1.04  --reset_solvers                         false
% 0.34/1.04  --bc_imp_inh                            [conj_cone]
% 0.34/1.04  --conj_cone_tolerance                   3.
% 0.34/1.04  --extra_neg_conj                        none
% 0.34/1.04  --large_theory_mode                     true
% 0.34/1.04  --prolific_symb_bound                   200
% 0.34/1.04  --lt_threshold                          2000
% 0.34/1.04  --clause_weak_htbl                      true
% 0.34/1.04  --gc_record_bc_elim                     false
% 0.34/1.04  
% 0.34/1.04  ------ Preprocessing Options
% 0.34/1.04  
% 0.34/1.04  --preprocessing_flag                    true
% 0.34/1.04  --time_out_prep_mult                    0.1
% 0.34/1.04  --splitting_mode                        input
% 0.34/1.04  --splitting_grd                         true
% 0.34/1.04  --splitting_cvd                         false
% 0.34/1.04  --splitting_cvd_svl                     false
% 0.34/1.04  --splitting_nvd                         32
% 0.34/1.04  --sub_typing                            true
% 0.34/1.04  --prep_gs_sim                           true
% 0.34/1.04  --prep_unflatten                        true
% 0.34/1.04  --prep_res_sim                          true
% 0.34/1.04  --prep_upred                            true
% 0.34/1.04  --prep_sem_filter                       exhaustive
% 0.34/1.04  --prep_sem_filter_out                   false
% 0.34/1.04  --pred_elim                             true
% 0.34/1.04  --res_sim_input                         true
% 0.34/1.04  --eq_ax_congr_red                       true
% 0.34/1.04  --pure_diseq_elim                       true
% 0.34/1.04  --brand_transform                       false
% 0.34/1.04  --non_eq_to_eq                          false
% 0.34/1.04  --prep_def_merge                        true
% 0.34/1.04  --prep_def_merge_prop_impl              false
% 0.34/1.04  --prep_def_merge_mbd                    true
% 0.34/1.04  --prep_def_merge_tr_red                 false
% 0.34/1.04  --prep_def_merge_tr_cl                  false
% 0.34/1.04  --smt_preprocessing                     true
% 0.34/1.04  --smt_ac_axioms                         fast
% 0.34/1.04  --preprocessed_out                      false
% 0.34/1.04  --preprocessed_stats                    false
% 0.34/1.04  
% 0.34/1.04  ------ Abstraction refinement Options
% 0.34/1.04  
% 0.34/1.04  --abstr_ref                             []
% 0.34/1.04  --abstr_ref_prep                        false
% 0.34/1.04  --abstr_ref_until_sat                   false
% 0.34/1.04  --abstr_ref_sig_restrict                funpre
% 0.34/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.34/1.04  --abstr_ref_under                       []
% 0.34/1.04  
% 0.34/1.04  ------ SAT Options
% 0.34/1.04  
% 0.34/1.04  --sat_mode                              false
% 0.34/1.04  --sat_fm_restart_options                ""
% 0.34/1.04  --sat_gr_def                            false
% 0.34/1.04  --sat_epr_types                         true
% 0.34/1.04  --sat_non_cyclic_types                  false
% 0.34/1.04  --sat_finite_models                     false
% 0.34/1.04  --sat_fm_lemmas                         false
% 0.34/1.04  --sat_fm_prep                           false
% 0.34/1.04  --sat_fm_uc_incr                        true
% 0.34/1.04  --sat_out_model                         small
% 0.34/1.04  --sat_out_clauses                       false
% 0.34/1.04  
% 0.34/1.04  ------ QBF Options
% 0.34/1.04  
% 0.34/1.04  --qbf_mode                              false
% 0.34/1.04  --qbf_elim_univ                         false
% 0.34/1.04  --qbf_dom_inst                          none
% 0.34/1.04  --qbf_dom_pre_inst                      false
% 0.34/1.04  --qbf_sk_in                             false
% 0.34/1.04  --qbf_pred_elim                         true
% 0.34/1.04  --qbf_split                             512
% 0.34/1.04  
% 0.34/1.04  ------ BMC1 Options
% 0.34/1.04  
% 0.34/1.04  --bmc1_incremental                      false
% 0.34/1.04  --bmc1_axioms                           reachable_all
% 0.34/1.04  --bmc1_min_bound                        0
% 0.34/1.04  --bmc1_max_bound                        -1
% 0.34/1.04  --bmc1_max_bound_default                -1
% 0.34/1.04  --bmc1_symbol_reachability              true
% 0.34/1.04  --bmc1_property_lemmas                  false
% 0.34/1.04  --bmc1_k_induction                      false
% 0.34/1.04  --bmc1_non_equiv_states                 false
% 0.34/1.04  --bmc1_deadlock                         false
% 0.34/1.04  --bmc1_ucm                              false
% 0.34/1.04  --bmc1_add_unsat_core                   none
% 0.34/1.04  --bmc1_unsat_core_children              false
% 0.34/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.34/1.04  --bmc1_out_stat                         full
% 0.34/1.04  --bmc1_ground_init                      false
% 0.34/1.04  --bmc1_pre_inst_next_state              false
% 0.34/1.04  --bmc1_pre_inst_state                   false
% 0.34/1.04  --bmc1_pre_inst_reach_state             false
% 0.34/1.04  --bmc1_out_unsat_core                   false
% 0.34/1.04  --bmc1_aig_witness_out                  false
% 0.34/1.04  --bmc1_verbose                          false
% 0.34/1.04  --bmc1_dump_clauses_tptp                false
% 0.34/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.34/1.04  --bmc1_dump_file                        -
% 0.34/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.34/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.34/1.04  --bmc1_ucm_extend_mode                  1
% 0.34/1.04  --bmc1_ucm_init_mode                    2
% 0.34/1.04  --bmc1_ucm_cone_mode                    none
% 0.34/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.34/1.04  --bmc1_ucm_relax_model                  4
% 0.34/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.34/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.34/1.04  --bmc1_ucm_layered_model                none
% 0.34/1.04  --bmc1_ucm_max_lemma_size               10
% 0.34/1.04  
% 0.34/1.04  ------ AIG Options
% 0.34/1.04  
% 0.34/1.04  --aig_mode                              false
% 0.34/1.04  
% 0.34/1.04  ------ Instantiation Options
% 0.34/1.04  
% 0.34/1.04  --instantiation_flag                    true
% 0.34/1.04  --inst_sos_flag                         false
% 0.34/1.04  --inst_sos_phase                        true
% 0.34/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.34/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.34/1.04  --inst_lit_sel_side                     none
% 0.34/1.04  --inst_solver_per_active                1400
% 0.34/1.04  --inst_solver_calls_frac                1.
% 0.34/1.04  --inst_passive_queue_type               priority_queues
% 0.34/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.34/1.04  --inst_passive_queues_freq              [25;2]
% 0.34/1.04  --inst_dismatching                      true
% 0.34/1.04  --inst_eager_unprocessed_to_passive     true
% 0.34/1.04  --inst_prop_sim_given                   true
% 0.34/1.04  --inst_prop_sim_new                     false
% 0.34/1.04  --inst_subs_new                         false
% 0.34/1.04  --inst_eq_res_simp                      false
% 0.34/1.04  --inst_subs_given                       false
% 0.34/1.04  --inst_orphan_elimination               true
% 0.34/1.04  --inst_learning_loop_flag               true
% 0.34/1.04  --inst_learning_start                   3000
% 0.34/1.04  --inst_learning_factor                  2
% 0.34/1.04  --inst_start_prop_sim_after_learn       3
% 0.34/1.04  --inst_sel_renew                        solver
% 0.34/1.04  --inst_lit_activity_flag                true
% 0.34/1.04  --inst_restr_to_given                   false
% 0.34/1.04  --inst_activity_threshold               500
% 0.34/1.04  --inst_out_proof                        true
% 0.34/1.04  
% 0.34/1.04  ------ Resolution Options
% 0.34/1.04  
% 0.34/1.04  --resolution_flag                       false
% 0.34/1.04  --res_lit_sel                           adaptive
% 0.34/1.04  --res_lit_sel_side                      none
% 0.34/1.04  --res_ordering                          kbo
% 0.34/1.04  --res_to_prop_solver                    active
% 0.34/1.04  --res_prop_simpl_new                    false
% 0.34/1.04  --res_prop_simpl_given                  true
% 0.34/1.04  --res_passive_queue_type                priority_queues
% 0.34/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.34/1.04  --res_passive_queues_freq               [15;5]
% 0.34/1.04  --res_forward_subs                      full
% 0.34/1.04  --res_backward_subs                     full
% 0.34/1.04  --res_forward_subs_resolution           true
% 0.34/1.04  --res_backward_subs_resolution          true
% 0.34/1.04  --res_orphan_elimination                true
% 0.34/1.04  --res_time_limit                        2.
% 0.34/1.04  --res_out_proof                         true
% 0.34/1.04  
% 0.34/1.04  ------ Superposition Options
% 0.34/1.04  
% 0.34/1.04  --superposition_flag                    true
% 0.34/1.04  --sup_passive_queue_type                priority_queues
% 0.34/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.34/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.34/1.04  --demod_completeness_check              fast
% 0.34/1.04  --demod_use_ground                      true
% 0.34/1.04  --sup_to_prop_solver                    passive
% 0.34/1.04  --sup_prop_simpl_new                    true
% 0.34/1.04  --sup_prop_simpl_given                  true
% 0.34/1.04  --sup_fun_splitting                     false
% 0.34/1.04  --sup_smt_interval                      50000
% 0.34/1.04  
% 0.34/1.04  ------ Superposition Simplification Setup
% 0.34/1.04  
% 0.34/1.04  --sup_indices_passive                   []
% 0.34/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.34/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.34/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.34/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.34/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.34/1.04  --sup_full_bw                           [BwDemod]
% 0.34/1.04  --sup_immed_triv                        [TrivRules]
% 0.34/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.34/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.34/1.04  --sup_immed_bw_main                     []
% 0.34/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.34/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.34/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.34/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.34/1.04  
% 0.34/1.04  ------ Combination Options
% 0.34/1.04  
% 0.34/1.04  --comb_res_mult                         3
% 0.34/1.04  --comb_sup_mult                         2
% 0.34/1.04  --comb_inst_mult                        10
% 0.34/1.04  
% 0.34/1.04  ------ Debug Options
% 0.34/1.04  
% 0.34/1.04  --dbg_backtrace                         false
% 0.34/1.04  --dbg_dump_prop_clauses                 false
% 0.34/1.04  --dbg_dump_prop_clauses_file            -
% 0.34/1.04  --dbg_out_stat                          false
% 0.34/1.04  
% 0.34/1.04  
% 0.34/1.04  
% 0.34/1.04  
% 0.34/1.04  ------ Proving...
% 0.34/1.04  
% 0.34/1.04  
% 0.34/1.04  % SZS status Theorem for theBenchmark.p
% 0.34/1.04  
% 0.34/1.04   Resolution empty clause
% 0.34/1.04  
% 0.34/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.34/1.04  
% 0.34/1.04  fof(f11,axiom,(
% 0.34/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f23,plain,(
% 0.34/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.34/1.04    inference(ennf_transformation,[],[f11])).
% 0.34/1.04  
% 0.34/1.04  fof(f24,plain,(
% 0.34/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.34/1.04    inference(flattening,[],[f23])).
% 0.34/1.04  
% 0.34/1.04  fof(f34,plain,(
% 0.34/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.34/1.04    inference(nnf_transformation,[],[f24])).
% 0.34/1.04  
% 0.34/1.04  fof(f54,plain,(
% 0.34/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.34/1.04    inference(cnf_transformation,[],[f34])).
% 0.34/1.04  
% 0.34/1.04  fof(f13,conjecture,(
% 0.34/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f14,negated_conjecture,(
% 0.34/1.04    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.34/1.04    inference(negated_conjecture,[],[f13])).
% 0.34/1.04  
% 0.34/1.04  fof(f27,plain,(
% 0.34/1.04    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.34/1.04    inference(ennf_transformation,[],[f14])).
% 0.34/1.04  
% 0.34/1.04  fof(f28,plain,(
% 0.34/1.04    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.34/1.04    inference(flattening,[],[f27])).
% 0.34/1.04  
% 0.34/1.04  fof(f35,plain,(
% 0.34/1.04    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.34/1.04    introduced(choice_axiom,[])).
% 0.34/1.04  
% 0.34/1.04  fof(f36,plain,(
% 0.34/1.04    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.34/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f35])).
% 0.34/1.04  
% 0.34/1.04  fof(f64,plain,(
% 0.34/1.04    v1_funct_2(sK2,sK0,sK1)),
% 0.34/1.04    inference(cnf_transformation,[],[f36])).
% 0.34/1.04  
% 0.34/1.04  fof(f65,plain,(
% 0.34/1.04    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.34/1.04    inference(cnf_transformation,[],[f36])).
% 0.34/1.04  
% 0.34/1.04  fof(f8,axiom,(
% 0.34/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f20,plain,(
% 0.34/1.04    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.34/1.04    inference(ennf_transformation,[],[f8])).
% 0.34/1.04  
% 0.34/1.04  fof(f51,plain,(
% 0.34/1.04    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.34/1.04    inference(cnf_transformation,[],[f20])).
% 0.34/1.04  
% 0.34/1.04  fof(f9,axiom,(
% 0.34/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f21,plain,(
% 0.34/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.34/1.04    inference(ennf_transformation,[],[f9])).
% 0.34/1.04  
% 0.34/1.04  fof(f52,plain,(
% 0.34/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.34/1.04    inference(cnf_transformation,[],[f21])).
% 0.34/1.04  
% 0.34/1.04  fof(f10,axiom,(
% 0.34/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f22,plain,(
% 0.34/1.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.34/1.04    inference(ennf_transformation,[],[f10])).
% 0.34/1.04  
% 0.34/1.04  fof(f53,plain,(
% 0.34/1.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.34/1.04    inference(cnf_transformation,[],[f22])).
% 0.34/1.04  
% 0.34/1.04  fof(f67,plain,(
% 0.34/1.04    k2_relset_1(sK0,sK1,sK2) = sK1),
% 0.34/1.04    inference(cnf_transformation,[],[f36])).
% 0.34/1.04  
% 0.34/1.04  fof(f12,axiom,(
% 0.34/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f25,plain,(
% 0.34/1.04    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.34/1.04    inference(ennf_transformation,[],[f12])).
% 0.34/1.04  
% 0.34/1.04  fof(f26,plain,(
% 0.34/1.04    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.34/1.04    inference(flattening,[],[f25])).
% 0.34/1.04  
% 0.34/1.04  fof(f61,plain,(
% 0.34/1.04    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.34/1.04    inference(cnf_transformation,[],[f26])).
% 0.34/1.04  
% 0.34/1.04  fof(f68,plain,(
% 0.34/1.04    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.34/1.04    inference(cnf_transformation,[],[f36])).
% 0.34/1.04  
% 0.34/1.04  fof(f7,axiom,(
% 0.34/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f19,plain,(
% 0.34/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.34/1.04    inference(ennf_transformation,[],[f7])).
% 0.34/1.04  
% 0.34/1.04  fof(f50,plain,(
% 0.34/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.34/1.04    inference(cnf_transformation,[],[f19])).
% 0.34/1.04  
% 0.34/1.04  fof(f63,plain,(
% 0.34/1.04    v1_funct_1(sK2)),
% 0.34/1.04    inference(cnf_transformation,[],[f36])).
% 0.34/1.04  
% 0.34/1.04  fof(f5,axiom,(
% 0.34/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f15,plain,(
% 0.34/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.34/1.04    inference(ennf_transformation,[],[f5])).
% 0.34/1.04  
% 0.34/1.04  fof(f16,plain,(
% 0.34/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.34/1.04    inference(flattening,[],[f15])).
% 0.34/1.04  
% 0.34/1.04  fof(f47,plain,(
% 0.34/1.04    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.34/1.04    inference(cnf_transformation,[],[f16])).
% 0.34/1.04  
% 0.34/1.04  fof(f46,plain,(
% 0.34/1.04    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.34/1.04    inference(cnf_transformation,[],[f16])).
% 0.34/1.04  
% 0.34/1.04  fof(f6,axiom,(
% 0.34/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f17,plain,(
% 0.34/1.04    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.34/1.04    inference(ennf_transformation,[],[f6])).
% 0.34/1.04  
% 0.34/1.04  fof(f18,plain,(
% 0.34/1.04    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.34/1.04    inference(flattening,[],[f17])).
% 0.34/1.04  
% 0.34/1.04  fof(f49,plain,(
% 0.34/1.04    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.34/1.04    inference(cnf_transformation,[],[f18])).
% 0.34/1.04  
% 0.34/1.04  fof(f66,plain,(
% 0.34/1.04    v2_funct_1(sK2)),
% 0.34/1.04    inference(cnf_transformation,[],[f36])).
% 0.34/1.04  
% 0.34/1.04  fof(f48,plain,(
% 0.34/1.04    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.34/1.04    inference(cnf_transformation,[],[f18])).
% 0.34/1.04  
% 0.34/1.04  fof(f62,plain,(
% 0.34/1.04    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.34/1.04    inference(cnf_transformation,[],[f26])).
% 0.34/1.04  
% 0.34/1.04  fof(f3,axiom,(
% 0.34/1.04    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f31,plain,(
% 0.34/1.04    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.34/1.04    inference(nnf_transformation,[],[f3])).
% 0.34/1.04  
% 0.34/1.04  fof(f32,plain,(
% 0.34/1.04    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.34/1.04    inference(flattening,[],[f31])).
% 0.34/1.04  
% 0.34/1.04  fof(f42,plain,(
% 0.34/1.04    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.34/1.04    inference(cnf_transformation,[],[f32])).
% 0.34/1.04  
% 0.34/1.04  fof(f72,plain,(
% 0.34/1.04    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.34/1.04    inference(equality_resolution,[],[f42])).
% 0.34/1.04  
% 0.34/1.04  fof(f57,plain,(
% 0.34/1.04    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.34/1.04    inference(cnf_transformation,[],[f34])).
% 0.34/1.04  
% 0.34/1.04  fof(f76,plain,(
% 0.34/1.04    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.34/1.04    inference(equality_resolution,[],[f57])).
% 0.34/1.04  
% 0.34/1.04  fof(f58,plain,(
% 0.34/1.04    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.34/1.04    inference(cnf_transformation,[],[f34])).
% 0.34/1.04  
% 0.34/1.04  fof(f75,plain,(
% 0.34/1.04    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.34/1.04    inference(equality_resolution,[],[f58])).
% 0.34/1.04  
% 0.34/1.04  fof(f43,plain,(
% 0.34/1.04    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.34/1.04    inference(cnf_transformation,[],[f32])).
% 0.34/1.04  
% 0.34/1.04  fof(f71,plain,(
% 0.34/1.04    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.34/1.04    inference(equality_resolution,[],[f43])).
% 0.34/1.04  
% 0.34/1.04  fof(f2,axiom,(
% 0.34/1.04    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f40,plain,(
% 0.34/1.04    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.34/1.04    inference(cnf_transformation,[],[f2])).
% 0.34/1.04  
% 0.34/1.04  fof(f1,axiom,(
% 0.34/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f29,plain,(
% 0.34/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.34/1.04    inference(nnf_transformation,[],[f1])).
% 0.34/1.04  
% 0.34/1.04  fof(f30,plain,(
% 0.34/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.34/1.04    inference(flattening,[],[f29])).
% 0.34/1.04  
% 0.34/1.04  fof(f39,plain,(
% 0.34/1.04    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.34/1.04    inference(cnf_transformation,[],[f30])).
% 0.34/1.04  
% 0.34/1.04  fof(f4,axiom,(
% 0.34/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.34/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.34/1.04  
% 0.34/1.04  fof(f33,plain,(
% 0.34/1.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.34/1.04    inference(nnf_transformation,[],[f4])).
% 0.34/1.04  
% 0.34/1.04  fof(f44,plain,(
% 0.34/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.34/1.04    inference(cnf_transformation,[],[f33])).
% 0.34/1.04  
% 0.34/1.04  cnf(c_22,plain,
% 0.34/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 0.34/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.34/1.04      | k1_relset_1(X1,X2,X0) = X1
% 0.34/1.04      | k1_xboole_0 = X2 ),
% 0.34/1.04      inference(cnf_transformation,[],[f54]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_30,negated_conjecture,
% 0.34/1.04      ( v1_funct_2(sK2,sK0,sK1) ),
% 0.34/1.04      inference(cnf_transformation,[],[f64]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_575,plain,
% 0.34/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.34/1.04      | k1_relset_1(X1,X2,X0) = X1
% 0.34/1.04      | sK0 != X1
% 0.34/1.04      | sK1 != X2
% 0.34/1.04      | sK2 != X0
% 0.34/1.04      | k1_xboole_0 = X2 ),
% 0.34/1.04      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_576,plain,
% 0.34/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.34/1.04      | k1_relset_1(sK0,sK1,sK2) = sK0
% 0.34/1.04      | k1_xboole_0 = sK1 ),
% 0.34/1.04      inference(unflattening,[status(thm)],[c_575]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_29,negated_conjecture,
% 0.34/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.34/1.04      inference(cnf_transformation,[],[f65]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_578,plain,
% 0.34/1.04      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 0.34/1.04      inference(global_propositional_subsumption,[status(thm)],[c_576,c_29]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_14,plain,
% 0.34/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.34/1.04      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 0.34/1.04      inference(cnf_transformation,[],[f51]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1561,plain,
% 0.34/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 0.34/1.04      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3491,plain,
% 0.34/1.04      ( sK1 = k1_xboole_0
% 0.34/1.04      | m1_subset_1(sK0,k1_zfmisc_1(sK0)) = iProver_top
% 0.34/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 0.34/1.04      inference(superposition,[status(thm)],[c_578,c_1561]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1557,plain,
% 0.34/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_15,plain,
% 0.34/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.34/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 0.34/1.04      inference(cnf_transformation,[],[f52]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1560,plain,
% 0.34/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 0.34/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2981,plain,
% 0.34/1.04      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 0.34/1.04      inference(superposition,[status(thm)],[c_1557,c_1560]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3126,plain,
% 0.34/1.04      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 0.34/1.04      inference(superposition,[status(thm)],[c_578,c_2981]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_16,plain,
% 0.34/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.34/1.04      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 0.34/1.04      inference(cnf_transformation,[],[f53]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1559,plain,
% 0.34/1.04      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 0.34/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2488,plain,
% 0.34/1.04      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 0.34/1.04      inference(superposition,[status(thm)],[c_1557,c_1559]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_27,negated_conjecture,
% 0.34/1.04      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 0.34/1.04      inference(cnf_transformation,[],[f67]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2500,plain,
% 0.34/1.04      ( k2_relat_1(sK2) = sK1 ),
% 0.34/1.04      inference(light_normalisation,[status(thm)],[c_2488,c_27]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_24,plain,
% 0.34/1.04      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 0.34/1.04      | ~ v1_relat_1(X0)
% 0.34/1.04      | ~ v1_funct_1(X0) ),
% 0.34/1.04      inference(cnf_transformation,[],[f61]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_26,negated_conjecture,
% 0.34/1.04      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 0.34/1.04      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 0.34/1.04      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 0.34/1.04      inference(cnf_transformation,[],[f68]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_586,plain,
% 0.34/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 0.34/1.04      | ~ v1_relat_1(X0)
% 0.34/1.04      | ~ v1_funct_1(X0)
% 0.34/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 0.34/1.04      | k1_relat_1(X0) != sK1
% 0.34/1.04      | k2_relat_1(X0) != sK0
% 0.34/1.04      | k2_funct_1(sK2) != X0 ),
% 0.34/1.04      inference(resolution_lifted,[status(thm)],[c_24,c_26]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_587,plain,
% 0.34/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 0.34/1.04      | ~ v1_relat_1(k2_funct_1(sK2))
% 0.34/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 0.34/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 0.34/1.04      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 0.34/1.04      inference(unflattening,[status(thm)],[c_586]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_13,plain,
% 0.34/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 0.34/1.04      inference(cnf_transformation,[],[f50]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_599,plain,
% 0.34/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 0.34/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 0.34/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 0.34/1.04      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 0.34/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_587,c_13]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1545,plain,
% 0.34/1.04      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 0.34/1.04      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 0.34/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_31,negated_conjecture,
% 0.34/1.04      ( v1_funct_1(sK2) ),
% 0.34/1.04      inference(cnf_transformation,[],[f63]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_32,plain,
% 0.34/1.04      ( v1_funct_1(sK2) = iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_34,plain,
% 0.34/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_588,plain,
% 0.34/1.04      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 0.34/1.04      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 0.34/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 0.34/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1812,plain,
% 0.34/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.34/1.04      | v1_relat_1(sK2) ),
% 0.34/1.04      inference(instantiation,[status(thm)],[c_13]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1813,plain,
% 0.34/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 0.34/1.04      | v1_relat_1(sK2) = iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_1812]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_9,plain,
% 0.34/1.04      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 0.34/1.04      inference(cnf_transformation,[],[f47]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1871,plain,
% 0.34/1.04      ( ~ v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) ),
% 0.34/1.04      inference(instantiation,[status(thm)],[c_9]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1872,plain,
% 0.34/1.04      ( v1_relat_1(sK2) != iProver_top
% 0.34/1.04      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 0.34/1.04      | v1_funct_1(sK2) != iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_1871]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_10,plain,
% 0.34/1.04      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 0.34/1.04      inference(cnf_transformation,[],[f46]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1870,plain,
% 0.34/1.04      ( v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) | ~ v1_funct_1(sK2) ),
% 0.34/1.04      inference(instantiation,[status(thm)],[c_10]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1874,plain,
% 0.34/1.04      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 0.34/1.04      | v1_relat_1(sK2) != iProver_top
% 0.34/1.04      | v1_funct_1(sK2) != iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_1870]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1890,plain,
% 0.34/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 0.34/1.04      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 0.34/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 0.34/1.04      inference(global_propositional_subsumption,
% 0.34/1.04                [status(thm)],
% 0.34/1.04                [c_1545,c_32,c_34,c_588,c_1813,c_1872,c_1874]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1891,plain,
% 0.34/1.04      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 0.34/1.04      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 0.34/1.04      inference(renaming,[status(thm)],[c_1890]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_11,plain,
% 0.34/1.04      ( ~ v2_funct_1(X0)
% 0.34/1.04      | ~ v1_relat_1(X0)
% 0.34/1.04      | ~ v1_funct_1(X0)
% 0.34/1.04      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 0.34/1.04      inference(cnf_transformation,[],[f49]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_28,negated_conjecture,
% 0.34/1.04      ( v2_funct_1(sK2) ),
% 0.34/1.04      inference(cnf_transformation,[],[f66]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_380,plain,
% 0.34/1.04      ( ~ v1_relat_1(X0)
% 0.34/1.04      | ~ v1_funct_1(X0)
% 0.34/1.04      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 0.34/1.04      | sK2 != X0 ),
% 0.34/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_28]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_381,plain,
% 0.34/1.04      ( ~ v1_relat_1(sK2)
% 0.34/1.04      | ~ v1_funct_1(sK2)
% 0.34/1.04      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 0.34/1.04      inference(unflattening,[status(thm)],[c_380]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_383,plain,
% 0.34/1.04      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 0.34/1.04      inference(global_propositional_subsumption,[status(thm)],[c_381,c_31]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1554,plain,
% 0.34/1.04      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 0.34/1.04      | v1_relat_1(sK2) != iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1821,plain,
% 0.34/1.04      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 0.34/1.04      inference(global_propositional_subsumption,
% 0.34/1.04                [status(thm)],
% 0.34/1.04                [c_1554,c_31,c_29,c_381,c_1812]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_12,plain,
% 0.34/1.04      ( ~ v2_funct_1(X0)
% 0.34/1.04      | ~ v1_relat_1(X0)
% 0.34/1.04      | ~ v1_funct_1(X0)
% 0.34/1.04      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 0.34/1.04      inference(cnf_transformation,[],[f48]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_366,plain,
% 0.34/1.04      ( ~ v1_relat_1(X0)
% 0.34/1.04      | ~ v1_funct_1(X0)
% 0.34/1.04      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 0.34/1.04      | sK2 != X0 ),
% 0.34/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_367,plain,
% 0.34/1.04      ( ~ v1_relat_1(sK2)
% 0.34/1.04      | ~ v1_funct_1(sK2)
% 0.34/1.04      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 0.34/1.04      inference(unflattening,[status(thm)],[c_366]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_369,plain,
% 0.34/1.04      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 0.34/1.04      inference(global_propositional_subsumption,[status(thm)],[c_367,c_31]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1555,plain,
% 0.34/1.04      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 0.34/1.04      | v1_relat_1(sK2) != iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1825,plain,
% 0.34/1.04      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 0.34/1.04      inference(global_propositional_subsumption,
% 0.34/1.04                [status(thm)],
% 0.34/1.04                [c_1555,c_31,c_29,c_367,c_1812]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1894,plain,
% 0.34/1.04      ( k1_relat_1(sK2) != sK0
% 0.34/1.04      | k2_relat_1(sK2) != sK1
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 0.34/1.04      inference(light_normalisation,[status(thm)],[c_1891,c_1821,c_1825]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2514,plain,
% 0.34/1.04      ( k1_relat_1(sK2) != sK0
% 0.34/1.04      | sK1 != sK1
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_2500,c_1894]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2518,plain,
% 0.34/1.04      ( k1_relat_1(sK2) != sK0
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 0.34/1.04      inference(equality_resolution_simp,[status(thm)],[c_2514]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3346,plain,
% 0.34/1.04      ( sK1 = k1_xboole_0
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 0.34/1.04      inference(superposition,[status(thm)],[c_3126,c_2518]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_23,plain,
% 0.34/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 0.34/1.04      | ~ v1_relat_1(X0)
% 0.34/1.04      | ~ v1_funct_1(X0) ),
% 0.34/1.04      inference(cnf_transformation,[],[f62]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1558,plain,
% 0.34/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 0.34/1.04      | v1_relat_1(X0) != iProver_top
% 0.34/1.04      | v1_funct_1(X0) != iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2869,plain,
% 0.34/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 0.34/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 0.34/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.34/1.04      inference(superposition,[status(thm)],[c_1821,c_1558]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2515,plain,
% 0.34/1.04      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_2500,c_1825]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2888,plain,
% 0.34/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 0.34/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 0.34/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.34/1.04      inference(light_normalisation,[status(thm)],[c_2869,c_2515]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3460,plain,
% 0.34/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 0.34/1.04      inference(global_propositional_subsumption,
% 0.34/1.04                [status(thm)],
% 0.34/1.04                [c_2888,c_32,c_34,c_1813,c_1872,c_1874]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3465,plain,
% 0.34/1.04      ( sK1 = k1_xboole_0
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 0.34/1.04      inference(superposition,[status(thm)],[c_3126,c_3460]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3760,plain,
% 0.34/1.04      ( sK1 = k1_xboole_0 ),
% 0.34/1.04      inference(global_propositional_subsumption,
% 0.34/1.04                [status(thm)],
% 0.34/1.04                [c_3491,c_3346,c_3465]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3763,plain,
% 0.34/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_3760,c_3460]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_5,plain,
% 0.34/1.04      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.34/1.04      inference(cnf_transformation,[],[f72]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3848,plain,
% 0.34/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_3763,c_5]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_19,plain,
% 0.34/1.04      ( v1_funct_2(X0,k1_xboole_0,X1)
% 0.34/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.34/1.04      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 0.34/1.04      inference(cnf_transformation,[],[f76]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_503,plain,
% 0.34/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.34/1.04      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 0.34/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 0.34/1.04      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 0.34/1.04      | k2_funct_1(sK2) != X0
% 0.34/1.04      | sK0 != X1
% 0.34/1.04      | sK1 != k1_xboole_0 ),
% 0.34/1.04      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_504,plain,
% 0.34/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 0.34/1.04      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.34/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 0.34/1.04      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 0.34/1.04      | sK1 != k1_xboole_0 ),
% 0.34/1.04      inference(unflattening,[status(thm)],[c_503]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1549,plain,
% 0.34/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 0.34/1.04      | sK1 != k1_xboole_0
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 0.34/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1718,plain,
% 0.34/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 0.34/1.04      | sK1 != k1_xboole_0
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 0.34/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_1549,c_5]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2128,plain,
% 0.34/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 0.34/1.04      | sK1 != k1_xboole_0
% 0.34/1.04      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 0.34/1.04      inference(global_propositional_subsumption,
% 0.34/1.04                [status(thm)],
% 0.34/1.04                [c_1718,c_32,c_34,c_1813,c_1872]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2129,plain,
% 0.34/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 0.34/1.04      | sK1 != k1_xboole_0
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 0.34/1.04      inference(renaming,[status(thm)],[c_2128]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3775,plain,
% 0.34/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 0.34/1.04      | k1_xboole_0 != k1_xboole_0
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_3760,c_2129]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3811,plain,
% 0.34/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 0.34/1.04      inference(equality_resolution_simp,[status(thm)],[c_3775]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3815,plain,
% 0.34/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 0.34/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_3811,c_5]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3851,plain,
% 0.34/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 0.34/1.04      inference(backward_subsumption_resolution,[status(thm)],[c_3848,c_3815]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3771,plain,
% 0.34/1.04      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_3760,c_2500]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_18,plain,
% 0.34/1.04      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 0.34/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 0.34/1.04      | k1_xboole_0 = X1
% 0.34/1.04      | k1_xboole_0 = X0 ),
% 0.34/1.04      inference(cnf_transformation,[],[f75]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_434,plain,
% 0.34/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 0.34/1.04      | ~ v1_relat_1(X2)
% 0.34/1.04      | ~ v1_funct_1(X2)
% 0.34/1.04      | X2 != X0
% 0.34/1.04      | k1_relat_1(X2) != X1
% 0.34/1.04      | k2_relat_1(X2) != k1_xboole_0
% 0.34/1.04      | k1_xboole_0 = X1
% 0.34/1.04      | k1_xboole_0 = X0 ),
% 0.34/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_435,plain,
% 0.34/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 0.34/1.04      | ~ v1_relat_1(X0)
% 0.34/1.04      | ~ v1_funct_1(X0)
% 0.34/1.04      | k2_relat_1(X0) != k1_xboole_0
% 0.34/1.04      | k1_xboole_0 = X0
% 0.34/1.04      | k1_xboole_0 = k1_relat_1(X0) ),
% 0.34/1.04      inference(unflattening,[status(thm)],[c_434]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_451,plain,
% 0.34/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 0.34/1.04      | ~ v1_funct_1(X0)
% 0.34/1.04      | k2_relat_1(X0) != k1_xboole_0
% 0.34/1.04      | k1_xboole_0 = X0
% 0.34/1.04      | k1_xboole_0 = k1_relat_1(X0) ),
% 0.34/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_435,c_13]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1552,plain,
% 0.34/1.04      ( k2_relat_1(X0) != k1_xboole_0
% 0.34/1.04      | k1_xboole_0 = X0
% 0.34/1.04      | k1_xboole_0 = k1_relat_1(X0)
% 0.34/1.04      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
% 0.34/1.04      | v1_funct_1(X0) != iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_4,plain,
% 0.34/1.04      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 0.34/1.04      inference(cnf_transformation,[],[f71]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_1707,plain,
% 0.34/1.04      ( k1_relat_1(X0) = k1_xboole_0
% 0.34/1.04      | k2_relat_1(X0) != k1_xboole_0
% 0.34/1.04      | k1_xboole_0 = X0
% 0.34/1.04      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 0.34/1.04      | v1_funct_1(X0) != iProver_top ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_1552,c_4]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_4849,plain,
% 0.34/1.04      ( k1_relat_1(sK2) = k1_xboole_0
% 0.34/1.04      | sK2 = k1_xboole_0
% 0.34/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 0.34/1.04      | v1_funct_1(sK2) != iProver_top ),
% 0.34/1.04      inference(superposition,[status(thm)],[c_3771,c_1707]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3,plain,
% 0.34/1.04      ( r1_tarski(k1_xboole_0,X0) ),
% 0.34/1.04      inference(cnf_transformation,[],[f40]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2083,plain,
% 0.34/1.04      ( r1_tarski(k1_xboole_0,sK2) ),
% 0.34/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2086,plain,
% 0.34/1.04      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_2083]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_0,plain,
% 0.34/1.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 0.34/1.04      inference(cnf_transformation,[],[f39]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2091,plain,
% 0.34/1.04      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 0.34/1.04      inference(instantiation,[status(thm)],[c_0]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2092,plain,
% 0.34/1.04      ( sK2 = X0
% 0.34/1.04      | r1_tarski(X0,sK2) != iProver_top
% 0.34/1.04      | r1_tarski(sK2,X0) != iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_2091]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2094,plain,
% 0.34/1.04      ( sK2 = k1_xboole_0
% 0.34/1.04      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 0.34/1.04      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 0.34/1.04      inference(instantiation,[status(thm)],[c_2092]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_8,plain,
% 0.34/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 0.34/1.04      inference(cnf_transformation,[],[f44]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2413,plain,
% 0.34/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(sK2,X0) ),
% 0.34/1.04      inference(instantiation,[status(thm)],[c_8]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2414,plain,
% 0.34/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 0.34/1.04      | r1_tarski(sK2,X0) = iProver_top ),
% 0.34/1.04      inference(predicate_to_equality,[status(thm)],[c_2413]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2416,plain,
% 0.34/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 0.34/1.04      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 0.34/1.04      inference(instantiation,[status(thm)],[c_2414]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3780,plain,
% 0.34/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_3760,c_1557]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3785,plain,
% 0.34/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_3780,c_4]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_5196,plain,
% 0.34/1.04      ( sK2 = k1_xboole_0 ),
% 0.34/1.04      inference(global_propositional_subsumption,
% 0.34/1.04                [status(thm)],
% 0.34/1.04                [c_4849,c_2086,c_2094,c_2416,c_3785]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_7323,plain,
% 0.34/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 0.34/1.04      inference(light_normalisation,[status(thm)],[c_3851,c_5196]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_2983,plain,
% 0.34/1.04      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 0.34/1.04      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 0.34/1.04      inference(superposition,[status(thm)],[c_5,c_1560]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_4190,plain,
% 0.34/1.04      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 0.34/1.04      inference(superposition,[status(thm)],[c_3848,c_2983]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_3770,plain,
% 0.34/1.04      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_3760,c_2515]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_4204,plain,
% 0.34/1.04      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0 ),
% 0.34/1.04      inference(light_normalisation,[status(thm)],[c_4190,c_3770]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_6170,plain,
% 0.34/1.04      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 0.34/1.04      inference(light_normalisation,[status(thm)],[c_4204,c_5196]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_7324,plain,
% 0.34/1.04      ( k1_xboole_0 != k1_xboole_0 ),
% 0.34/1.04      inference(demodulation,[status(thm)],[c_7323,c_6170]) ).
% 0.34/1.04  
% 0.34/1.04  cnf(c_7325,plain,
% 0.34/1.04      ( $false ),
% 0.34/1.04      inference(equality_resolution_simp,[status(thm)],[c_7324]) ).
% 0.34/1.04  
% 0.34/1.04  
% 0.34/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.34/1.04  
% 0.34/1.04  ------                               Statistics
% 0.34/1.04  
% 0.34/1.04  ------ General
% 0.34/1.04  
% 0.34/1.04  abstr_ref_over_cycles:                  0
% 0.34/1.04  abstr_ref_under_cycles:                 0
% 0.34/1.04  gc_basic_clause_elim:                   0
% 0.34/1.04  forced_gc_time:                         0
% 0.34/1.04  parsing_time:                           0.015
% 0.34/1.04  unif_index_cands_time:                  0.
% 0.34/1.04  unif_index_add_time:                    0.
% 0.34/1.04  orderings_time:                         0.
% 0.34/1.04  out_proof_time:                         0.01
% 0.34/1.04  total_time:                             0.193
% 0.34/1.04  num_of_symbols:                         48
% 0.34/1.04  num_of_terms:                           5958
% 0.34/1.04  
% 0.34/1.04  ------ Preprocessing
% 0.34/1.04  
% 0.34/1.04  num_of_splits:                          0
% 0.34/1.04  num_of_split_atoms:                     0
% 0.34/1.04  num_of_reused_defs:                     0
% 0.34/1.04  num_eq_ax_congr_red:                    5
% 0.34/1.04  num_of_sem_filtered_clauses:            1
% 0.34/1.04  num_of_subtypes:                        0
% 0.34/1.04  monotx_restored_types:                  0
% 0.34/1.04  sat_num_of_epr_types:                   0
% 0.34/1.04  sat_num_of_non_cyclic_types:            0
% 0.34/1.04  sat_guarded_non_collapsed_types:        0
% 0.34/1.04  num_pure_diseq_elim:                    0
% 0.34/1.04  simp_replaced_by:                       0
% 0.34/1.04  res_preprocessed:                       150
% 0.34/1.04  prep_upred:                             0
% 0.34/1.04  prep_unflattend:                        43
% 0.34/1.04  smt_new_axioms:                         0
% 0.34/1.04  pred_elim_cands:                        4
% 0.34/1.04  pred_elim:                              2
% 0.34/1.04  pred_elim_cl:                           -1
% 0.34/1.04  pred_elim_cycles:                       4
% 0.34/1.04  merged_defs:                            8
% 0.34/1.04  merged_defs_ncl:                        0
% 0.34/1.04  bin_hyper_res:                          8
% 0.34/1.04  prep_cycles:                            4
% 0.34/1.04  pred_elim_time:                         0.007
% 0.34/1.04  splitting_time:                         0.
% 0.34/1.04  sem_filter_time:                        0.
% 0.34/1.04  monotx_time:                            0.
% 0.34/1.04  subtype_inf_time:                       0.
% 0.34/1.04  
% 0.34/1.04  ------ Problem properties
% 0.34/1.04  
% 0.34/1.04  clauses:                                31
% 0.34/1.04  conjectures:                            3
% 0.34/1.04  epr:                                    4
% 0.34/1.04  horn:                                   26
% 0.34/1.04  ground:                                 13
% 0.34/1.04  unary:                                  7
% 0.34/1.04  binary:                                 9
% 0.34/1.04  lits:                                   83
% 0.34/1.04  lits_eq:                                36
% 0.34/1.04  fd_pure:                                0
% 0.34/1.04  fd_pseudo:                              0
% 0.34/1.04  fd_cond:                                2
% 0.34/1.04  fd_pseudo_cond:                         1
% 0.34/1.04  ac_symbols:                             0
% 0.34/1.04  
% 0.34/1.04  ------ Propositional Solver
% 0.34/1.04  
% 0.34/1.04  prop_solver_calls:                      29
% 0.34/1.04  prop_fast_solver_calls:                 1124
% 0.34/1.04  smt_solver_calls:                       0
% 0.34/1.04  smt_fast_solver_calls:                  0
% 0.34/1.04  prop_num_of_clauses:                    2596
% 0.34/1.04  prop_preprocess_simplified:             7525
% 0.34/1.04  prop_fo_subsumed:                       31
% 0.34/1.04  prop_solver_time:                       0.
% 0.34/1.04  smt_solver_time:                        0.
% 0.34/1.04  smt_fast_solver_time:                   0.
% 0.34/1.04  prop_fast_solver_time:                  0.
% 0.34/1.04  prop_unsat_core_time:                   0.
% 0.34/1.04  
% 0.34/1.04  ------ QBF
% 0.34/1.04  
% 0.34/1.04  qbf_q_res:                              0
% 0.34/1.04  qbf_num_tautologies:                    0
% 0.34/1.04  qbf_prep_cycles:                        0
% 0.34/1.04  
% 0.34/1.04  ------ BMC1
% 0.34/1.04  
% 0.34/1.04  bmc1_current_bound:                     -1
% 0.34/1.04  bmc1_last_solved_bound:                 -1
% 0.34/1.04  bmc1_unsat_core_size:                   -1
% 0.34/1.04  bmc1_unsat_core_parents_size:           -1
% 0.34/1.04  bmc1_merge_next_fun:                    0
% 0.34/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.34/1.04  
% 0.34/1.04  ------ Instantiation
% 0.34/1.04  
% 0.34/1.04  inst_num_of_clauses:                    946
% 0.34/1.04  inst_num_in_passive:                    322
% 0.34/1.04  inst_num_in_active:                     432
% 0.34/1.04  inst_num_in_unprocessed:                192
% 0.34/1.04  inst_num_of_loops:                      570
% 0.34/1.04  inst_num_of_learning_restarts:          0
% 0.34/1.04  inst_num_moves_active_passive:          135
% 0.34/1.04  inst_lit_activity:                      0
% 0.34/1.04  inst_lit_activity_moves:                0
% 0.34/1.04  inst_num_tautologies:                   0
% 0.34/1.04  inst_num_prop_implied:                  0
% 0.34/1.04  inst_num_existing_simplified:           0
% 0.34/1.04  inst_num_eq_res_simplified:             0
% 0.34/1.04  inst_num_child_elim:                    0
% 0.34/1.04  inst_num_of_dismatching_blockings:      237
% 0.34/1.04  inst_num_of_non_proper_insts:           849
% 0.34/1.04  inst_num_of_duplicates:                 0
% 0.34/1.04  inst_inst_num_from_inst_to_res:         0
% 0.34/1.04  inst_dismatching_checking_time:         0.
% 0.34/1.04  
% 0.34/1.04  ------ Resolution
% 0.34/1.04  
% 0.34/1.04  res_num_of_clauses:                     0
% 0.34/1.04  res_num_in_passive:                     0
% 0.34/1.04  res_num_in_active:                      0
% 0.34/1.04  res_num_of_loops:                       154
% 0.34/1.04  res_forward_subset_subsumed:            57
% 0.34/1.04  res_backward_subset_subsumed:           0
% 0.34/1.04  res_forward_subsumed:                   0
% 0.34/1.04  res_backward_subsumed:                  0
% 0.34/1.04  res_forward_subsumption_resolution:     3
% 0.34/1.04  res_backward_subsumption_resolution:    0
% 0.34/1.04  res_clause_to_clause_subsumption:       589
% 0.34/1.04  res_orphan_elimination:                 0
% 0.34/1.04  res_tautology_del:                      98
% 0.34/1.04  res_num_eq_res_simplified:              0
% 0.34/1.04  res_num_sel_changes:                    0
% 0.34/1.04  res_moves_from_active_to_pass:          0
% 0.34/1.04  
% 0.34/1.04  ------ Superposition
% 0.34/1.04  
% 0.34/1.04  sup_time_total:                         0.
% 0.34/1.04  sup_time_generating:                    0.
% 0.34/1.04  sup_time_sim_full:                      0.
% 0.34/1.04  sup_time_sim_immed:                     0.
% 0.34/1.04  
% 0.34/1.04  sup_num_of_clauses:                     148
% 0.34/1.04  sup_num_in_active:                      71
% 0.34/1.04  sup_num_in_passive:                     77
% 0.34/1.04  sup_num_of_loops:                       113
% 0.34/1.04  sup_fw_superposition:                   131
% 0.34/1.04  sup_bw_superposition:                   108
% 0.34/1.04  sup_immediate_simplified:               113
% 0.34/1.04  sup_given_eliminated:                   0
% 0.34/1.04  comparisons_done:                       0
% 0.34/1.04  comparisons_avoided:                    10
% 0.34/1.04  
% 0.34/1.04  ------ Simplifications
% 0.34/1.04  
% 0.34/1.04  
% 0.34/1.04  sim_fw_subset_subsumed:                 21
% 0.34/1.04  sim_bw_subset_subsumed:                 8
% 0.34/1.04  sim_fw_subsumed:                        9
% 0.34/1.04  sim_bw_subsumed:                        2
% 0.34/1.04  sim_fw_subsumption_res:                 2
% 0.34/1.04  sim_bw_subsumption_res:                 3
% 0.34/1.04  sim_tautology_del:                      3
% 0.34/1.04  sim_eq_tautology_del:                   10
% 0.34/1.04  sim_eq_res_simp:                        3
% 0.34/1.04  sim_fw_demodulated:                     70
% 0.34/1.04  sim_bw_demodulated:                     41
% 0.34/1.04  sim_light_normalised:                   44
% 0.34/1.04  sim_joinable_taut:                      0
% 0.34/1.04  sim_joinable_simp:                      0
% 0.34/1.04  sim_ac_normalised:                      0
% 0.34/1.04  sim_smt_subsumption:                    0
% 0.34/1.04  
%------------------------------------------------------------------------------

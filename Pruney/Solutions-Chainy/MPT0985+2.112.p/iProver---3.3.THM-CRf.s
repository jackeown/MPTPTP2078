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
% DateTime   : Thu Dec  3 12:02:43 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  173 (9373 expanded)
%              Number of clauses        :  111 (2791 expanded)
%              Number of leaves         :   13 (1855 expanded)
%              Depth                    :   27
%              Number of atoms          :  529 (52061 expanded)
%              Number of equality atoms :  278 (10247 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f31])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f19])).

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
    inference(flattening,[],[f35])).

fof(f49,plain,
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

fof(f50,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f49])).

fof(f89,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f71,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f100,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f61])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_752,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_41])).

cnf(c_753,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_752])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_755,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_753,c_40])).

cnf(c_1702,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1708,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3711,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1702,c_1708])).

cnf(c_4040,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_755,c_3711])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1707,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3180,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1702,c_1707])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3196,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3180,c_38])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_37,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_776,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(X0) != sK3
    | k2_relat_1(X0) != sK2
    | k2_funct_1(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_37])).

cnf(c_777,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(unflattening,[status(thm)],[c_776])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_789,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_777,c_21])).

cnf(c_1688,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_519,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_39])).

cnf(c_520,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_522,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_42])).

cnf(c_1698,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_2025,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2029,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1698,c_42,c_40,c_520,c_2025])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_505,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_39])).

cnf(c_506,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_508,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_42])).

cnf(c_1699,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_2033,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1699,c_42,c_40,c_506,c_2025])).

cnf(c_2101,plain,
    ( k1_relat_1(sK4) != sK2
    | k2_relat_1(sK4) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1688,c_2029,c_2033])).

cnf(c_3247,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3196,c_2101])).

cnf(c_3251,plain,
    ( k1_relat_1(sK4) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3247])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2026,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2025])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2171,plain,
    ( ~ v1_relat_1(sK4)
    | v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2172,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2171])).

cnf(c_4242,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | k1_relat_1(sK4) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3251,c_43,c_45,c_2026,c_2101,c_2172,c_3196])).

cnf(c_4243,plain,
    ( k1_relat_1(sK4) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4242])).

cnf(c_4248,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_4243])).

cnf(c_34,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1703,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2805,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2029,c_1703])).

cnf(c_2816,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2805,c_2033])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2170,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2174,plain,
    ( v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2170])).

cnf(c_2985,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2816,c_43,c_45,c_2026,c_2172,c_2174])).

cnf(c_3246,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3196,c_2985])).

cnf(c_4121,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4040,c_3246])).

cnf(c_4280,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4248,c_4121])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != X1
    | sK3 != k1_xboole_0
    | sK4 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_41])).

cnf(c_615,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_1695,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1839,plain,
    ( sK2 = k1_xboole_0
    | sK3 != k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1695,c_8])).

cnf(c_4296,plain,
    ( sK2 = k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4280,c_1839])).

cnf(c_4347,plain,
    ( sK2 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4296])).

cnf(c_4304,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4280,c_1702])).

cnf(c_4309,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4304,c_8])).

cnf(c_4351,plain,
    ( sK2 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4347,c_4309])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2733,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2734,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2733])).

cnf(c_2736,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2734])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3409,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3412,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3409])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3947,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3948,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3947])).

cnf(c_3950,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3948])).

cnf(c_5298,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4351,c_2736,c_3412,c_3950,c_4309])).

cnf(c_4290,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4280,c_3246])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4367,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4290,c_9])).

cnf(c_5311,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5298,c_4367])).

cnf(c_3715,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1708])).

cnf(c_5932,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_5311,c_3715])).

cnf(c_3248,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3196,c_2033])).

cnf(c_4293,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4280,c_3248])).

cnf(c_5315,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5298,c_4293])).

cnf(c_5943,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5932,c_5315])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_669,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK4) != X0
    | sK2 != X1
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_670,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_1693,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_1912,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1693,c_9])).

cnf(c_2333,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | sK3 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1912,c_43,c_45,c_2026,c_2172])).

cnf(c_2334,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2333])).

cnf(c_4298,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4280,c_2334])).

cnf(c_4340,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4298])).

cnf(c_4344,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4340,c_9])).

cnf(c_4371,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4367,c_4344])).

cnf(c_5945,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4371,c_5298])).

cnf(c_6340,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5943,c_5945])).

cnf(c_122,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_121,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6340,c_122,c_121])).

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
% 0.14/0.34  % DateTime   : Tue Dec  1 12:19:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.11/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/0.98  
% 3.11/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.11/0.98  
% 3.11/0.98  ------  iProver source info
% 3.11/0.98  
% 3.11/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.11/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.11/0.98  git: non_committed_changes: false
% 3.11/0.98  git: last_make_outside_of_git: false
% 3.11/0.98  
% 3.11/0.98  ------ 
% 3.11/0.98  
% 3.11/0.98  ------ Input Options
% 3.11/0.98  
% 3.11/0.98  --out_options                           all
% 3.11/0.98  --tptp_safe_out                         true
% 3.11/0.98  --problem_path                          ""
% 3.11/0.98  --include_path                          ""
% 3.11/0.98  --clausifier                            res/vclausify_rel
% 3.11/0.98  --clausifier_options                    --mode clausify
% 3.11/0.98  --stdin                                 false
% 3.11/0.98  --stats_out                             all
% 3.11/0.98  
% 3.11/0.98  ------ General Options
% 3.11/0.98  
% 3.11/0.98  --fof                                   false
% 3.11/0.98  --time_out_real                         305.
% 3.11/0.98  --time_out_virtual                      -1.
% 3.11/0.98  --symbol_type_check                     false
% 3.11/0.98  --clausify_out                          false
% 3.11/0.98  --sig_cnt_out                           false
% 3.11/0.98  --trig_cnt_out                          false
% 3.11/0.98  --trig_cnt_out_tolerance                1.
% 3.11/0.98  --trig_cnt_out_sk_spl                   false
% 3.11/0.98  --abstr_cl_out                          false
% 3.11/0.98  
% 3.11/0.98  ------ Global Options
% 3.11/0.98  
% 3.11/0.98  --schedule                              default
% 3.11/0.98  --add_important_lit                     false
% 3.11/0.98  --prop_solver_per_cl                    1000
% 3.11/0.98  --min_unsat_core                        false
% 3.11/0.98  --soft_assumptions                      false
% 3.11/0.98  --soft_lemma_size                       3
% 3.11/0.98  --prop_impl_unit_size                   0
% 3.11/0.98  --prop_impl_unit                        []
% 3.11/0.98  --share_sel_clauses                     true
% 3.11/0.98  --reset_solvers                         false
% 3.11/0.98  --bc_imp_inh                            [conj_cone]
% 3.11/0.98  --conj_cone_tolerance                   3.
% 3.11/0.98  --extra_neg_conj                        none
% 3.11/0.98  --large_theory_mode                     true
% 3.11/0.98  --prolific_symb_bound                   200
% 3.11/0.98  --lt_threshold                          2000
% 3.11/0.98  --clause_weak_htbl                      true
% 3.11/0.98  --gc_record_bc_elim                     false
% 3.11/0.98  
% 3.11/0.98  ------ Preprocessing Options
% 3.11/0.98  
% 3.11/0.98  --preprocessing_flag                    true
% 3.11/0.98  --time_out_prep_mult                    0.1
% 3.11/0.98  --splitting_mode                        input
% 3.11/0.98  --splitting_grd                         true
% 3.11/0.98  --splitting_cvd                         false
% 3.11/0.98  --splitting_cvd_svl                     false
% 3.11/0.98  --splitting_nvd                         32
% 3.11/0.98  --sub_typing                            true
% 3.11/0.98  --prep_gs_sim                           true
% 3.11/0.98  --prep_unflatten                        true
% 3.11/0.98  --prep_res_sim                          true
% 3.11/0.98  --prep_upred                            true
% 3.11/0.98  --prep_sem_filter                       exhaustive
% 3.11/0.98  --prep_sem_filter_out                   false
% 3.11/0.98  --pred_elim                             true
% 3.11/0.98  --res_sim_input                         true
% 3.11/0.98  --eq_ax_congr_red                       true
% 3.11/0.98  --pure_diseq_elim                       true
% 3.11/0.98  --brand_transform                       false
% 3.11/0.98  --non_eq_to_eq                          false
% 3.11/0.98  --prep_def_merge                        true
% 3.11/0.98  --prep_def_merge_prop_impl              false
% 3.11/0.98  --prep_def_merge_mbd                    true
% 3.11/0.98  --prep_def_merge_tr_red                 false
% 3.11/0.98  --prep_def_merge_tr_cl                  false
% 3.11/0.98  --smt_preprocessing                     true
% 3.11/0.98  --smt_ac_axioms                         fast
% 3.11/0.98  --preprocessed_out                      false
% 3.11/0.98  --preprocessed_stats                    false
% 3.11/0.98  
% 3.11/0.98  ------ Abstraction refinement Options
% 3.11/0.98  
% 3.11/0.98  --abstr_ref                             []
% 3.11/0.98  --abstr_ref_prep                        false
% 3.11/0.98  --abstr_ref_until_sat                   false
% 3.11/0.98  --abstr_ref_sig_restrict                funpre
% 3.11/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.98  --abstr_ref_under                       []
% 3.11/0.98  
% 3.11/0.98  ------ SAT Options
% 3.11/0.98  
% 3.11/0.98  --sat_mode                              false
% 3.11/0.98  --sat_fm_restart_options                ""
% 3.11/0.98  --sat_gr_def                            false
% 3.11/0.98  --sat_epr_types                         true
% 3.11/0.98  --sat_non_cyclic_types                  false
% 3.11/0.98  --sat_finite_models                     false
% 3.11/0.98  --sat_fm_lemmas                         false
% 3.11/0.98  --sat_fm_prep                           false
% 3.11/0.98  --sat_fm_uc_incr                        true
% 3.11/0.98  --sat_out_model                         small
% 3.11/0.98  --sat_out_clauses                       false
% 3.11/0.98  
% 3.11/0.98  ------ QBF Options
% 3.11/0.98  
% 3.11/0.98  --qbf_mode                              false
% 3.11/0.98  --qbf_elim_univ                         false
% 3.11/0.98  --qbf_dom_inst                          none
% 3.11/0.98  --qbf_dom_pre_inst                      false
% 3.11/0.98  --qbf_sk_in                             false
% 3.11/0.98  --qbf_pred_elim                         true
% 3.11/0.98  --qbf_split                             512
% 3.11/0.98  
% 3.11/0.98  ------ BMC1 Options
% 3.11/0.98  
% 3.11/0.98  --bmc1_incremental                      false
% 3.11/0.98  --bmc1_axioms                           reachable_all
% 3.11/0.98  --bmc1_min_bound                        0
% 3.11/0.98  --bmc1_max_bound                        -1
% 3.11/0.98  --bmc1_max_bound_default                -1
% 3.11/0.98  --bmc1_symbol_reachability              true
% 3.11/0.98  --bmc1_property_lemmas                  false
% 3.11/0.98  --bmc1_k_induction                      false
% 3.11/0.98  --bmc1_non_equiv_states                 false
% 3.11/0.98  --bmc1_deadlock                         false
% 3.11/0.98  --bmc1_ucm                              false
% 3.11/0.98  --bmc1_add_unsat_core                   none
% 3.11/0.98  --bmc1_unsat_core_children              false
% 3.11/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.98  --bmc1_out_stat                         full
% 3.11/0.98  --bmc1_ground_init                      false
% 3.11/0.98  --bmc1_pre_inst_next_state              false
% 3.11/0.98  --bmc1_pre_inst_state                   false
% 3.11/0.98  --bmc1_pre_inst_reach_state             false
% 3.11/0.98  --bmc1_out_unsat_core                   false
% 3.11/0.98  --bmc1_aig_witness_out                  false
% 3.11/0.98  --bmc1_verbose                          false
% 3.11/0.98  --bmc1_dump_clauses_tptp                false
% 3.11/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.98  --bmc1_dump_file                        -
% 3.11/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.98  --bmc1_ucm_extend_mode                  1
% 3.11/0.98  --bmc1_ucm_init_mode                    2
% 3.11/0.98  --bmc1_ucm_cone_mode                    none
% 3.11/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.98  --bmc1_ucm_relax_model                  4
% 3.11/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.98  --bmc1_ucm_layered_model                none
% 3.11/0.98  --bmc1_ucm_max_lemma_size               10
% 3.11/0.98  
% 3.11/0.98  ------ AIG Options
% 3.11/0.98  
% 3.11/0.98  --aig_mode                              false
% 3.11/0.98  
% 3.11/0.98  ------ Instantiation Options
% 3.11/0.98  
% 3.11/0.98  --instantiation_flag                    true
% 3.11/0.98  --inst_sos_flag                         false
% 3.11/0.98  --inst_sos_phase                        true
% 3.11/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.98  --inst_lit_sel_side                     num_symb
% 3.11/0.98  --inst_solver_per_active                1400
% 3.11/0.98  --inst_solver_calls_frac                1.
% 3.11/0.98  --inst_passive_queue_type               priority_queues
% 3.11/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.98  --inst_passive_queues_freq              [25;2]
% 3.11/0.98  --inst_dismatching                      true
% 3.11/0.98  --inst_eager_unprocessed_to_passive     true
% 3.11/0.98  --inst_prop_sim_given                   true
% 3.11/0.98  --inst_prop_sim_new                     false
% 3.11/0.98  --inst_subs_new                         false
% 3.11/0.98  --inst_eq_res_simp                      false
% 3.11/0.98  --inst_subs_given                       false
% 3.11/0.98  --inst_orphan_elimination               true
% 3.11/0.98  --inst_learning_loop_flag               true
% 3.11/0.98  --inst_learning_start                   3000
% 3.11/0.98  --inst_learning_factor                  2
% 3.11/0.98  --inst_start_prop_sim_after_learn       3
% 3.11/0.98  --inst_sel_renew                        solver
% 3.11/0.98  --inst_lit_activity_flag                true
% 3.11/0.98  --inst_restr_to_given                   false
% 3.11/0.98  --inst_activity_threshold               500
% 3.11/0.98  --inst_out_proof                        true
% 3.11/0.98  
% 3.11/0.98  ------ Resolution Options
% 3.11/0.98  
% 3.11/0.98  --resolution_flag                       true
% 3.11/0.98  --res_lit_sel                           adaptive
% 3.11/0.98  --res_lit_sel_side                      none
% 3.11/0.98  --res_ordering                          kbo
% 3.11/0.98  --res_to_prop_solver                    active
% 3.11/0.98  --res_prop_simpl_new                    false
% 3.11/0.98  --res_prop_simpl_given                  true
% 3.11/0.98  --res_passive_queue_type                priority_queues
% 3.11/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.98  --res_passive_queues_freq               [15;5]
% 3.11/0.98  --res_forward_subs                      full
% 3.11/0.98  --res_backward_subs                     full
% 3.11/0.98  --res_forward_subs_resolution           true
% 3.11/0.98  --res_backward_subs_resolution          true
% 3.11/0.98  --res_orphan_elimination                true
% 3.11/0.98  --res_time_limit                        2.
% 3.11/0.98  --res_out_proof                         true
% 3.11/0.98  
% 3.11/0.98  ------ Superposition Options
% 3.11/0.98  
% 3.11/0.98  --superposition_flag                    true
% 3.11/0.98  --sup_passive_queue_type                priority_queues
% 3.11/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.98  --demod_completeness_check              fast
% 3.11/0.98  --demod_use_ground                      true
% 3.11/0.98  --sup_to_prop_solver                    passive
% 3.11/0.98  --sup_prop_simpl_new                    true
% 3.11/0.98  --sup_prop_simpl_given                  true
% 3.11/0.98  --sup_fun_splitting                     false
% 3.11/0.98  --sup_smt_interval                      50000
% 3.11/0.98  
% 3.11/0.98  ------ Superposition Simplification Setup
% 3.11/0.98  
% 3.11/0.98  --sup_indices_passive                   []
% 3.11/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.98  --sup_full_bw                           [BwDemod]
% 3.11/0.98  --sup_immed_triv                        [TrivRules]
% 3.11/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.98  --sup_immed_bw_main                     []
% 3.11/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.98  
% 3.11/0.98  ------ Combination Options
% 3.11/0.98  
% 3.11/0.98  --comb_res_mult                         3
% 3.11/0.98  --comb_sup_mult                         2
% 3.11/0.98  --comb_inst_mult                        10
% 3.11/0.98  
% 3.11/0.98  ------ Debug Options
% 3.11/0.98  
% 3.11/0.98  --dbg_backtrace                         false
% 3.11/0.98  --dbg_dump_prop_clauses                 false
% 3.11/0.98  --dbg_dump_prop_clauses_file            -
% 3.11/0.98  --dbg_out_stat                          false
% 3.11/0.98  ------ Parsing...
% 3.11/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.11/0.98  
% 3.11/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.11/0.98  
% 3.11/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.11/0.98  
% 3.11/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.11/0.98  ------ Proving...
% 3.11/0.98  ------ Problem Properties 
% 3.11/0.98  
% 3.11/0.98  
% 3.11/0.98  clauses                                 44
% 3.11/0.98  conjectures                             3
% 3.11/0.98  EPR                                     6
% 3.11/0.98  Horn                                    36
% 3.11/0.98  unary                                   14
% 3.11/0.98  binary                                  13
% 3.11/0.98  lits                                    104
% 3.11/0.98  lits eq                                 43
% 3.11/0.98  fd_pure                                 0
% 3.11/0.98  fd_pseudo                               0
% 3.11/0.98  fd_cond                                 3
% 3.11/0.98  fd_pseudo_cond                          1
% 3.11/0.98  AC symbols                              0
% 3.11/0.98  
% 3.11/0.98  ------ Schedule dynamic 5 is on 
% 3.11/0.98  
% 3.11/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.11/0.98  
% 3.11/0.98  
% 3.11/0.98  ------ 
% 3.11/0.98  Current options:
% 3.11/0.98  ------ 
% 3.11/0.98  
% 3.11/0.98  ------ Input Options
% 3.11/0.98  
% 3.11/0.98  --out_options                           all
% 3.11/0.98  --tptp_safe_out                         true
% 3.11/0.98  --problem_path                          ""
% 3.11/0.98  --include_path                          ""
% 3.11/0.98  --clausifier                            res/vclausify_rel
% 3.11/0.98  --clausifier_options                    --mode clausify
% 3.11/0.98  --stdin                                 false
% 3.11/0.98  --stats_out                             all
% 3.11/0.98  
% 3.11/0.98  ------ General Options
% 3.11/0.98  
% 3.11/0.98  --fof                                   false
% 3.11/0.98  --time_out_real                         305.
% 3.11/0.98  --time_out_virtual                      -1.
% 3.11/0.98  --symbol_type_check                     false
% 3.11/0.98  --clausify_out                          false
% 3.11/0.98  --sig_cnt_out                           false
% 3.11/0.98  --trig_cnt_out                          false
% 3.11/0.98  --trig_cnt_out_tolerance                1.
% 3.11/0.98  --trig_cnt_out_sk_spl                   false
% 3.11/0.98  --abstr_cl_out                          false
% 3.11/0.98  
% 3.11/0.98  ------ Global Options
% 3.11/0.98  
% 3.11/0.98  --schedule                              default
% 3.11/0.98  --add_important_lit                     false
% 3.11/0.98  --prop_solver_per_cl                    1000
% 3.11/0.98  --min_unsat_core                        false
% 3.11/0.98  --soft_assumptions                      false
% 3.11/0.98  --soft_lemma_size                       3
% 3.11/0.98  --prop_impl_unit_size                   0
% 3.11/0.98  --prop_impl_unit                        []
% 3.11/0.98  --share_sel_clauses                     true
% 3.11/0.98  --reset_solvers                         false
% 3.11/0.98  --bc_imp_inh                            [conj_cone]
% 3.11/0.98  --conj_cone_tolerance                   3.
% 3.11/0.98  --extra_neg_conj                        none
% 3.11/0.98  --large_theory_mode                     true
% 3.11/0.98  --prolific_symb_bound                   200
% 3.11/0.98  --lt_threshold                          2000
% 3.11/0.98  --clause_weak_htbl                      true
% 3.11/0.98  --gc_record_bc_elim                     false
% 3.11/0.98  
% 3.11/0.98  ------ Preprocessing Options
% 3.11/0.98  
% 3.11/0.98  --preprocessing_flag                    true
% 3.11/0.98  --time_out_prep_mult                    0.1
% 3.11/0.98  --splitting_mode                        input
% 3.11/0.98  --splitting_grd                         true
% 3.11/0.98  --splitting_cvd                         false
% 3.11/0.98  --splitting_cvd_svl                     false
% 3.11/0.98  --splitting_nvd                         32
% 3.11/0.98  --sub_typing                            true
% 3.11/0.98  --prep_gs_sim                           true
% 3.11/0.98  --prep_unflatten                        true
% 3.11/0.98  --prep_res_sim                          true
% 3.11/0.98  --prep_upred                            true
% 3.11/0.98  --prep_sem_filter                       exhaustive
% 3.11/0.98  --prep_sem_filter_out                   false
% 3.11/0.98  --pred_elim                             true
% 3.11/0.98  --res_sim_input                         true
% 3.11/0.98  --eq_ax_congr_red                       true
% 3.11/0.98  --pure_diseq_elim                       true
% 3.11/0.98  --brand_transform                       false
% 3.11/0.98  --non_eq_to_eq                          false
% 3.11/0.98  --prep_def_merge                        true
% 3.11/0.98  --prep_def_merge_prop_impl              false
% 3.11/0.98  --prep_def_merge_mbd                    true
% 3.11/0.98  --prep_def_merge_tr_red                 false
% 3.11/0.98  --prep_def_merge_tr_cl                  false
% 3.11/0.98  --smt_preprocessing                     true
% 3.11/0.98  --smt_ac_axioms                         fast
% 3.11/0.98  --preprocessed_out                      false
% 3.11/0.98  --preprocessed_stats                    false
% 3.11/0.98  
% 3.11/0.98  ------ Abstraction refinement Options
% 3.11/0.98  
% 3.11/0.98  --abstr_ref                             []
% 3.11/0.98  --abstr_ref_prep                        false
% 3.11/0.98  --abstr_ref_until_sat                   false
% 3.11/0.98  --abstr_ref_sig_restrict                funpre
% 3.11/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.98  --abstr_ref_under                       []
% 3.11/0.98  
% 3.11/0.98  ------ SAT Options
% 3.11/0.98  
% 3.11/0.98  --sat_mode                              false
% 3.11/0.98  --sat_fm_restart_options                ""
% 3.11/0.98  --sat_gr_def                            false
% 3.11/0.98  --sat_epr_types                         true
% 3.11/0.98  --sat_non_cyclic_types                  false
% 3.11/0.98  --sat_finite_models                     false
% 3.11/0.98  --sat_fm_lemmas                         false
% 3.11/0.98  --sat_fm_prep                           false
% 3.11/0.98  --sat_fm_uc_incr                        true
% 3.11/0.98  --sat_out_model                         small
% 3.11/0.98  --sat_out_clauses                       false
% 3.11/0.98  
% 3.11/0.98  ------ QBF Options
% 3.11/0.98  
% 3.11/0.98  --qbf_mode                              false
% 3.11/0.98  --qbf_elim_univ                         false
% 3.11/0.98  --qbf_dom_inst                          none
% 3.11/0.98  --qbf_dom_pre_inst                      false
% 3.11/0.98  --qbf_sk_in                             false
% 3.11/0.98  --qbf_pred_elim                         true
% 3.11/0.98  --qbf_split                             512
% 3.11/0.98  
% 3.11/0.98  ------ BMC1 Options
% 3.11/0.98  
% 3.11/0.98  --bmc1_incremental                      false
% 3.11/0.98  --bmc1_axioms                           reachable_all
% 3.11/0.98  --bmc1_min_bound                        0
% 3.11/0.98  --bmc1_max_bound                        -1
% 3.11/0.98  --bmc1_max_bound_default                -1
% 3.11/0.98  --bmc1_symbol_reachability              true
% 3.11/0.98  --bmc1_property_lemmas                  false
% 3.11/0.98  --bmc1_k_induction                      false
% 3.11/0.98  --bmc1_non_equiv_states                 false
% 3.11/0.98  --bmc1_deadlock                         false
% 3.11/0.98  --bmc1_ucm                              false
% 3.11/0.98  --bmc1_add_unsat_core                   none
% 3.11/0.98  --bmc1_unsat_core_children              false
% 3.11/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.98  --bmc1_out_stat                         full
% 3.11/0.98  --bmc1_ground_init                      false
% 3.11/0.98  --bmc1_pre_inst_next_state              false
% 3.11/0.98  --bmc1_pre_inst_state                   false
% 3.11/0.98  --bmc1_pre_inst_reach_state             false
% 3.11/0.98  --bmc1_out_unsat_core                   false
% 3.11/0.98  --bmc1_aig_witness_out                  false
% 3.11/0.98  --bmc1_verbose                          false
% 3.11/0.98  --bmc1_dump_clauses_tptp                false
% 3.11/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.98  --bmc1_dump_file                        -
% 3.11/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.98  --bmc1_ucm_extend_mode                  1
% 3.11/0.98  --bmc1_ucm_init_mode                    2
% 3.11/0.98  --bmc1_ucm_cone_mode                    none
% 3.11/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.98  --bmc1_ucm_relax_model                  4
% 3.11/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.98  --bmc1_ucm_layered_model                none
% 3.11/0.98  --bmc1_ucm_max_lemma_size               10
% 3.11/0.98  
% 3.11/0.98  ------ AIG Options
% 3.11/0.98  
% 3.11/0.98  --aig_mode                              false
% 3.11/0.98  
% 3.11/0.98  ------ Instantiation Options
% 3.11/0.98  
% 3.11/0.98  --instantiation_flag                    true
% 3.11/0.98  --inst_sos_flag                         false
% 3.11/0.98  --inst_sos_phase                        true
% 3.11/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.98  --inst_lit_sel_side                     none
% 3.11/0.98  --inst_solver_per_active                1400
% 3.11/0.98  --inst_solver_calls_frac                1.
% 3.11/0.98  --inst_passive_queue_type               priority_queues
% 3.11/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.98  --inst_passive_queues_freq              [25;2]
% 3.11/0.98  --inst_dismatching                      true
% 3.11/0.98  --inst_eager_unprocessed_to_passive     true
% 3.11/0.98  --inst_prop_sim_given                   true
% 3.11/0.98  --inst_prop_sim_new                     false
% 3.11/0.98  --inst_subs_new                         false
% 3.11/0.98  --inst_eq_res_simp                      false
% 3.11/0.98  --inst_subs_given                       false
% 3.11/0.98  --inst_orphan_elimination               true
% 3.11/0.98  --inst_learning_loop_flag               true
% 3.11/0.98  --inst_learning_start                   3000
% 3.11/0.98  --inst_learning_factor                  2
% 3.11/0.98  --inst_start_prop_sim_after_learn       3
% 3.11/0.98  --inst_sel_renew                        solver
% 3.11/0.98  --inst_lit_activity_flag                true
% 3.11/0.98  --inst_restr_to_given                   false
% 3.11/0.98  --inst_activity_threshold               500
% 3.11/0.98  --inst_out_proof                        true
% 3.11/0.98  
% 3.11/0.98  ------ Resolution Options
% 3.11/0.98  
% 3.11/0.98  --resolution_flag                       false
% 3.11/0.98  --res_lit_sel                           adaptive
% 3.11/0.98  --res_lit_sel_side                      none
% 3.11/0.98  --res_ordering                          kbo
% 3.11/0.98  --res_to_prop_solver                    active
% 3.11/0.98  --res_prop_simpl_new                    false
% 3.11/0.98  --res_prop_simpl_given                  true
% 3.11/0.98  --res_passive_queue_type                priority_queues
% 3.11/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.98  --res_passive_queues_freq               [15;5]
% 3.11/0.98  --res_forward_subs                      full
% 3.11/0.98  --res_backward_subs                     full
% 3.11/0.98  --res_forward_subs_resolution           true
% 3.11/0.98  --res_backward_subs_resolution          true
% 3.11/0.98  --res_orphan_elimination                true
% 3.11/0.98  --res_time_limit                        2.
% 3.11/0.98  --res_out_proof                         true
% 3.11/0.98  
% 3.11/0.98  ------ Superposition Options
% 3.11/0.98  
% 3.11/0.98  --superposition_flag                    true
% 3.11/0.98  --sup_passive_queue_type                priority_queues
% 3.11/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.98  --demod_completeness_check              fast
% 3.11/0.98  --demod_use_ground                      true
% 3.11/0.98  --sup_to_prop_solver                    passive
% 3.11/0.98  --sup_prop_simpl_new                    true
% 3.11/0.98  --sup_prop_simpl_given                  true
% 3.11/0.98  --sup_fun_splitting                     false
% 3.11/0.98  --sup_smt_interval                      50000
% 3.11/0.98  
% 3.11/0.98  ------ Superposition Simplification Setup
% 3.11/0.98  
% 3.11/0.98  --sup_indices_passive                   []
% 3.11/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.98  --sup_full_bw                           [BwDemod]
% 3.11/0.98  --sup_immed_triv                        [TrivRules]
% 3.11/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ Proving...
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  % SZS status Theorem for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  fof(f15,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f31,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f15])).
% 3.11/0.99  
% 3.11/0.99  fof(f32,plain,(
% 3.11/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(flattening,[],[f31])).
% 3.11/0.99  
% 3.11/0.99  fof(f46,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(nnf_transformation,[],[f32])).
% 3.11/0.99  
% 3.11/0.99  fof(f75,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f18,conjecture,(
% 3.11/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f19,negated_conjecture,(
% 3.11/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.11/0.99    inference(negated_conjecture,[],[f18])).
% 3.11/0.99  
% 3.11/0.99  fof(f35,plain,(
% 3.11/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.11/0.99    inference(ennf_transformation,[],[f19])).
% 3.11/0.99  
% 3.11/0.99  fof(f36,plain,(
% 3.11/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.11/0.99    inference(flattening,[],[f35])).
% 3.11/0.99  
% 3.11/0.99  fof(f49,plain,(
% 3.11/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f50,plain,(
% 3.11/0.99    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f49])).
% 3.11/0.99  
% 3.11/0.99  fof(f89,plain,(
% 3.11/0.99    v1_funct_2(sK4,sK2,sK3)),
% 3.11/0.99    inference(cnf_transformation,[],[f50])).
% 3.11/0.99  
% 3.11/0.99  fof(f90,plain,(
% 3.11/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.11/0.99    inference(cnf_transformation,[],[f50])).
% 3.11/0.99  
% 3.11/0.99  fof(f13,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f29,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f13])).
% 3.11/0.99  
% 3.11/0.99  fof(f73,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f29])).
% 3.11/0.99  
% 3.11/0.99  fof(f14,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f30,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f14])).
% 3.11/0.99  
% 3.11/0.99  fof(f74,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f30])).
% 3.11/0.99  
% 3.11/0.99  fof(f92,plain,(
% 3.11/0.99    k2_relset_1(sK2,sK3,sK4) = sK3),
% 3.11/0.99    inference(cnf_transformation,[],[f50])).
% 3.11/0.99  
% 3.11/0.99  fof(f17,axiom,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f33,plain,(
% 3.11/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f17])).
% 3.11/0.99  
% 3.11/0.99  fof(f34,plain,(
% 3.11/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(flattening,[],[f33])).
% 3.11/0.99  
% 3.11/0.99  fof(f86,plain,(
% 3.11/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f34])).
% 3.11/0.99  
% 3.11/0.99  fof(f93,plain,(
% 3.11/0.99    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 3.11/0.99    inference(cnf_transformation,[],[f50])).
% 3.11/0.99  
% 3.11/0.99  fof(f12,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f28,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f12])).
% 3.11/0.99  
% 3.11/0.99  fof(f72,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f28])).
% 3.11/0.99  
% 3.11/0.99  fof(f11,axiom,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f26,plain,(
% 3.11/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f11])).
% 3.11/0.99  
% 3.11/0.99  fof(f27,plain,(
% 3.11/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(flattening,[],[f26])).
% 3.11/0.99  
% 3.11/0.99  fof(f71,plain,(
% 3.11/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f27])).
% 3.11/0.99  
% 3.11/0.99  fof(f91,plain,(
% 3.11/0.99    v2_funct_1(sK4)),
% 3.11/0.99    inference(cnf_transformation,[],[f50])).
% 3.11/0.99  
% 3.11/0.99  fof(f88,plain,(
% 3.11/0.99    v1_funct_1(sK4)),
% 3.11/0.99    inference(cnf_transformation,[],[f50])).
% 3.11/0.99  
% 3.11/0.99  fof(f70,plain,(
% 3.11/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f27])).
% 3.11/0.99  
% 3.11/0.99  fof(f9,axiom,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f24,plain,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f9])).
% 3.11/0.99  
% 3.11/0.99  fof(f25,plain,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(flattening,[],[f24])).
% 3.11/0.99  
% 3.11/0.99  fof(f67,plain,(
% 3.11/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f25])).
% 3.11/0.99  
% 3.11/0.99  fof(f87,plain,(
% 3.11/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f34])).
% 3.11/0.99  
% 3.11/0.99  fof(f66,plain,(
% 3.11/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f25])).
% 3.11/0.99  
% 3.11/0.99  fof(f79,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f100,plain,(
% 3.11/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.11/0.99    inference(equality_resolution,[],[f79])).
% 3.11/0.99  
% 3.11/0.99  fof(f5,axiom,(
% 3.11/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f43,plain,(
% 3.11/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.11/0.99    inference(nnf_transformation,[],[f5])).
% 3.11/0.99  
% 3.11/0.99  fof(f44,plain,(
% 3.11/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.11/0.99    inference(flattening,[],[f43])).
% 3.11/0.99  
% 3.11/0.99  fof(f61,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.11/0.99    inference(cnf_transformation,[],[f44])).
% 3.11/0.99  
% 3.11/0.99  fof(f96,plain,(
% 3.11/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.11/0.99    inference(equality_resolution,[],[f61])).
% 3.11/0.99  
% 3.11/0.99  fof(f3,axiom,(
% 3.11/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f41,plain,(
% 3.11/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.11/0.99    inference(nnf_transformation,[],[f3])).
% 3.11/0.99  
% 3.11/0.99  fof(f42,plain,(
% 3.11/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.11/0.99    inference(flattening,[],[f41])).
% 3.11/0.99  
% 3.11/0.99  fof(f57,plain,(
% 3.11/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f42])).
% 3.11/0.99  
% 3.11/0.99  fof(f4,axiom,(
% 3.11/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f58,plain,(
% 3.11/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f4])).
% 3.11/0.99  
% 3.11/0.99  fof(f6,axiom,(
% 3.11/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f45,plain,(
% 3.11/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.11/0.99    inference(nnf_transformation,[],[f6])).
% 3.11/0.99  
% 3.11/0.99  fof(f62,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f45])).
% 3.11/0.99  
% 3.11/0.99  fof(f60,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.11/0.99    inference(cnf_transformation,[],[f44])).
% 3.11/0.99  
% 3.11/0.99  fof(f97,plain,(
% 3.11/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.11/0.99    inference(equality_resolution,[],[f60])).
% 3.11/0.99  
% 3.11/0.99  fof(f78,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f101,plain,(
% 3.11/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.11/0.99    inference(equality_resolution,[],[f78])).
% 3.11/0.99  
% 3.11/0.99  fof(f59,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f44])).
% 3.11/0.99  
% 3.11/0.99  cnf(c_29,plain,
% 3.11/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.11/0.99      | k1_xboole_0 = X2 ),
% 3.11/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_41,negated_conjecture,
% 3.11/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.11/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_752,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.11/0.99      | sK2 != X1
% 3.11/0.99      | sK3 != X2
% 3.11/0.99      | sK4 != X0
% 3.11/0.99      | k1_xboole_0 = X2 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_41]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_753,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.11/0.99      | k1_relset_1(sK2,sK3,sK4) = sK2
% 3.11/0.99      | k1_xboole_0 = sK3 ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_752]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_40,negated_conjecture,
% 3.11/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.11/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_755,plain,
% 3.11/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_753,c_40]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1702,plain,
% 3.11/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_22,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1708,plain,
% 3.11/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.11/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3711,plain,
% 3.11/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_1702,c_1708]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4040,plain,
% 3.11/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_755,c_3711]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_23,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1707,plain,
% 3.11/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.11/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3180,plain,
% 3.11/0.99      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_1702,c_1707]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_38,negated_conjecture,
% 3.11/0.99      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 3.11/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3196,plain,
% 3.11/0.99      ( k2_relat_1(sK4) = sK3 ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_3180,c_38]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_35,plain,
% 3.11/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | ~ v1_funct_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_37,negated_conjecture,
% 3.11/0.99      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 3.11/0.99      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 3.11/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_776,plain,
% 3.11/0.99      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.11/0.99      | k1_relat_1(X0) != sK3
% 3.11/0.99      | k2_relat_1(X0) != sK2
% 3.11/0.99      | k2_funct_1(sK4) != X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_35,c_37]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_777,plain,
% 3.11/0.99      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.11/0.99      | ~ v1_relat_1(k2_funct_1(sK4))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.11/0.99      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.11/0.99      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_776]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_21,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | v1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_789,plain,
% 3.11/0.99      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.11/0.99      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.11/0.99      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 3.11/0.99      inference(forward_subsumption_resolution,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_777,c_21]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1688,plain,
% 3.11/0.99      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.11/0.99      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_19,plain,
% 3.11/0.99      ( ~ v2_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_39,negated_conjecture,
% 3.11/0.99      ( v2_funct_1(sK4) ),
% 3.11/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_519,plain,
% 3.11/0.99      ( ~ v1_relat_1(X0)
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.11/0.99      | sK4 != X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_39]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_520,plain,
% 3.11/0.99      ( ~ v1_relat_1(sK4)
% 3.11/0.99      | ~ v1_funct_1(sK4)
% 3.11/0.99      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_519]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_42,negated_conjecture,
% 3.11/0.99      ( v1_funct_1(sK4) ),
% 3.11/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_522,plain,
% 3.11/0.99      ( ~ v1_relat_1(sK4)
% 3.11/0.99      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_520,c_42]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1698,plain,
% 3.11/0.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 3.11/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2025,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.11/0.99      | v1_relat_1(sK4) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2029,plain,
% 3.11/0.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_1698,c_42,c_40,c_520,c_2025]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_20,plain,
% 3.11/0.99      ( ~ v2_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_505,plain,
% 3.11/0.99      ( ~ v1_relat_1(X0)
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.11/0.99      | sK4 != X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_39]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_506,plain,
% 3.11/0.99      ( ~ v1_relat_1(sK4)
% 3.11/0.99      | ~ v1_funct_1(sK4)
% 3.11/0.99      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_505]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_508,plain,
% 3.11/0.99      ( ~ v1_relat_1(sK4)
% 3.11/0.99      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_506,c_42]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1699,plain,
% 3.11/0.99      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 3.11/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2033,plain,
% 3.11/0.99      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_1699,c_42,c_40,c_506,c_2025]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2101,plain,
% 3.11/0.99      ( k1_relat_1(sK4) != sK2
% 3.11/0.99      | k2_relat_1(sK4) != sK3
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_1688,c_2029,c_2033]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3247,plain,
% 3.11/0.99      ( k1_relat_1(sK4) != sK2
% 3.11/0.99      | sK3 != sK3
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_3196,c_2101]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3251,plain,
% 3.11/0.99      ( k1_relat_1(sK4) != sK2
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.11/0.99      inference(equality_resolution_simp,[status(thm)],[c_3247]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_43,plain,
% 3.11/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_45,plain,
% 3.11/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2026,plain,
% 3.11/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.11/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2025]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_15,plain,
% 3.11/0.99      ( ~ v1_relat_1(X0)
% 3.11/0.99      | ~ v1_funct_1(X0)
% 3.11/0.99      | v1_funct_1(k2_funct_1(X0)) ),
% 3.11/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2171,plain,
% 3.11/0.99      ( ~ v1_relat_1(sK4)
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK4))
% 3.11/0.99      | ~ v1_funct_1(sK4) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2172,plain,
% 3.11/0.99      ( v1_relat_1(sK4) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 3.11/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2171]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4242,plain,
% 3.11/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/0.99      | k1_relat_1(sK4) != sK2 ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_3251,c_43,c_45,c_2026,c_2101,c_2172,c_3196]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4243,plain,
% 3.11/0.99      ( k1_relat_1(sK4) != sK2
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.11/0.99      inference(renaming,[status(thm)],[c_4242]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4248,plain,
% 3.11/0.99      ( sK3 = k1_xboole_0
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_4040,c_4243]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_34,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | ~ v1_funct_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1703,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.11/0.99      | v1_relat_1(X0) != iProver_top
% 3.11/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2805,plain,
% 3.11/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
% 3.11/0.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_2029,c_1703]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2816,plain,
% 3.11/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top
% 3.11/0.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_2805,c_2033]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_16,plain,
% 3.11/0.99      ( ~ v1_relat_1(X0)
% 3.11/0.99      | v1_relat_1(k2_funct_1(X0))
% 3.11/0.99      | ~ v1_funct_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2170,plain,
% 3.11/0.99      ( v1_relat_1(k2_funct_1(sK4))
% 3.11/0.99      | ~ v1_relat_1(sK4)
% 3.11/0.99      | ~ v1_funct_1(sK4) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2174,plain,
% 3.11/0.99      ( v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 3.11/0.99      | v1_relat_1(sK4) != iProver_top
% 3.11/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2170]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2985,plain,
% 3.11/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4)))) = iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_2816,c_43,c_45,c_2026,c_2172,c_2174]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3246,plain,
% 3.11/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_3196,c_2985]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4121,plain,
% 3.11/0.99      ( sK3 = k1_xboole_0
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_4040,c_3246]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4280,plain,
% 3.11/0.99      ( sK3 = k1_xboole_0 ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_4248,c_4121]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_25,plain,
% 3.11/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.11/0.99      | k1_xboole_0 = X1
% 3.11/0.99      | k1_xboole_0 = X0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_614,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.11/0.99      | sK2 != X1
% 3.11/0.99      | sK3 != k1_xboole_0
% 3.11/0.99      | sK4 != X0
% 3.11/0.99      | k1_xboole_0 = X1
% 3.11/0.99      | k1_xboole_0 = X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_41]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_615,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.11/0.99      | sK3 != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 = sK2
% 3.11/0.99      | k1_xboole_0 = sK4 ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_614]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1695,plain,
% 3.11/0.99      ( sK3 != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 = sK2
% 3.11/0.99      | k1_xboole_0 = sK4
% 3.11/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_8,plain,
% 3.11/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1839,plain,
% 3.11/0.99      ( sK2 = k1_xboole_0
% 3.11/0.99      | sK3 != k1_xboole_0
% 3.11/0.99      | sK4 = k1_xboole_0
% 3.11/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_1695,c_8]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4296,plain,
% 3.11/0.99      ( sK2 = k1_xboole_0
% 3.11/0.99      | sK4 = k1_xboole_0
% 3.11/0.99      | k1_xboole_0 != k1_xboole_0
% 3.11/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_4280,c_1839]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4347,plain,
% 3.11/0.99      ( sK2 = k1_xboole_0
% 3.11/0.99      | sK4 = k1_xboole_0
% 3.11/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(equality_resolution_simp,[status(thm)],[c_4296]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4304,plain,
% 3.11/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_4280,c_1702]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4309,plain,
% 3.11/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_4304,c_8]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4351,plain,
% 3.11/0.99      ( sK2 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.11/0.99      inference(forward_subsumption_resolution,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_4347,c_4309]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4,plain,
% 3.11/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2733,plain,
% 3.11/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2734,plain,
% 3.11/0.99      ( sK4 = X0
% 3.11/0.99      | r1_tarski(X0,sK4) != iProver_top
% 3.11/0.99      | r1_tarski(sK4,X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2733]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2736,plain,
% 3.11/0.99      ( sK4 = k1_xboole_0
% 3.11/0.99      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.11/0.99      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_2734]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_7,plain,
% 3.11/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3409,plain,
% 3.11/0.99      ( r1_tarski(k1_xboole_0,sK4) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3412,plain,
% 3.11/0.99      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_3409]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_12,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3947,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3948,plain,
% 3.11/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.11/0.99      | r1_tarski(sK4,X0) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_3947]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3950,plain,
% 3.11/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.11/0.99      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_3948]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5298,plain,
% 3.11/0.99      ( sK4 = k1_xboole_0 ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_4351,c_2736,c_3412,c_3950,c_4309]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4290,plain,
% 3.11/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK4)))) = iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_4280,c_3246]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_9,plain,
% 3.11/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4367,plain,
% 3.11/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_4290,c_9]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5311,plain,
% 3.11/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_5298,c_4367]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3715,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.11/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_9,c_1708]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5932,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_5311,c_3715]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3248,plain,
% 3.11/0.99      ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_3196,c_2033]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4293,plain,
% 3.11/0.99      ( k1_relat_1(k2_funct_1(sK4)) = k1_xboole_0 ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_4280,c_3248]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5315,plain,
% 3.11/0.99      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_5298,c_4293]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5943,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_5932,c_5315]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_26,plain,
% 3.11/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_669,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/0.99      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.11/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.11/0.99      | k2_funct_1(sK4) != X0
% 3.11/0.99      | sK2 != X1
% 3.11/0.99      | sK3 != k1_xboole_0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_670,plain,
% 3.11/0.99      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.11/0.99      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.11/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.11/0.99      | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.11/0.99      | sK3 != k1_xboole_0 ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_669]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1693,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.11/0.99      | sK3 != k1_xboole_0
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1912,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.11/0.99      | sK3 != k1_xboole_0
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.11/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_1693,c_9]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2333,plain,
% 3.11/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/0.99      | sK3 != k1_xboole_0
% 3.11/0.99      | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0 ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_1912,c_43,c_45,c_2026,c_2172]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2334,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.11/0.99      | sK3 != k1_xboole_0
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(renaming,[status(thm)],[c_2333]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4298,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 != k1_xboole_0
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_4280,c_2334]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4340,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(equality_resolution_simp,[status(thm)],[c_4298]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4344,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.11/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_4340,c_9]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4371,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0 ),
% 3.11/0.99      inference(backward_subsumption_resolution,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_4367,c_4344]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_5945,plain,
% 3.11/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.11/0.99      inference(light_normalisation,[status(thm)],[c_4371,c_5298]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_6340,plain,
% 3.11/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_5943,c_5945]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_122,plain,
% 3.11/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_10,plain,
% 3.11/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 = X1
% 3.11/0.99      | k1_xboole_0 = X0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_121,plain,
% 3.11/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.11/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(contradiction,plain,
% 3.11/0.99      ( $false ),
% 3.11/0.99      inference(minisat,[status(thm)],[c_6340,c_122,c_121]) ).
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  ------                               Statistics
% 3.11/0.99  
% 3.11/0.99  ------ General
% 3.11/0.99  
% 3.11/0.99  abstr_ref_over_cycles:                  0
% 3.11/0.99  abstr_ref_under_cycles:                 0
% 3.11/0.99  gc_basic_clause_elim:                   0
% 3.11/0.99  forced_gc_time:                         0
% 3.11/0.99  parsing_time:                           0.012
% 3.11/0.99  unif_index_cands_time:                  0.
% 3.11/0.99  unif_index_add_time:                    0.
% 3.11/0.99  orderings_time:                         0.
% 3.11/0.99  out_proof_time:                         0.013
% 3.11/0.99  total_time:                             0.159
% 3.11/0.99  num_of_symbols:                         53
% 3.11/0.99  num_of_terms:                           4831
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing
% 3.11/0.99  
% 3.11/0.99  num_of_splits:                          0
% 3.11/0.99  num_of_split_atoms:                     0
% 3.11/0.99  num_of_reused_defs:                     0
% 3.11/0.99  num_eq_ax_congr_red:                    11
% 3.11/0.99  num_of_sem_filtered_clauses:            1
% 3.11/0.99  num_of_subtypes:                        0
% 3.11/0.99  monotx_restored_types:                  0
% 3.11/0.99  sat_num_of_epr_types:                   0
% 3.11/0.99  sat_num_of_non_cyclic_types:            0
% 3.11/0.99  sat_guarded_non_collapsed_types:        0
% 3.11/0.99  num_pure_diseq_elim:                    0
% 3.11/0.99  simp_replaced_by:                       0
% 3.11/0.99  res_preprocessed:                       162
% 3.11/0.99  prep_upred:                             0
% 3.11/0.99  prep_unflattend:                        55
% 3.11/0.99  smt_new_axioms:                         0
% 3.11/0.99  pred_elim_cands:                        8
% 3.11/0.99  pred_elim:                              3
% 3.11/0.99  pred_elim_cl:                           -3
% 3.11/0.99  pred_elim_cycles:                       4
% 3.11/0.99  merged_defs:                            6
% 3.11/0.99  merged_defs_ncl:                        0
% 3.11/0.99  bin_hyper_res:                          7
% 3.11/0.99  prep_cycles:                            3
% 3.11/0.99  pred_elim_time:                         0.007
% 3.11/0.99  splitting_time:                         0.
% 3.11/0.99  sem_filter_time:                        0.
% 3.11/0.99  monotx_time:                            0.
% 3.11/0.99  subtype_inf_time:                       0.
% 3.11/0.99  
% 3.11/0.99  ------ Problem properties
% 3.11/0.99  
% 3.11/0.99  clauses:                                44
% 3.11/0.99  conjectures:                            3
% 3.11/0.99  epr:                                    6
% 3.11/0.99  horn:                                   36
% 3.11/0.99  ground:                                 15
% 3.11/0.99  unary:                                  14
% 3.11/0.99  binary:                                 13
% 3.11/0.99  lits:                                   104
% 3.11/0.99  lits_eq:                                43
% 3.11/0.99  fd_pure:                                0
% 3.11/0.99  fd_pseudo:                              0
% 3.11/0.99  fd_cond:                                3
% 3.11/0.99  fd_pseudo_cond:                         1
% 3.11/0.99  ac_symbols:                             0
% 3.11/0.99  
% 3.11/0.99  ------ Propositional Solver
% 3.11/0.99  
% 3.11/0.99  prop_solver_calls:                      24
% 3.11/0.99  prop_fast_solver_calls:                 1117
% 3.11/0.99  smt_solver_calls:                       0
% 3.11/0.99  smt_fast_solver_calls:                  0
% 3.11/0.99  prop_num_of_clauses:                    2138
% 3.11/0.99  prop_preprocess_simplified:             6860
% 3.11/0.99  prop_fo_subsumed:                       32
% 3.11/0.99  prop_solver_time:                       0.
% 3.11/0.99  smt_solver_time:                        0.
% 3.11/0.99  smt_fast_solver_time:                   0.
% 3.11/0.99  prop_fast_solver_time:                  0.
% 3.11/0.99  prop_unsat_core_time:                   0.
% 3.11/0.99  
% 3.11/0.99  ------ QBF
% 3.11/0.99  
% 3.11/0.99  qbf_q_res:                              0
% 3.11/0.99  qbf_num_tautologies:                    0
% 3.11/0.99  qbf_prep_cycles:                        0
% 3.11/0.99  
% 3.11/0.99  ------ BMC1
% 3.11/0.99  
% 3.11/0.99  bmc1_current_bound:                     -1
% 3.11/0.99  bmc1_last_solved_bound:                 -1
% 3.11/0.99  bmc1_unsat_core_size:                   -1
% 3.11/0.99  bmc1_unsat_core_parents_size:           -1
% 3.11/0.99  bmc1_merge_next_fun:                    0
% 3.11/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation
% 3.11/0.99  
% 3.11/0.99  inst_num_of_clauses:                    708
% 3.11/0.99  inst_num_in_passive:                    82
% 3.11/0.99  inst_num_in_active:                     427
% 3.11/0.99  inst_num_in_unprocessed:                199
% 3.11/0.99  inst_num_of_loops:                      610
% 3.11/0.99  inst_num_of_learning_restarts:          0
% 3.11/0.99  inst_num_moves_active_passive:          180
% 3.11/0.99  inst_lit_activity:                      0
% 3.11/0.99  inst_lit_activity_moves:                0
% 3.11/0.99  inst_num_tautologies:                   0
% 3.11/0.99  inst_num_prop_implied:                  0
% 3.11/0.99  inst_num_existing_simplified:           0
% 3.11/0.99  inst_num_eq_res_simplified:             0
% 3.11/0.99  inst_num_child_elim:                    0
% 3.11/0.99  inst_num_of_dismatching_blockings:      204
% 3.11/0.99  inst_num_of_non_proper_insts:           683
% 3.11/0.99  inst_num_of_duplicates:                 0
% 3.11/0.99  inst_inst_num_from_inst_to_res:         0
% 3.11/0.99  inst_dismatching_checking_time:         0.
% 3.11/0.99  
% 3.11/0.99  ------ Resolution
% 3.11/0.99  
% 3.11/0.99  res_num_of_clauses:                     0
% 3.11/0.99  res_num_in_passive:                     0
% 3.11/0.99  res_num_in_active:                      0
% 3.11/0.99  res_num_of_loops:                       165
% 3.11/0.99  res_forward_subset_subsumed:            32
% 3.11/0.99  res_backward_subset_subsumed:           0
% 3.11/0.99  res_forward_subsumed:                   0
% 3.11/0.99  res_backward_subsumed:                  0
% 3.11/0.99  res_forward_subsumption_resolution:     5
% 3.11/0.99  res_backward_subsumption_resolution:    0
% 3.11/0.99  res_clause_to_clause_subsumption:       379
% 3.11/0.99  res_orphan_elimination:                 0
% 3.11/0.99  res_tautology_del:                      73
% 3.11/0.99  res_num_eq_res_simplified:              0
% 3.11/0.99  res_num_sel_changes:                    0
% 3.11/0.99  res_moves_from_active_to_pass:          0
% 3.11/0.99  
% 3.11/0.99  ------ Superposition
% 3.11/0.99  
% 3.11/0.99  sup_time_total:                         0.
% 3.11/0.99  sup_time_generating:                    0.
% 3.11/0.99  sup_time_sim_full:                      0.
% 3.11/0.99  sup_time_sim_immed:                     0.
% 3.11/0.99  
% 3.11/0.99  sup_num_of_clauses:                     107
% 3.11/0.99  sup_num_in_active:                      66
% 3.11/0.99  sup_num_in_passive:                     41
% 3.11/0.99  sup_num_of_loops:                       121
% 3.11/0.99  sup_fw_superposition:                   96
% 3.11/0.99  sup_bw_superposition:                   73
% 3.11/0.99  sup_immediate_simplified:               80
% 3.11/0.99  sup_given_eliminated:                   1
% 3.11/0.99  comparisons_done:                       0
% 3.11/0.99  comparisons_avoided:                    13
% 3.11/0.99  
% 3.11/0.99  ------ Simplifications
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  sim_fw_subset_subsumed:                 18
% 3.11/0.99  sim_bw_subset_subsumed:                 7
% 3.11/0.99  sim_fw_subsumed:                        9
% 3.11/0.99  sim_bw_subsumed:                        6
% 3.11/0.99  sim_fw_subsumption_res:                 2
% 3.11/0.99  sim_bw_subsumption_res:                 3
% 3.11/0.99  sim_tautology_del:                      2
% 3.11/0.99  sim_eq_tautology_del:                   12
% 3.11/0.99  sim_eq_res_simp:                        3
% 3.11/0.99  sim_fw_demodulated:                     26
% 3.11/0.99  sim_bw_demodulated:                     55
% 3.11/0.99  sim_light_normalised:                   39
% 3.11/0.99  sim_joinable_taut:                      0
% 3.11/0.99  sim_joinable_simp:                      0
% 3.11/0.99  sim_ac_normalised:                      0
% 3.11/0.99  sim_smt_subsumption:                    0
% 3.11/0.99  
%------------------------------------------------------------------------------

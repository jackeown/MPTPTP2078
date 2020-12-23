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
% DateTime   : Thu Dec  3 12:02:21 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  254 (6483 expanded)
%              Number of clauses        :  164 (2197 expanded)
%              Number of leaves         :   23 (1218 expanded)
%              Depth                    :   32
%              Number of atoms          :  782 (33465 expanded)
%              Number of equality atoms :  423 (6967 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f59,plain,
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

fof(f60,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f59])).

fof(f102,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f103,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f60])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f60])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f84,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f101,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f81,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f82,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f106,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f60])).

fof(f15,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f25,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f57,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f25])).

fof(f86,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f55])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f110,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f97])).

fof(f112,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f111])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f113,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f96])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f62,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1221,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_44])).

cnf(c_1222,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_1221])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1224,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1222,c_43])).

cnf(c_2279,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2282,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5365,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2279,c_2282])).

cnf(c_5562,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1224,c_5365])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2281,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4519,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2279,c_2281])).

cnf(c_41,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_4531,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4519,c_41])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2283,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3740,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2279,c_2283])).

cnf(c_24,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_42,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_486,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_42])).

cnf(c_487,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_489,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_45])).

cnf(c_2274,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_3792,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3740,c_2274])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_514,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_42])).

cnf(c_515,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_517,plain,
    ( ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_45])).

cnf(c_2272,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_3794,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3740,c_2272])).

cnf(c_3800,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_3792,c_3794])).

cnf(c_4538,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4531,c_3800])).

cnf(c_37,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2280,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5996,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK3)),X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4538,c_2280])).

cnf(c_23,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_500,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_42])).

cnf(c_501,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_503,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_45])).

cnf(c_2273,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_3793,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3740,c_2273])).

cnf(c_3797,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_3793,c_3794])).

cnf(c_6012,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5996,c_3797])).

cnf(c_46,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2630,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2759,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2630])).

cnf(c_2760,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2759])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2287,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6064,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3794,c_2287])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2288,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6154,plain,
    ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3794,c_2288])).

cnf(c_7189,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6012,c_46,c_48,c_2760,c_6064,c_6154])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2295,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7200,plain,
    ( k1_relset_1(sK2,X0,k4_relat_1(sK3)) = k1_relat_1(k4_relat_1(sK3))
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7189,c_2282])).

cnf(c_7214,plain,
    ( k1_relset_1(sK2,X0,k4_relat_1(sK3)) = sK2
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7200,c_4538])).

cnf(c_7673,plain,
    ( k1_relset_1(sK2,X0,k4_relat_1(sK3)) = sK2
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5562,c_7214])).

cnf(c_8085,plain,
    ( k1_relset_1(sK2,sK1,k4_relat_1(sK3)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2295,c_7673])).

cnf(c_34,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_40,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1205,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK3) != X0
    | sK1 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_40])).

cnf(c_1206,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1205])).

cnf(c_2264,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1206])).

cnf(c_3806,plain,
    ( k1_relset_1(sK2,sK1,k4_relat_1(sK3)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3794,c_2264])).

cnf(c_9529,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8085,c_3806])).

cnf(c_26,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_88,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_89,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_119,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_120,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_121,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_123,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_1590,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2679,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),X3)
    | X3 != X1
    | k2_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_2680,plain,
    ( X0 != X1
    | k2_relat_1(X2) != X3
    | r1_tarski(X3,X1) != iProver_top
    | r1_tarski(k2_relat_1(X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2679])).

cnf(c_2682,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2680])).

cnf(c_2735,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_2736,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2735])).

cnf(c_2738,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2736])).

cnf(c_31,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1048,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_40])).

cnf(c_1049,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_1048])).

cnf(c_2271,plain,
    ( k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1049])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2514,plain,
    ( k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2271,c_7])).

cnf(c_2621,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2622,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2621])).

cnf(c_2864,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | k2_funct_1(sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2514,c_46,c_48,c_2622,c_2760])).

cnf(c_2865,plain,
    ( k2_funct_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2864])).

cnf(c_3804,plain,
    ( k4_relat_1(sK3) != k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3794,c_2865])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_38,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1074,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_38])).

cnf(c_1075,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_1074])).

cnf(c_1091,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1075,c_37])).

cnf(c_2270,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1091])).

cnf(c_4119,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k1_xboole_0
    | k4_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3797,c_2270])).

cnf(c_5732,plain,
    ( k4_relat_1(sK3) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4119,c_4538])).

cnf(c_5739,plain,
    ( k4_relat_1(sK3) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5562,c_5732])).

cnf(c_5993,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_2280])).

cnf(c_6046,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5993])).

cnf(c_9721,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9529,c_46,c_48,c_88,c_89,c_14,c_119,c_120,c_123,c_2682,c_2738,c_2760,c_3804,c_5739,c_6046,c_6064,c_6154])).

cnf(c_9722,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9721])).

cnf(c_9727,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7189,c_9722])).

cnf(c_1232,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_40])).

cnf(c_1233,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1232])).

cnf(c_1245,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1233,c_28])).

cnf(c_2263,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_3807,plain,
    ( k1_relat_1(k4_relat_1(sK3)) != sK2
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3794,c_2263])).

cnf(c_4973,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3807,c_4538])).

cnf(c_4977,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4973,c_3797])).

cnf(c_7202,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7189,c_4977])).

cnf(c_9730,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9727,c_46,c_48,c_2760,c_6154,c_7202])).

cnf(c_9735,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5562,c_9730])).

cnf(c_4706,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4709,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4706])).

cnf(c_9814,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9735,c_4709])).

cnf(c_4539,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4531,c_2270])).

cnf(c_4800,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4539,c_46,c_48,c_2760])).

cnf(c_9847,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9814,c_4800])).

cnf(c_122,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2703,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1586,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2719,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_2740,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_2742,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2740])).

cnf(c_1587,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2762,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_3352,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2762])).

cnf(c_3353,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3352])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2299,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8365,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4531,c_5993])).

cnf(c_8482,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8365,c_46,c_48,c_2760])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2293,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8488,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8482,c_2293])).

cnf(c_2294,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_27,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2284,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3728,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2294,c_2284])).

cnf(c_9432,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8488,c_3728])).

cnf(c_9433,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_9432])).

cnf(c_9440,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_9433])).

cnf(c_9441,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9440])).

cnf(c_10593,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9847,c_119,c_120,c_122,c_2703,c_2719,c_2742,c_3353,c_4709,c_9441,c_9735])).

cnf(c_10606,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10593,c_9730])).

cnf(c_15,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_10628,plain,
    ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10606,c_15])).

cnf(c_4915,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4918,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4915])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10628,c_4918])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.21/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/0.99  
% 3.21/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.21/0.99  
% 3.21/0.99  ------  iProver source info
% 3.21/0.99  
% 3.21/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.21/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.21/0.99  git: non_committed_changes: false
% 3.21/0.99  git: last_make_outside_of_git: false
% 3.21/0.99  
% 3.21/0.99  ------ 
% 3.21/0.99  
% 3.21/0.99  ------ Input Options
% 3.21/0.99  
% 3.21/0.99  --out_options                           all
% 3.21/0.99  --tptp_safe_out                         true
% 3.21/0.99  --problem_path                          ""
% 3.21/0.99  --include_path                          ""
% 3.21/0.99  --clausifier                            res/vclausify_rel
% 3.21/0.99  --clausifier_options                    --mode clausify
% 3.21/0.99  --stdin                                 false
% 3.21/0.99  --stats_out                             all
% 3.21/0.99  
% 3.21/0.99  ------ General Options
% 3.21/0.99  
% 3.21/0.99  --fof                                   false
% 3.21/0.99  --time_out_real                         305.
% 3.21/0.99  --time_out_virtual                      -1.
% 3.21/0.99  --symbol_type_check                     false
% 3.21/0.99  --clausify_out                          false
% 3.21/0.99  --sig_cnt_out                           false
% 3.21/0.99  --trig_cnt_out                          false
% 3.21/0.99  --trig_cnt_out_tolerance                1.
% 3.21/0.99  --trig_cnt_out_sk_spl                   false
% 3.21/0.99  --abstr_cl_out                          false
% 3.21/0.99  
% 3.21/0.99  ------ Global Options
% 3.21/0.99  
% 3.21/0.99  --schedule                              default
% 3.21/0.99  --add_important_lit                     false
% 3.21/0.99  --prop_solver_per_cl                    1000
% 3.21/0.99  --min_unsat_core                        false
% 3.21/0.99  --soft_assumptions                      false
% 3.21/0.99  --soft_lemma_size                       3
% 3.21/0.99  --prop_impl_unit_size                   0
% 3.21/0.99  --prop_impl_unit                        []
% 3.21/0.99  --share_sel_clauses                     true
% 3.21/0.99  --reset_solvers                         false
% 3.21/0.99  --bc_imp_inh                            [conj_cone]
% 3.21/0.99  --conj_cone_tolerance                   3.
% 3.21/0.99  --extra_neg_conj                        none
% 3.21/0.99  --large_theory_mode                     true
% 3.21/0.99  --prolific_symb_bound                   200
% 3.21/0.99  --lt_threshold                          2000
% 3.21/0.99  --clause_weak_htbl                      true
% 3.21/0.99  --gc_record_bc_elim                     false
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing Options
% 3.21/0.99  
% 3.21/0.99  --preprocessing_flag                    true
% 3.21/0.99  --time_out_prep_mult                    0.1
% 3.21/0.99  --splitting_mode                        input
% 3.21/0.99  --splitting_grd                         true
% 3.21/0.99  --splitting_cvd                         false
% 3.21/0.99  --splitting_cvd_svl                     false
% 3.21/0.99  --splitting_nvd                         32
% 3.21/0.99  --sub_typing                            true
% 3.21/0.99  --prep_gs_sim                           true
% 3.21/0.99  --prep_unflatten                        true
% 3.21/0.99  --prep_res_sim                          true
% 3.21/0.99  --prep_upred                            true
% 3.21/0.99  --prep_sem_filter                       exhaustive
% 3.21/0.99  --prep_sem_filter_out                   false
% 3.21/0.99  --pred_elim                             true
% 3.21/0.99  --res_sim_input                         true
% 3.21/0.99  --eq_ax_congr_red                       true
% 3.21/0.99  --pure_diseq_elim                       true
% 3.21/0.99  --brand_transform                       false
% 3.21/0.99  --non_eq_to_eq                          false
% 3.21/0.99  --prep_def_merge                        true
% 3.21/0.99  --prep_def_merge_prop_impl              false
% 3.21/0.99  --prep_def_merge_mbd                    true
% 3.21/0.99  --prep_def_merge_tr_red                 false
% 3.21/0.99  --prep_def_merge_tr_cl                  false
% 3.21/0.99  --smt_preprocessing                     true
% 3.21/0.99  --smt_ac_axioms                         fast
% 3.21/0.99  --preprocessed_out                      false
% 3.21/0.99  --preprocessed_stats                    false
% 3.21/0.99  
% 3.21/0.99  ------ Abstraction refinement Options
% 3.21/0.99  
% 3.21/0.99  --abstr_ref                             []
% 3.21/0.99  --abstr_ref_prep                        false
% 3.21/0.99  --abstr_ref_until_sat                   false
% 3.21/0.99  --abstr_ref_sig_restrict                funpre
% 3.21/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/0.99  --abstr_ref_under                       []
% 3.21/0.99  
% 3.21/0.99  ------ SAT Options
% 3.21/0.99  
% 3.21/0.99  --sat_mode                              false
% 3.21/0.99  --sat_fm_restart_options                ""
% 3.21/0.99  --sat_gr_def                            false
% 3.21/0.99  --sat_epr_types                         true
% 3.21/0.99  --sat_non_cyclic_types                  false
% 3.21/0.99  --sat_finite_models                     false
% 3.21/0.99  --sat_fm_lemmas                         false
% 3.21/0.99  --sat_fm_prep                           false
% 3.21/0.99  --sat_fm_uc_incr                        true
% 3.21/0.99  --sat_out_model                         small
% 3.21/0.99  --sat_out_clauses                       false
% 3.21/0.99  
% 3.21/0.99  ------ QBF Options
% 3.21/0.99  
% 3.21/0.99  --qbf_mode                              false
% 3.21/0.99  --qbf_elim_univ                         false
% 3.21/0.99  --qbf_dom_inst                          none
% 3.21/0.99  --qbf_dom_pre_inst                      false
% 3.21/0.99  --qbf_sk_in                             false
% 3.21/0.99  --qbf_pred_elim                         true
% 3.21/0.99  --qbf_split                             512
% 3.21/0.99  
% 3.21/0.99  ------ BMC1 Options
% 3.21/0.99  
% 3.21/0.99  --bmc1_incremental                      false
% 3.21/0.99  --bmc1_axioms                           reachable_all
% 3.21/0.99  --bmc1_min_bound                        0
% 3.21/0.99  --bmc1_max_bound                        -1
% 3.21/0.99  --bmc1_max_bound_default                -1
% 3.21/0.99  --bmc1_symbol_reachability              true
% 3.21/0.99  --bmc1_property_lemmas                  false
% 3.21/0.99  --bmc1_k_induction                      false
% 3.21/0.99  --bmc1_non_equiv_states                 false
% 3.21/0.99  --bmc1_deadlock                         false
% 3.21/0.99  --bmc1_ucm                              false
% 3.21/0.99  --bmc1_add_unsat_core                   none
% 3.21/0.99  --bmc1_unsat_core_children              false
% 3.21/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/0.99  --bmc1_out_stat                         full
% 3.21/0.99  --bmc1_ground_init                      false
% 3.21/0.99  --bmc1_pre_inst_next_state              false
% 3.21/0.99  --bmc1_pre_inst_state                   false
% 3.21/0.99  --bmc1_pre_inst_reach_state             false
% 3.21/0.99  --bmc1_out_unsat_core                   false
% 3.21/0.99  --bmc1_aig_witness_out                  false
% 3.21/0.99  --bmc1_verbose                          false
% 3.21/0.99  --bmc1_dump_clauses_tptp                false
% 3.21/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.21/0.99  --bmc1_dump_file                        -
% 3.21/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.21/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.21/0.99  --bmc1_ucm_extend_mode                  1
% 3.21/0.99  --bmc1_ucm_init_mode                    2
% 3.21/0.99  --bmc1_ucm_cone_mode                    none
% 3.21/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.21/0.99  --bmc1_ucm_relax_model                  4
% 3.21/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.21/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/0.99  --bmc1_ucm_layered_model                none
% 3.21/0.99  --bmc1_ucm_max_lemma_size               10
% 3.21/0.99  
% 3.21/0.99  ------ AIG Options
% 3.21/0.99  
% 3.21/0.99  --aig_mode                              false
% 3.21/0.99  
% 3.21/0.99  ------ Instantiation Options
% 3.21/0.99  
% 3.21/0.99  --instantiation_flag                    true
% 3.21/0.99  --inst_sos_flag                         false
% 3.21/0.99  --inst_sos_phase                        true
% 3.21/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/0.99  --inst_lit_sel_side                     num_symb
% 3.21/0.99  --inst_solver_per_active                1400
% 3.21/0.99  --inst_solver_calls_frac                1.
% 3.21/0.99  --inst_passive_queue_type               priority_queues
% 3.21/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/0.99  --inst_passive_queues_freq              [25;2]
% 3.21/0.99  --inst_dismatching                      true
% 3.21/0.99  --inst_eager_unprocessed_to_passive     true
% 3.21/0.99  --inst_prop_sim_given                   true
% 3.21/0.99  --inst_prop_sim_new                     false
% 3.21/0.99  --inst_subs_new                         false
% 3.21/0.99  --inst_eq_res_simp                      false
% 3.21/0.99  --inst_subs_given                       false
% 3.21/0.99  --inst_orphan_elimination               true
% 3.21/0.99  --inst_learning_loop_flag               true
% 3.21/0.99  --inst_learning_start                   3000
% 3.21/0.99  --inst_learning_factor                  2
% 3.21/0.99  --inst_start_prop_sim_after_learn       3
% 3.21/0.99  --inst_sel_renew                        solver
% 3.21/0.99  --inst_lit_activity_flag                true
% 3.21/0.99  --inst_restr_to_given                   false
% 3.21/0.99  --inst_activity_threshold               500
% 3.21/0.99  --inst_out_proof                        true
% 3.21/0.99  
% 3.21/0.99  ------ Resolution Options
% 3.21/0.99  
% 3.21/0.99  --resolution_flag                       true
% 3.21/0.99  --res_lit_sel                           adaptive
% 3.21/0.99  --res_lit_sel_side                      none
% 3.21/0.99  --res_ordering                          kbo
% 3.21/0.99  --res_to_prop_solver                    active
% 3.21/0.99  --res_prop_simpl_new                    false
% 3.21/0.99  --res_prop_simpl_given                  true
% 3.21/0.99  --res_passive_queue_type                priority_queues
% 3.21/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/0.99  --res_passive_queues_freq               [15;5]
% 3.21/0.99  --res_forward_subs                      full
% 3.21/0.99  --res_backward_subs                     full
% 3.21/0.99  --res_forward_subs_resolution           true
% 3.21/0.99  --res_backward_subs_resolution          true
% 3.21/0.99  --res_orphan_elimination                true
% 3.21/0.99  --res_time_limit                        2.
% 3.21/0.99  --res_out_proof                         true
% 3.21/0.99  
% 3.21/0.99  ------ Superposition Options
% 3.21/0.99  
% 3.21/0.99  --superposition_flag                    true
% 3.21/0.99  --sup_passive_queue_type                priority_queues
% 3.21/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.21/0.99  --demod_completeness_check              fast
% 3.21/0.99  --demod_use_ground                      true
% 3.21/0.99  --sup_to_prop_solver                    passive
% 3.21/0.99  --sup_prop_simpl_new                    true
% 3.21/0.99  --sup_prop_simpl_given                  true
% 3.21/0.99  --sup_fun_splitting                     false
% 3.21/0.99  --sup_smt_interval                      50000
% 3.21/0.99  
% 3.21/0.99  ------ Superposition Simplification Setup
% 3.21/0.99  
% 3.21/0.99  --sup_indices_passive                   []
% 3.21/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_full_bw                           [BwDemod]
% 3.21/0.99  --sup_immed_triv                        [TrivRules]
% 3.21/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_immed_bw_main                     []
% 3.21/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/0.99  
% 3.21/0.99  ------ Combination Options
% 3.21/0.99  
% 3.21/0.99  --comb_res_mult                         3
% 3.21/0.99  --comb_sup_mult                         2
% 3.21/0.99  --comb_inst_mult                        10
% 3.21/0.99  
% 3.21/0.99  ------ Debug Options
% 3.21/0.99  
% 3.21/0.99  --dbg_backtrace                         false
% 3.21/0.99  --dbg_dump_prop_clauses                 false
% 3.21/0.99  --dbg_dump_prop_clauses_file            -
% 3.21/0.99  --dbg_out_stat                          false
% 3.21/0.99  ------ Parsing...
% 3.21/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.21/0.99  ------ Proving...
% 3.21/0.99  ------ Problem Properties 
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  clauses                                 45
% 3.21/0.99  conjectures                             3
% 3.21/0.99  EPR                                     11
% 3.21/0.99  Horn                                    39
% 3.21/0.99  unary                                   11
% 3.21/0.99  binary                                  18
% 3.21/0.99  lits                                    111
% 3.21/0.99  lits eq                                 41
% 3.21/0.99  fd_pure                                 0
% 3.21/0.99  fd_pseudo                               0
% 3.21/0.99  fd_cond                                 4
% 3.21/0.99  fd_pseudo_cond                          1
% 3.21/0.99  AC symbols                              0
% 3.21/0.99  
% 3.21/0.99  ------ Schedule dynamic 5 is on 
% 3.21/0.99  
% 3.21/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  ------ 
% 3.21/0.99  Current options:
% 3.21/0.99  ------ 
% 3.21/0.99  
% 3.21/0.99  ------ Input Options
% 3.21/0.99  
% 3.21/0.99  --out_options                           all
% 3.21/0.99  --tptp_safe_out                         true
% 3.21/0.99  --problem_path                          ""
% 3.21/0.99  --include_path                          ""
% 3.21/0.99  --clausifier                            res/vclausify_rel
% 3.21/0.99  --clausifier_options                    --mode clausify
% 3.21/0.99  --stdin                                 false
% 3.21/0.99  --stats_out                             all
% 3.21/0.99  
% 3.21/0.99  ------ General Options
% 3.21/0.99  
% 3.21/0.99  --fof                                   false
% 3.21/0.99  --time_out_real                         305.
% 3.21/0.99  --time_out_virtual                      -1.
% 3.21/0.99  --symbol_type_check                     false
% 3.21/0.99  --clausify_out                          false
% 3.21/0.99  --sig_cnt_out                           false
% 3.21/0.99  --trig_cnt_out                          false
% 3.21/0.99  --trig_cnt_out_tolerance                1.
% 3.21/0.99  --trig_cnt_out_sk_spl                   false
% 3.21/0.99  --abstr_cl_out                          false
% 3.21/0.99  
% 3.21/0.99  ------ Global Options
% 3.21/0.99  
% 3.21/0.99  --schedule                              default
% 3.21/0.99  --add_important_lit                     false
% 3.21/0.99  --prop_solver_per_cl                    1000
% 3.21/0.99  --min_unsat_core                        false
% 3.21/0.99  --soft_assumptions                      false
% 3.21/0.99  --soft_lemma_size                       3
% 3.21/0.99  --prop_impl_unit_size                   0
% 3.21/0.99  --prop_impl_unit                        []
% 3.21/0.99  --share_sel_clauses                     true
% 3.21/0.99  --reset_solvers                         false
% 3.21/0.99  --bc_imp_inh                            [conj_cone]
% 3.21/0.99  --conj_cone_tolerance                   3.
% 3.21/0.99  --extra_neg_conj                        none
% 3.21/0.99  --large_theory_mode                     true
% 3.21/0.99  --prolific_symb_bound                   200
% 3.21/0.99  --lt_threshold                          2000
% 3.21/0.99  --clause_weak_htbl                      true
% 3.21/0.99  --gc_record_bc_elim                     false
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing Options
% 3.21/0.99  
% 3.21/0.99  --preprocessing_flag                    true
% 3.21/0.99  --time_out_prep_mult                    0.1
% 3.21/0.99  --splitting_mode                        input
% 3.21/0.99  --splitting_grd                         true
% 3.21/0.99  --splitting_cvd                         false
% 3.21/0.99  --splitting_cvd_svl                     false
% 3.21/0.99  --splitting_nvd                         32
% 3.21/0.99  --sub_typing                            true
% 3.21/0.99  --prep_gs_sim                           true
% 3.21/0.99  --prep_unflatten                        true
% 3.21/0.99  --prep_res_sim                          true
% 3.21/0.99  --prep_upred                            true
% 3.21/0.99  --prep_sem_filter                       exhaustive
% 3.21/0.99  --prep_sem_filter_out                   false
% 3.21/0.99  --pred_elim                             true
% 3.21/0.99  --res_sim_input                         true
% 3.21/0.99  --eq_ax_congr_red                       true
% 3.21/0.99  --pure_diseq_elim                       true
% 3.21/0.99  --brand_transform                       false
% 3.21/0.99  --non_eq_to_eq                          false
% 3.21/0.99  --prep_def_merge                        true
% 3.21/0.99  --prep_def_merge_prop_impl              false
% 3.21/0.99  --prep_def_merge_mbd                    true
% 3.21/0.99  --prep_def_merge_tr_red                 false
% 3.21/0.99  --prep_def_merge_tr_cl                  false
% 3.21/0.99  --smt_preprocessing                     true
% 3.21/0.99  --smt_ac_axioms                         fast
% 3.21/0.99  --preprocessed_out                      false
% 3.21/0.99  --preprocessed_stats                    false
% 3.21/0.99  
% 3.21/0.99  ------ Abstraction refinement Options
% 3.21/0.99  
% 3.21/0.99  --abstr_ref                             []
% 3.21/0.99  --abstr_ref_prep                        false
% 3.21/0.99  --abstr_ref_until_sat                   false
% 3.21/0.99  --abstr_ref_sig_restrict                funpre
% 3.21/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/0.99  --abstr_ref_under                       []
% 3.21/0.99  
% 3.21/0.99  ------ SAT Options
% 3.21/0.99  
% 3.21/0.99  --sat_mode                              false
% 3.21/0.99  --sat_fm_restart_options                ""
% 3.21/0.99  --sat_gr_def                            false
% 3.21/0.99  --sat_epr_types                         true
% 3.21/0.99  --sat_non_cyclic_types                  false
% 3.21/0.99  --sat_finite_models                     false
% 3.21/0.99  --sat_fm_lemmas                         false
% 3.21/0.99  --sat_fm_prep                           false
% 3.21/0.99  --sat_fm_uc_incr                        true
% 3.21/0.99  --sat_out_model                         small
% 3.21/0.99  --sat_out_clauses                       false
% 3.21/0.99  
% 3.21/0.99  ------ QBF Options
% 3.21/0.99  
% 3.21/0.99  --qbf_mode                              false
% 3.21/0.99  --qbf_elim_univ                         false
% 3.21/0.99  --qbf_dom_inst                          none
% 3.21/0.99  --qbf_dom_pre_inst                      false
% 3.21/0.99  --qbf_sk_in                             false
% 3.21/0.99  --qbf_pred_elim                         true
% 3.21/0.99  --qbf_split                             512
% 3.21/0.99  
% 3.21/0.99  ------ BMC1 Options
% 3.21/0.99  
% 3.21/0.99  --bmc1_incremental                      false
% 3.21/0.99  --bmc1_axioms                           reachable_all
% 3.21/0.99  --bmc1_min_bound                        0
% 3.21/0.99  --bmc1_max_bound                        -1
% 3.21/0.99  --bmc1_max_bound_default                -1
% 3.21/0.99  --bmc1_symbol_reachability              true
% 3.21/0.99  --bmc1_property_lemmas                  false
% 3.21/0.99  --bmc1_k_induction                      false
% 3.21/0.99  --bmc1_non_equiv_states                 false
% 3.21/0.99  --bmc1_deadlock                         false
% 3.21/0.99  --bmc1_ucm                              false
% 3.21/0.99  --bmc1_add_unsat_core                   none
% 3.21/0.99  --bmc1_unsat_core_children              false
% 3.21/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/0.99  --bmc1_out_stat                         full
% 3.21/0.99  --bmc1_ground_init                      false
% 3.21/0.99  --bmc1_pre_inst_next_state              false
% 3.21/0.99  --bmc1_pre_inst_state                   false
% 3.21/0.99  --bmc1_pre_inst_reach_state             false
% 3.21/0.99  --bmc1_out_unsat_core                   false
% 3.21/0.99  --bmc1_aig_witness_out                  false
% 3.21/0.99  --bmc1_verbose                          false
% 3.21/0.99  --bmc1_dump_clauses_tptp                false
% 3.21/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.21/0.99  --bmc1_dump_file                        -
% 3.21/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.21/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.21/0.99  --bmc1_ucm_extend_mode                  1
% 3.21/0.99  --bmc1_ucm_init_mode                    2
% 3.21/0.99  --bmc1_ucm_cone_mode                    none
% 3.21/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.21/0.99  --bmc1_ucm_relax_model                  4
% 3.21/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.21/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/0.99  --bmc1_ucm_layered_model                none
% 3.21/0.99  --bmc1_ucm_max_lemma_size               10
% 3.21/0.99  
% 3.21/0.99  ------ AIG Options
% 3.21/0.99  
% 3.21/0.99  --aig_mode                              false
% 3.21/0.99  
% 3.21/0.99  ------ Instantiation Options
% 3.21/0.99  
% 3.21/0.99  --instantiation_flag                    true
% 3.21/0.99  --inst_sos_flag                         false
% 3.21/0.99  --inst_sos_phase                        true
% 3.21/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/0.99  --inst_lit_sel_side                     none
% 3.21/0.99  --inst_solver_per_active                1400
% 3.21/0.99  --inst_solver_calls_frac                1.
% 3.21/0.99  --inst_passive_queue_type               priority_queues
% 3.21/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/0.99  --inst_passive_queues_freq              [25;2]
% 3.21/0.99  --inst_dismatching                      true
% 3.21/0.99  --inst_eager_unprocessed_to_passive     true
% 3.21/0.99  --inst_prop_sim_given                   true
% 3.21/0.99  --inst_prop_sim_new                     false
% 3.21/0.99  --inst_subs_new                         false
% 3.21/0.99  --inst_eq_res_simp                      false
% 3.21/0.99  --inst_subs_given                       false
% 3.21/0.99  --inst_orphan_elimination               true
% 3.21/0.99  --inst_learning_loop_flag               true
% 3.21/0.99  --inst_learning_start                   3000
% 3.21/0.99  --inst_learning_factor                  2
% 3.21/0.99  --inst_start_prop_sim_after_learn       3
% 3.21/0.99  --inst_sel_renew                        solver
% 3.21/0.99  --inst_lit_activity_flag                true
% 3.21/0.99  --inst_restr_to_given                   false
% 3.21/0.99  --inst_activity_threshold               500
% 3.21/0.99  --inst_out_proof                        true
% 3.21/0.99  
% 3.21/0.99  ------ Resolution Options
% 3.21/0.99  
% 3.21/0.99  --resolution_flag                       false
% 3.21/0.99  --res_lit_sel                           adaptive
% 3.21/0.99  --res_lit_sel_side                      none
% 3.21/0.99  --res_ordering                          kbo
% 3.21/0.99  --res_to_prop_solver                    active
% 3.21/0.99  --res_prop_simpl_new                    false
% 3.21/0.99  --res_prop_simpl_given                  true
% 3.21/0.99  --res_passive_queue_type                priority_queues
% 3.21/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/0.99  --res_passive_queues_freq               [15;5]
% 3.21/0.99  --res_forward_subs                      full
% 3.21/0.99  --res_backward_subs                     full
% 3.21/0.99  --res_forward_subs_resolution           true
% 3.21/0.99  --res_backward_subs_resolution          true
% 3.21/0.99  --res_orphan_elimination                true
% 3.21/0.99  --res_time_limit                        2.
% 3.21/0.99  --res_out_proof                         true
% 3.21/0.99  
% 3.21/0.99  ------ Superposition Options
% 3.21/0.99  
% 3.21/0.99  --superposition_flag                    true
% 3.21/0.99  --sup_passive_queue_type                priority_queues
% 3.21/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.21/0.99  --demod_completeness_check              fast
% 3.21/0.99  --demod_use_ground                      true
% 3.21/0.99  --sup_to_prop_solver                    passive
% 3.21/0.99  --sup_prop_simpl_new                    true
% 3.21/0.99  --sup_prop_simpl_given                  true
% 3.21/0.99  --sup_fun_splitting                     false
% 3.21/0.99  --sup_smt_interval                      50000
% 3.21/0.99  
% 3.21/0.99  ------ Superposition Simplification Setup
% 3.21/0.99  
% 3.21/0.99  --sup_indices_passive                   []
% 3.21/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_full_bw                           [BwDemod]
% 3.21/0.99  --sup_immed_triv                        [TrivRules]
% 3.21/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_immed_bw_main                     []
% 3.21/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/0.99  
% 3.21/0.99  ------ Combination Options
% 3.21/0.99  
% 3.21/0.99  --comb_res_mult                         3
% 3.21/0.99  --comb_sup_mult                         2
% 3.21/0.99  --comb_inst_mult                        10
% 3.21/0.99  
% 3.21/0.99  ------ Debug Options
% 3.21/0.99  
% 3.21/0.99  --dbg_backtrace                         false
% 3.21/0.99  --dbg_dump_prop_clauses                 false
% 3.21/0.99  --dbg_dump_prop_clauses_file            -
% 3.21/0.99  --dbg_out_stat                          false
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  ------ Proving...
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  % SZS status Theorem for theBenchmark.p
% 3.21/0.99  
% 3.21/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.21/0.99  
% 3.21/0.99  fof(f20,axiom,(
% 3.21/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f43,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/0.99    inference(ennf_transformation,[],[f20])).
% 3.21/0.99  
% 3.21/0.99  fof(f44,plain,(
% 3.21/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/0.99    inference(flattening,[],[f43])).
% 3.21/0.99  
% 3.21/0.99  fof(f58,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/0.99    inference(nnf_transformation,[],[f44])).
% 3.21/0.99  
% 3.21/0.99  fof(f92,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f58])).
% 3.21/0.99  
% 3.21/0.99  fof(f22,conjecture,(
% 3.21/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f23,negated_conjecture,(
% 3.21/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.21/0.99    inference(negated_conjecture,[],[f22])).
% 3.21/0.99  
% 3.21/0.99  fof(f47,plain,(
% 3.21/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.21/0.99    inference(ennf_transformation,[],[f23])).
% 3.21/0.99  
% 3.21/0.99  fof(f48,plain,(
% 3.21/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.21/0.99    inference(flattening,[],[f47])).
% 3.21/0.99  
% 3.21/0.99  fof(f59,plain,(
% 3.21/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f60,plain,(
% 3.21/0.99    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.21/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f59])).
% 3.21/0.99  
% 3.21/0.99  fof(f102,plain,(
% 3.21/0.99    v1_funct_2(sK3,sK1,sK2)),
% 3.21/0.99    inference(cnf_transformation,[],[f60])).
% 3.21/0.99  
% 3.21/0.99  fof(f103,plain,(
% 3.21/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.21/0.99    inference(cnf_transformation,[],[f60])).
% 3.21/0.99  
% 3.21/0.99  fof(f18,axiom,(
% 3.21/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f41,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/0.99    inference(ennf_transformation,[],[f18])).
% 3.21/0.99  
% 3.21/0.99  fof(f90,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f41])).
% 3.21/0.99  
% 3.21/0.99  fof(f19,axiom,(
% 3.21/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f42,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/0.99    inference(ennf_transformation,[],[f19])).
% 3.21/0.99  
% 3.21/0.99  fof(f91,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f42])).
% 3.21/0.99  
% 3.21/0.99  fof(f105,plain,(
% 3.21/0.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.21/0.99    inference(cnf_transformation,[],[f60])).
% 3.21/0.99  
% 3.21/0.99  fof(f17,axiom,(
% 3.21/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f40,plain,(
% 3.21/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.21/0.99    inference(ennf_transformation,[],[f17])).
% 3.21/0.99  
% 3.21/0.99  fof(f89,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f40])).
% 3.21/0.99  
% 3.21/0.99  fof(f14,axiom,(
% 3.21/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f37,plain,(
% 3.21/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f14])).
% 3.21/0.99  
% 3.21/0.99  fof(f38,plain,(
% 3.21/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.21/0.99    inference(flattening,[],[f37])).
% 3.21/0.99  
% 3.21/0.99  fof(f84,plain,(
% 3.21/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f38])).
% 3.21/0.99  
% 3.21/0.99  fof(f104,plain,(
% 3.21/0.99    v2_funct_1(sK3)),
% 3.21/0.99    inference(cnf_transformation,[],[f60])).
% 3.21/0.99  
% 3.21/0.99  fof(f101,plain,(
% 3.21/0.99    v1_funct_1(sK3)),
% 3.21/0.99    inference(cnf_transformation,[],[f60])).
% 3.21/0.99  
% 3.21/0.99  fof(f12,axiom,(
% 3.21/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f33,plain,(
% 3.21/0.99    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f12])).
% 3.21/0.99  
% 3.21/0.99  fof(f34,plain,(
% 3.21/0.99    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.21/0.99    inference(flattening,[],[f33])).
% 3.21/0.99  
% 3.21/0.99  fof(f81,plain,(
% 3.21/0.99    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f34])).
% 3.21/0.99  
% 3.21/0.99  fof(f21,axiom,(
% 3.21/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f45,plain,(
% 3.21/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.21/0.99    inference(ennf_transformation,[],[f21])).
% 3.21/0.99  
% 3.21/0.99  fof(f46,plain,(
% 3.21/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.21/0.99    inference(flattening,[],[f45])).
% 3.21/0.99  
% 3.21/0.99  fof(f100,plain,(
% 3.21/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f46])).
% 3.21/0.99  
% 3.21/0.99  fof(f85,plain,(
% 3.21/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f38])).
% 3.21/0.99  
% 3.21/0.99  fof(f13,axiom,(
% 3.21/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f35,plain,(
% 3.21/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f13])).
% 3.21/0.99  
% 3.21/0.99  fof(f36,plain,(
% 3.21/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.21/0.99    inference(flattening,[],[f35])).
% 3.21/0.99  
% 3.21/0.99  fof(f82,plain,(
% 3.21/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f36])).
% 3.21/0.99  
% 3.21/0.99  fof(f83,plain,(
% 3.21/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f36])).
% 3.21/0.99  
% 3.21/0.99  fof(f3,axiom,(
% 3.21/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f53,plain,(
% 3.21/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.21/0.99    inference(nnf_transformation,[],[f3])).
% 3.21/0.99  
% 3.21/0.99  fof(f54,plain,(
% 3.21/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.21/0.99    inference(flattening,[],[f53])).
% 3.21/0.99  
% 3.21/0.99  fof(f65,plain,(
% 3.21/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.21/0.99    inference(cnf_transformation,[],[f54])).
% 3.21/0.99  
% 3.21/0.99  fof(f107,plain,(
% 3.21/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.21/0.99    inference(equality_resolution,[],[f65])).
% 3.21/0.99  
% 3.21/0.99  fof(f94,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f58])).
% 3.21/0.99  
% 3.21/0.99  fof(f106,plain,(
% 3.21/0.99    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.21/0.99    inference(cnf_transformation,[],[f60])).
% 3.21/0.99  
% 3.21/0.99  fof(f15,axiom,(
% 3.21/0.99    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f24,plain,(
% 3.21/0.99    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 3.21/0.99    inference(pure_predicate_removal,[],[f15])).
% 3.21/0.99  
% 3.21/0.99  fof(f25,plain,(
% 3.21/0.99    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 3.21/0.99    inference(pure_predicate_removal,[],[f24])).
% 3.21/0.99  
% 3.21/0.99  fof(f57,plain,(
% 3.21/0.99    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 3.21/0.99    inference(rectify,[],[f25])).
% 3.21/0.99  
% 3.21/0.99  fof(f86,plain,(
% 3.21/0.99    v1_relat_1(k1_xboole_0)),
% 3.21/0.99    inference(cnf_transformation,[],[f57])).
% 3.21/0.99  
% 3.21/0.99  fof(f87,plain,(
% 3.21/0.99    v1_funct_1(k1_xboole_0)),
% 3.21/0.99    inference(cnf_transformation,[],[f57])).
% 3.21/0.99  
% 3.21/0.99  fof(f9,axiom,(
% 3.21/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f76,plain,(
% 3.21/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.21/0.99    inference(cnf_transformation,[],[f9])).
% 3.21/0.99  
% 3.21/0.99  fof(f5,axiom,(
% 3.21/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f55,plain,(
% 3.21/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.21/0.99    inference(nnf_transformation,[],[f5])).
% 3.21/0.99  
% 3.21/0.99  fof(f56,plain,(
% 3.21/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.21/0.99    inference(flattening,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f68,plain,(
% 3.21/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f56])).
% 3.21/0.99  
% 3.21/0.99  fof(f69,plain,(
% 3.21/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.21/0.99    inference(cnf_transformation,[],[f56])).
% 3.21/0.99  
% 3.21/0.99  fof(f110,plain,(
% 3.21/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.21/0.99    inference(equality_resolution,[],[f69])).
% 3.21/0.99  
% 3.21/0.99  fof(f4,axiom,(
% 3.21/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f67,plain,(
% 3.21/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f4])).
% 3.21/0.99  
% 3.21/0.99  fof(f97,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f58])).
% 3.21/0.99  
% 3.21/0.99  fof(f111,plain,(
% 3.21/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(equality_resolution,[],[f97])).
% 3.21/0.99  
% 3.21/0.99  fof(f112,plain,(
% 3.21/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.21/0.99    inference(equality_resolution,[],[f111])).
% 3.21/0.99  
% 3.21/0.99  fof(f70,plain,(
% 3.21/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.21/0.99    inference(cnf_transformation,[],[f56])).
% 3.21/0.99  
% 3.21/0.99  fof(f109,plain,(
% 3.21/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.21/0.99    inference(equality_resolution,[],[f70])).
% 3.21/0.99  
% 3.21/0.99  fof(f96,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f58])).
% 3.21/0.99  
% 3.21/0.99  fof(f113,plain,(
% 3.21/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.21/0.99    inference(equality_resolution,[],[f96])).
% 3.21/0.99  
% 3.21/0.99  fof(f99,plain,(
% 3.21/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f46])).
% 3.21/0.99  
% 3.21/0.99  fof(f2,axiom,(
% 3.21/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f26,plain,(
% 3.21/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.21/0.99    inference(ennf_transformation,[],[f2])).
% 3.21/0.99  
% 3.21/0.99  fof(f63,plain,(
% 3.21/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f26])).
% 3.21/0.99  
% 3.21/0.99  fof(f1,axiom,(
% 3.21/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f49,plain,(
% 3.21/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.21/0.99    inference(nnf_transformation,[],[f1])).
% 3.21/0.99  
% 3.21/0.99  fof(f50,plain,(
% 3.21/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.21/0.99    inference(rectify,[],[f49])).
% 3.21/0.99  
% 3.21/0.99  fof(f51,plain,(
% 3.21/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f52,plain,(
% 3.21/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.21/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 3.21/0.99  
% 3.21/0.99  fof(f62,plain,(
% 3.21/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f52])).
% 3.21/0.99  
% 3.21/0.99  fof(f6,axiom,(
% 3.21/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f27,plain,(
% 3.21/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f6])).
% 3.21/0.99  
% 3.21/0.99  fof(f71,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.21/0.99    inference(cnf_transformation,[],[f27])).
% 3.21/0.99  
% 3.21/0.99  fof(f16,axiom,(
% 3.21/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f39,plain,(
% 3.21/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.21/0.99    inference(ennf_transformation,[],[f16])).
% 3.21/0.99  
% 3.21/0.99  fof(f88,plain,(
% 3.21/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f39])).
% 3.21/0.99  
% 3.21/0.99  fof(f75,plain,(
% 3.21/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.21/0.99    inference(cnf_transformation,[],[f9])).
% 3.21/0.99  
% 3.21/0.99  cnf(c_36,plain,
% 3.21/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.21/0.99      | k1_xboole_0 = X2 ),
% 3.21/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_44,negated_conjecture,
% 3.21/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.21/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1221,plain,
% 3.21/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.21/0.99      | sK1 != X1
% 3.21/0.99      | sK2 != X2
% 3.21/0.99      | sK3 != X0
% 3.21/0.99      | k1_xboole_0 = X2 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_36,c_44]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1222,plain,
% 3.21/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.21/0.99      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.21/0.99      | k1_xboole_0 = sK2 ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_1221]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_43,negated_conjecture,
% 3.21/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.21/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1224,plain,
% 3.21/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_1222,c_43]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2279,plain,
% 3.21/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_29,plain,
% 3.21/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2282,plain,
% 3.21/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.21/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5365,plain,
% 3.21/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_2279,c_2282]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5562,plain,
% 3.21/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_1224,c_5365]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_30,plain,
% 3.21/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2281,plain,
% 3.21/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.21/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4519,plain,
% 3.21/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_2279,c_2281]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_41,negated_conjecture,
% 3.21/0.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.21/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4531,plain,
% 3.21/0.99      ( k2_relat_1(sK3) = sK2 ),
% 3.21/0.99      inference(light_normalisation,[status(thm)],[c_4519,c_41]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_28,plain,
% 3.21/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | v1_relat_1(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2283,plain,
% 3.21/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.21/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3740,plain,
% 3.21/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_2279,c_2283]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_24,plain,
% 3.21/0.99      ( ~ v2_funct_1(X0)
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_42,negated_conjecture,
% 3.21/0.99      ( v2_funct_1(sK3) ),
% 3.21/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_486,plain,
% 3.21/0.99      ( ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.21/0.99      | sK3 != X0 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_42]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_487,plain,
% 3.21/0.99      ( ~ v1_funct_1(sK3)
% 3.21/0.99      | ~ v1_relat_1(sK3)
% 3.21/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_486]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_45,negated_conjecture,
% 3.21/0.99      ( v1_funct_1(sK3) ),
% 3.21/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_489,plain,
% 3.21/0.99      ( ~ v1_relat_1(sK3)
% 3.21/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_487,c_45]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2274,plain,
% 3.21/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.21/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3792,plain,
% 3.21/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_3740,c_2274]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_20,plain,
% 3.21/0.99      ( ~ v2_funct_1(X0)
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_514,plain,
% 3.21/0.99      ( ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.21/0.99      | sK3 != X0 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_42]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_515,plain,
% 3.21/0.99      ( ~ v1_funct_1(sK3)
% 3.21/0.99      | ~ v1_relat_1(sK3)
% 3.21/0.99      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_514]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_517,plain,
% 3.21/0.99      ( ~ v1_relat_1(sK3) | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_515,c_45]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2272,plain,
% 3.21/0.99      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 3.21/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3794,plain,
% 3.21/0.99      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_3740,c_2272]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3800,plain,
% 3.21/0.99      ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
% 3.21/0.99      inference(light_normalisation,[status(thm)],[c_3792,c_3794]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4538,plain,
% 3.21/0.99      ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_4531,c_3800]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_37,plain,
% 3.21/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.21/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_relat_1(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2280,plain,
% 3.21/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.21/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.21/0.99      | v1_funct_1(X0) != iProver_top
% 3.21/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5996,plain,
% 3.21/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.21/0.99      | r1_tarski(k2_relat_1(k4_relat_1(sK3)),X0) != iProver_top
% 3.21/0.99      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.21/0.99      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_4538,c_2280]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_23,plain,
% 3.21/0.99      ( ~ v2_funct_1(X0)
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_500,plain,
% 3.21/0.99      ( ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.21/0.99      | sK3 != X0 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_42]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_501,plain,
% 3.21/0.99      ( ~ v1_funct_1(sK3)
% 3.21/0.99      | ~ v1_relat_1(sK3)
% 3.21/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_500]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_503,plain,
% 3.21/0.99      ( ~ v1_relat_1(sK3)
% 3.21/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_501,c_45]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2273,plain,
% 3.21/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.21/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3793,plain,
% 3.21/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_3740,c_2273]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3797,plain,
% 3.21/0.99      ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
% 3.21/0.99      inference(light_normalisation,[status(thm)],[c_3793,c_3794]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6012,plain,
% 3.21/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.21/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.21/0.99      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.21/0.99      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.21/0.99      inference(light_normalisation,[status(thm)],[c_5996,c_3797]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_46,plain,
% 3.21/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_48,plain,
% 3.21/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2630,plain,
% 3.21/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.21/0.99      | v1_relat_1(sK3) ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2759,plain,
% 3.21/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.21/0.99      | v1_relat_1(sK3) ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_2630]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2760,plain,
% 3.21/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.21/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_2759]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_22,plain,
% 3.21/0.99      ( ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_relat_1(X0)
% 3.21/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 3.21/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2287,plain,
% 3.21/0.99      ( v1_funct_1(X0) != iProver_top
% 3.21/0.99      | v1_relat_1(X0) != iProver_top
% 3.21/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6064,plain,
% 3.21/0.99      ( v1_funct_1(sK3) != iProver_top
% 3.21/0.99      | v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 3.21/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_3794,c_2287]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_21,plain,
% 3.21/0.99      ( ~ v1_funct_1(X0)
% 3.21/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.21/0.99      | ~ v1_relat_1(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2288,plain,
% 3.21/0.99      ( v1_funct_1(X0) != iProver_top
% 3.21/0.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.21/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6154,plain,
% 3.21/0.99      ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
% 3.21/0.99      | v1_funct_1(sK3) != iProver_top
% 3.21/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_3794,c_2288]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_7189,plain,
% 3.21/0.99      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.21/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_6012,c_46,c_48,c_2760,c_6064,c_6154]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4,plain,
% 3.21/0.99      ( r1_tarski(X0,X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2295,plain,
% 3.21/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_7200,plain,
% 3.21/0.99      ( k1_relset_1(sK2,X0,k4_relat_1(sK3)) = k1_relat_1(k4_relat_1(sK3))
% 3.21/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_7189,c_2282]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_7214,plain,
% 3.21/0.99      ( k1_relset_1(sK2,X0,k4_relat_1(sK3)) = sK2
% 3.21/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.21/0.99      inference(light_normalisation,[status(thm)],[c_7200,c_4538]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_7673,plain,
% 3.21/0.99      ( k1_relset_1(sK2,X0,k4_relat_1(sK3)) = sK2
% 3.21/0.99      | sK2 = k1_xboole_0
% 3.21/0.99      | r1_tarski(sK1,X0) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_5562,c_7214]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_8085,plain,
% 3.21/0.99      ( k1_relset_1(sK2,sK1,k4_relat_1(sK3)) = sK2 | sK2 = k1_xboole_0 ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_2295,c_7673]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_34,plain,
% 3.21/0.99      ( v1_funct_2(X0,X1,X2)
% 3.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.21/0.99      | k1_xboole_0 = X2 ),
% 3.21/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_40,negated_conjecture,
% 3.21/0.99      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.21/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.21/0.99      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.21/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1205,plain,
% 3.21/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.21/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.21/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.21/0.99      | k2_funct_1(sK3) != X0
% 3.21/0.99      | sK1 != X2
% 3.21/0.99      | sK2 != X1
% 3.21/0.99      | k1_xboole_0 = X2 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_34,c_40]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1206,plain,
% 3.21/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.21/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.21/0.99      | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 3.21/0.99      | k1_xboole_0 = sK1 ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_1205]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2264,plain,
% 3.21/0.99      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 3.21/0.99      | k1_xboole_0 = sK1
% 3.21/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_1206]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3806,plain,
% 3.21/0.99      ( k1_relset_1(sK2,sK1,k4_relat_1(sK3)) != sK2
% 3.21/0.99      | sK1 = k1_xboole_0
% 3.21/0.99      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/0.99      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_3794,c_2264]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_9529,plain,
% 3.21/0.99      ( sK1 = k1_xboole_0
% 3.21/0.99      | sK2 = k1_xboole_0
% 3.21/0.99      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/0.99      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_8085,c_3806]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_26,plain,
% 3.21/0.99      ( v1_relat_1(k1_xboole_0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_88,plain,
% 3.21/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_25,plain,
% 3.21/0.99      ( v1_funct_1(k1_xboole_0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_89,plain,
% 3.21/0.99      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_14,plain,
% 3.21/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.21/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_9,plain,
% 3.21/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.21/0.99      | k1_xboole_0 = X0
% 3.21/0.99      | k1_xboole_0 = X1 ),
% 3.21/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_119,plain,
% 3.21/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.21/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_8,plain,
% 3.21/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.21/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_120,plain,
% 3.21/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6,plain,
% 3.21/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_121,plain,
% 3.21/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_123,plain,
% 3.21/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_121]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1590,plain,
% 3.21/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.21/0.99      theory(equality) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2679,plain,
% 3.21/0.99      ( ~ r1_tarski(X0,X1)
% 3.21/0.99      | r1_tarski(k2_relat_1(X2),X3)
% 3.21/0.99      | X3 != X1
% 3.21/0.99      | k2_relat_1(X2) != X0 ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_1590]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2680,plain,
% 3.21/0.99      ( X0 != X1
% 3.21/0.99      | k2_relat_1(X2) != X3
% 3.21/0.99      | r1_tarski(X3,X1) != iProver_top
% 3.21/0.99      | r1_tarski(k2_relat_1(X2),X0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_2679]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2682,plain,
% 3.21/0.99      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 3.21/0.99      | k1_xboole_0 != k1_xboole_0
% 3.21/0.99      | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 3.21/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_2680]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2735,plain,
% 3.21/0.99      ( ~ r1_tarski(X0,X1)
% 3.21/0.99      | r1_tarski(sK1,k1_xboole_0)
% 3.21/0.99      | sK1 != X0
% 3.21/0.99      | k1_xboole_0 != X1 ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_1590]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2736,plain,
% 3.21/0.99      ( sK1 != X0
% 3.21/0.99      | k1_xboole_0 != X1
% 3.21/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.21/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_2735]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2738,plain,
% 3.21/0.99      ( sK1 != k1_xboole_0
% 3.21/0.99      | k1_xboole_0 != k1_xboole_0
% 3.21/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 3.21/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_2736]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_31,plain,
% 3.21/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.21/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.21/1.00      | k1_xboole_0 = X0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1048,plain,
% 3.21/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.21/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.21/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.21/1.00      | k2_funct_1(sK3) != k1_xboole_0
% 3.21/1.00      | sK1 != k1_xboole_0
% 3.21/1.00      | sK2 != X0
% 3.21/1.00      | k1_xboole_0 = X0 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_40]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1049,plain,
% 3.21/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.21/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.21/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.21/1.00      | k2_funct_1(sK3) != k1_xboole_0
% 3.21/1.00      | sK1 != k1_xboole_0
% 3.21/1.00      | k1_xboole_0 = sK2 ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_1048]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2271,plain,
% 3.21/1.00      ( k2_funct_1(sK3) != k1_xboole_0
% 3.21/1.00      | sK1 != k1_xboole_0
% 3.21/1.00      | k1_xboole_0 = sK2
% 3.21/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.21/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1049]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7,plain,
% 3.21/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2514,plain,
% 3.21/1.00      ( k2_funct_1(sK3) != k1_xboole_0
% 3.21/1.00      | sK1 != k1_xboole_0
% 3.21/1.00      | sK2 = k1_xboole_0
% 3.21/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.21/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_2271,c_7]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2621,plain,
% 3.21/1.00      ( v1_funct_1(k2_funct_1(sK3))
% 3.21/1.00      | ~ v1_funct_1(sK3)
% 3.21/1.00      | ~ v1_relat_1(sK3) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2622,plain,
% 3.21/1.00      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.21/1.00      | v1_funct_1(sK3) != iProver_top
% 3.21/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_2621]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2864,plain,
% 3.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.21/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/1.00      | sK2 = k1_xboole_0
% 3.21/1.00      | sK1 != k1_xboole_0
% 3.21/1.00      | k2_funct_1(sK3) != k1_xboole_0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_2514,c_46,c_48,c_2622,c_2760]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2865,plain,
% 3.21/1.00      ( k2_funct_1(sK3) != k1_xboole_0
% 3.21/1.00      | sK1 != k1_xboole_0
% 3.21/1.00      | sK2 = k1_xboole_0
% 3.21/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_2864]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3804,plain,
% 3.21/1.00      ( k4_relat_1(sK3) != k1_xboole_0
% 3.21/1.00      | sK1 != k1_xboole_0
% 3.21/1.00      | sK2 = k1_xboole_0
% 3.21/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_3794,c_2865]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_32,plain,
% 3.21/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.21/1.00      | k1_xboole_0 = X1
% 3.21/1.00      | k1_xboole_0 = X0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_38,plain,
% 3.21/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.21/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | ~ v1_relat_1(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1074,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.21/1.00      | ~ r1_tarski(k2_relat_1(X2),X3)
% 3.21/1.00      | ~ v1_funct_1(X2)
% 3.21/1.00      | ~ v1_relat_1(X2)
% 3.21/1.00      | X2 != X0
% 3.21/1.00      | k1_relat_1(X2) != X1
% 3.21/1.00      | k1_xboole_0 != X3
% 3.21/1.00      | k1_xboole_0 = X0
% 3.21/1.00      | k1_xboole_0 = X1 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_38]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1075,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.21/1.00      | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | ~ v1_relat_1(X0)
% 3.21/1.00      | k1_xboole_0 = X0
% 3.21/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_1074]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1091,plain,
% 3.21/1.00      ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | ~ v1_relat_1(X0)
% 3.21/1.00      | k1_xboole_0 = X0
% 3.21/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.21/1.00      inference(forward_subsumption_resolution,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_1075,c_37]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2270,plain,
% 3.21/1.00      ( k1_xboole_0 = X0
% 3.21/1.00      | k1_xboole_0 = k1_relat_1(X0)
% 3.21/1.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1091]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4119,plain,
% 3.21/1.00      ( k1_relat_1(k4_relat_1(sK3)) = k1_xboole_0
% 3.21/1.00      | k4_relat_1(sK3) = k1_xboole_0
% 3.21/1.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.21/1.00      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_3797,c_2270]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5732,plain,
% 3.21/1.00      ( k4_relat_1(sK3) = k1_xboole_0
% 3.21/1.00      | sK2 = k1_xboole_0
% 3.21/1.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.21/1.00      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_4119,c_4538]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5739,plain,
% 3.21/1.00      ( k4_relat_1(sK3) = k1_xboole_0
% 3.21/1.00      | sK2 = k1_xboole_0
% 3.21/1.00      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.21/1.00      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_5562,c_5732]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5993,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.21/1.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_7,c_2280]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_6046,plain,
% 3.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.21/1.00      | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_5993]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9721,plain,
% 3.21/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/1.00      | sK2 = k1_xboole_0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_9529,c_46,c_48,c_88,c_89,c_14,c_119,c_120,c_123,
% 3.21/1.00                 c_2682,c_2738,c_2760,c_3804,c_5739,c_6046,c_6064,c_6154]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9722,plain,
% 3.21/1.00      ( sK2 = k1_xboole_0
% 3.21/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_9721]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9727,plain,
% 3.21/1.00      ( sK2 = k1_xboole_0
% 3.21/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_7189,c_9722]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1232,plain,
% 3.21/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.21/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.21/1.00      | ~ v1_relat_1(X0)
% 3.21/1.00      | k2_funct_1(sK3) != X0
% 3.21/1.00      | k1_relat_1(X0) != sK2
% 3.21/1.00      | sK1 != X1 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_38,c_40]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1233,plain,
% 3.21/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.21/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 3.21/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.21/1.00      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.21/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_1232]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1245,plain,
% 3.21/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.21/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 3.21/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.21/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.21/1.00      inference(forward_subsumption_resolution,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_1233,c_28]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2263,plain,
% 3.21/1.00      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.21/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 3.21/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1245]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3807,plain,
% 3.21/1.00      ( k1_relat_1(k4_relat_1(sK3)) != sK2
% 3.21/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/1.00      | r1_tarski(k2_relat_1(k4_relat_1(sK3)),sK1) != iProver_top
% 3.21/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_3794,c_2263]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4973,plain,
% 3.21/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/1.00      | r1_tarski(k2_relat_1(k4_relat_1(sK3)),sK1) != iProver_top
% 3.21/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_3807,c_4538]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4977,plain,
% 3.21/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.21/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 3.21/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.21/1.00      inference(light_normalisation,[status(thm)],[c_4973,c_3797]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7202,plain,
% 3.21/1.00      ( r1_tarski(k1_relat_1(sK3),sK1) != iProver_top
% 3.21/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_7189,c_4977]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9730,plain,
% 3.21/1.00      ( r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_9727,c_46,c_48,c_2760,c_6154,c_7202]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9735,plain,
% 3.21/1.00      ( sK2 = k1_xboole_0 | r1_tarski(sK1,sK1) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_5562,c_9730]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4706,plain,
% 3.21/1.00      ( r1_tarski(sK1,sK1) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4709,plain,
% 3.21/1.00      ( r1_tarski(sK1,sK1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_4706]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9814,plain,
% 3.21/1.00      ( sK2 = k1_xboole_0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_9735,c_4709]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4539,plain,
% 3.21/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(sK3) != iProver_top
% 3.21/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_4531,c_2270]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4800,plain,
% 3.21/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_4539,c_46,c_48,c_2760]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9847,plain,
% 3.21/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.21/1.00      | sK3 = k1_xboole_0
% 3.21/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_9814,c_4800]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_122,plain,
% 3.21/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2,plain,
% 3.21/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2703,plain,
% 3.21/1.00      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1586,plain,( X0 = X0 ),theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2719,plain,
% 3.21/1.00      ( sK3 = sK3 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1586]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2740,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,X1)
% 3.21/1.00      | r1_tarski(sK2,k1_xboole_0)
% 3.21/1.00      | sK2 != X0
% 3.21/1.00      | k1_xboole_0 != X1 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1590]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2742,plain,
% 3.21/1.00      ( r1_tarski(sK2,k1_xboole_0)
% 3.21/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.21/1.00      | sK2 != k1_xboole_0
% 3.21/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2740]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1587,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2762,plain,
% 3.21/1.00      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1587]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3352,plain,
% 3.21/1.00      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_2762]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3353,plain,
% 3.21/1.00      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_3352]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_0,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2299,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.21/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8365,plain,
% 3.21/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.21/1.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_funct_1(sK3) != iProver_top
% 3.21/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_4531,c_5993]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8482,plain,
% 3.21/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.21/1.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_8365,c_46,c_48,c_2760]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_10,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/1.00      | ~ r2_hidden(X2,X0)
% 3.21/1.00      | r2_hidden(X2,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2293,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.21/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.21/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8488,plain,
% 3.21/1.00      ( r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.21/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_8482,c_2293]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2294,plain,
% 3.21/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_27,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2284,plain,
% 3.21/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.21/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3728,plain,
% 3.21/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2294,c_2284]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9432,plain,
% 3.21/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 3.21/1.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_8488,c_3728]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9433,plain,
% 3.21/1.00      ( r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.21/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_9432]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9440,plain,
% 3.21/1.00      ( r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2299,c_9433]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9441,plain,
% 3.21/1.00      ( ~ r1_tarski(sK2,k1_xboole_0) | v1_xboole_0(sK3) ),
% 3.21/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_9440]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_10593,plain,
% 3.21/1.00      ( sK3 = k1_xboole_0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_9847,c_119,c_120,c_122,c_2703,c_2719,c_2742,c_3353,
% 3.21/1.00                 c_4709,c_9441,c_9735]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_10606,plain,
% 3.21/1.00      ( r1_tarski(k1_relat_1(k1_xboole_0),sK1) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_10593,c_9730]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_15,plain,
% 3.21/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_10628,plain,
% 3.21/1.00      ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.21/1.00      inference(light_normalisation,[status(thm)],[c_10606,c_15]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4915,plain,
% 3.21/1.00      ( r1_tarski(k1_xboole_0,sK1) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4918,plain,
% 3.21/1.00      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_4915]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(contradiction,plain,
% 3.21/1.00      ( $false ),
% 3.21/1.00      inference(minisat,[status(thm)],[c_10628,c_4918]) ).
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  ------                               Statistics
% 3.21/1.00  
% 3.21/1.00  ------ General
% 3.21/1.00  
% 3.21/1.00  abstr_ref_over_cycles:                  0
% 3.21/1.00  abstr_ref_under_cycles:                 0
% 3.21/1.00  gc_basic_clause_elim:                   0
% 3.21/1.00  forced_gc_time:                         0
% 3.21/1.00  parsing_time:                           0.011
% 3.21/1.00  unif_index_cands_time:                  0.
% 3.21/1.00  unif_index_add_time:                    0.
% 3.21/1.00  orderings_time:                         0.
% 3.21/1.00  out_proof_time:                         0.015
% 3.21/1.00  total_time:                             0.317
% 3.21/1.00  num_of_symbols:                         52
% 3.21/1.00  num_of_terms:                           6743
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing
% 3.21/1.00  
% 3.21/1.00  num_of_splits:                          0
% 3.21/1.00  num_of_split_atoms:                     0
% 3.21/1.00  num_of_reused_defs:                     0
% 3.21/1.00  num_eq_ax_congr_red:                    10
% 3.21/1.00  num_of_sem_filtered_clauses:            1
% 3.21/1.00  num_of_subtypes:                        0
% 3.21/1.00  monotx_restored_types:                  0
% 3.21/1.00  sat_num_of_epr_types:                   0
% 3.21/1.00  sat_num_of_non_cyclic_types:            0
% 3.21/1.00  sat_guarded_non_collapsed_types:        0
% 3.21/1.00  num_pure_diseq_elim:                    0
% 3.21/1.00  simp_replaced_by:                       0
% 3.21/1.00  res_preprocessed:                       210
% 3.21/1.00  prep_upred:                             0
% 3.21/1.00  prep_unflattend:                        66
% 3.21/1.00  smt_new_axioms:                         0
% 3.21/1.00  pred_elim_cands:                        6
% 3.21/1.00  pred_elim:                              2
% 3.21/1.00  pred_elim_cl:                           -3
% 3.21/1.00  pred_elim_cycles:                       5
% 3.21/1.00  merged_defs:                            0
% 3.21/1.00  merged_defs_ncl:                        0
% 3.21/1.00  bin_hyper_res:                          0
% 3.21/1.00  prep_cycles:                            4
% 3.21/1.00  pred_elim_time:                         0.02
% 3.21/1.00  splitting_time:                         0.
% 3.21/1.00  sem_filter_time:                        0.
% 3.21/1.00  monotx_time:                            0.
% 3.21/1.00  subtype_inf_time:                       0.
% 3.21/1.00  
% 3.21/1.00  ------ Problem properties
% 3.21/1.00  
% 3.21/1.00  clauses:                                45
% 3.21/1.00  conjectures:                            3
% 3.21/1.00  epr:                                    11
% 3.21/1.00  horn:                                   39
% 3.21/1.00  ground:                                 18
% 3.21/1.00  unary:                                  11
% 3.21/1.00  binary:                                 18
% 3.21/1.00  lits:                                   111
% 3.21/1.00  lits_eq:                                41
% 3.21/1.00  fd_pure:                                0
% 3.21/1.00  fd_pseudo:                              0
% 3.21/1.00  fd_cond:                                4
% 3.21/1.00  fd_pseudo_cond:                         1
% 3.21/1.00  ac_symbols:                             0
% 3.21/1.00  
% 3.21/1.00  ------ Propositional Solver
% 3.21/1.00  
% 3.21/1.00  prop_solver_calls:                      29
% 3.21/1.00  prop_fast_solver_calls:                 1671
% 3.21/1.00  smt_solver_calls:                       0
% 3.21/1.00  smt_fast_solver_calls:                  0
% 3.21/1.00  prop_num_of_clauses:                    3516
% 3.21/1.00  prop_preprocess_simplified:             11150
% 3.21/1.00  prop_fo_subsumed:                       53
% 3.21/1.00  prop_solver_time:                       0.
% 3.21/1.00  smt_solver_time:                        0.
% 3.21/1.00  smt_fast_solver_time:                   0.
% 3.21/1.00  prop_fast_solver_time:                  0.
% 3.21/1.00  prop_unsat_core_time:                   0.
% 3.21/1.00  
% 3.21/1.00  ------ QBF
% 3.21/1.00  
% 3.21/1.00  qbf_q_res:                              0
% 3.21/1.00  qbf_num_tautologies:                    0
% 3.21/1.00  qbf_prep_cycles:                        0
% 3.21/1.00  
% 3.21/1.00  ------ BMC1
% 3.21/1.00  
% 3.21/1.00  bmc1_current_bound:                     -1
% 3.21/1.00  bmc1_last_solved_bound:                 -1
% 3.21/1.00  bmc1_unsat_core_size:                   -1
% 3.21/1.00  bmc1_unsat_core_parents_size:           -1
% 3.21/1.00  bmc1_merge_next_fun:                    0
% 3.21/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation
% 3.21/1.00  
% 3.21/1.00  inst_num_of_clauses:                    1233
% 3.21/1.00  inst_num_in_passive:                    528
% 3.21/1.00  inst_num_in_active:                     567
% 3.21/1.00  inst_num_in_unprocessed:                138
% 3.21/1.00  inst_num_of_loops:                      710
% 3.21/1.00  inst_num_of_learning_restarts:          0
% 3.21/1.00  inst_num_moves_active_passive:          139
% 3.21/1.00  inst_lit_activity:                      0
% 3.21/1.00  inst_lit_activity_moves:                0
% 3.21/1.00  inst_num_tautologies:                   0
% 3.21/1.00  inst_num_prop_implied:                  0
% 3.21/1.00  inst_num_existing_simplified:           0
% 3.21/1.00  inst_num_eq_res_simplified:             0
% 3.21/1.00  inst_num_child_elim:                    0
% 3.21/1.00  inst_num_of_dismatching_blockings:      220
% 3.21/1.00  inst_num_of_non_proper_insts:           1175
% 3.21/1.00  inst_num_of_duplicates:                 0
% 3.21/1.00  inst_inst_num_from_inst_to_res:         0
% 3.21/1.00  inst_dismatching_checking_time:         0.
% 3.21/1.00  
% 3.21/1.00  ------ Resolution
% 3.21/1.00  
% 3.21/1.00  res_num_of_clauses:                     0
% 3.21/1.00  res_num_in_passive:                     0
% 3.21/1.00  res_num_in_active:                      0
% 3.21/1.00  res_num_of_loops:                       214
% 3.21/1.00  res_forward_subset_subsumed:            78
% 3.21/1.00  res_backward_subset_subsumed:           4
% 3.21/1.00  res_forward_subsumed:                   0
% 3.21/1.00  res_backward_subsumed:                  0
% 3.21/1.00  res_forward_subsumption_resolution:     3
% 3.21/1.00  res_backward_subsumption_resolution:    0
% 3.21/1.00  res_clause_to_clause_subsumption:       549
% 3.21/1.00  res_orphan_elimination:                 0
% 3.21/1.00  res_tautology_del:                      103
% 3.21/1.00  res_num_eq_res_simplified:              0
% 3.21/1.00  res_num_sel_changes:                    0
% 3.21/1.00  res_moves_from_active_to_pass:          0
% 3.21/1.00  
% 3.21/1.00  ------ Superposition
% 3.21/1.00  
% 3.21/1.00  sup_time_total:                         0.
% 3.21/1.00  sup_time_generating:                    0.
% 3.21/1.00  sup_time_sim_full:                      0.
% 3.21/1.00  sup_time_sim_immed:                     0.
% 3.21/1.00  
% 3.21/1.00  sup_num_of_clauses:                     99
% 3.21/1.00  sup_num_in_active:                      55
% 3.21/1.00  sup_num_in_passive:                     44
% 3.21/1.00  sup_num_of_loops:                       140
% 3.21/1.00  sup_fw_superposition:                   77
% 3.21/1.00  sup_bw_superposition:                   78
% 3.21/1.00  sup_immediate_simplified:               77
% 3.21/1.00  sup_given_eliminated:                   0
% 3.21/1.00  comparisons_done:                       0
% 3.21/1.00  comparisons_avoided:                    8
% 3.21/1.00  
% 3.21/1.00  ------ Simplifications
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  sim_fw_subset_subsumed:                 20
% 3.21/1.00  sim_bw_subset_subsumed:                 26
% 3.21/1.00  sim_fw_subsumed:                        4
% 3.21/1.00  sim_bw_subsumed:                        1
% 3.21/1.00  sim_fw_subsumption_res:                 4
% 3.21/1.00  sim_bw_subsumption_res:                 0
% 3.21/1.00  sim_tautology_del:                      3
% 3.21/1.00  sim_eq_tautology_del:                   24
% 3.21/1.00  sim_eq_res_simp:                        3
% 3.21/1.00  sim_fw_demodulated:                     13
% 3.21/1.00  sim_bw_demodulated:                     71
% 3.21/1.00  sim_light_normalised:                   46
% 3.21/1.00  sim_joinable_taut:                      0
% 3.21/1.00  sim_joinable_simp:                      0
% 3.21/1.00  sim_ac_normalised:                      0
% 3.21/1.00  sim_smt_subsumption:                    0
% 3.21/1.00  
%------------------------------------------------------------------------------

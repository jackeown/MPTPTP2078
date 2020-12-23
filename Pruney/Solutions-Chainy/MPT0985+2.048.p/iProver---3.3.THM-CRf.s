%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:29 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  208 (10898 expanded)
%              Number of clauses        :  135 (3424 expanded)
%              Number of leaves         :   16 (2105 expanded)
%              Depth                    :   28
%              Number of atoms          :  649 (58512 expanded)
%              Number of equality atoms :  330 (10787 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f90,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f51,plain,(
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

fof(f52,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f64,plain,
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

fof(f65,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f52,f64])).

fof(f114,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f111,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f113,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f65])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f55])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f119,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f71])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f104,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f49])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f103,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f85,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f120,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f70])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f115,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f65])).

fof(f89,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f65])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f122,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f108])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_47,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_570,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_47])).

cnf(c_571,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_50,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_573,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_50])).

cnf(c_1435,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_48,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1534,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1605,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_1736,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1435,c_50,c_48,c_571,c_1605])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_36,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1449,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1446,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4751,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1449,c_1446])).

cnf(c_37,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_63,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_12946,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4751,c_63])).

cnf(c_12952,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_12946])).

cnf(c_12984,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1736,c_12952])).

cnf(c_12987,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12984,c_1736])).

cnf(c_51,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_53,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1526,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1527,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1526])).

cnf(c_1606,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1605])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1861,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1862,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1861])).

cnf(c_13472,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12987,c_51,c_53,c_1527,c_1606,c_1862])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_26,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1454,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2692,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1454])).

cnf(c_13478,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v5_relat_1(k2_funct_1(sK4),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13472,c_2692])).

cnf(c_1442,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_27,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_27,c_9])).

cnf(c_506,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_25])).

cnf(c_507,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_506])).

cnf(c_1438,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_2365,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1442,c_1438])).

cnf(c_4746,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1736,c_1449])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1453,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3509,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1442,c_1453])).

cnf(c_46,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3512,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3509,c_46])).

cnf(c_24,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_556,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_47])).

cnf(c_557,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_559,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_50])).

cnf(c_1436,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_559])).

cnf(c_1787,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1436,c_50,c_48,c_557,c_1605])).

cnf(c_3609,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3512,c_1787])).

cnf(c_4753,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4746,c_3609])).

cnf(c_5659,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4753,c_51,c_53,c_1527,c_1606,c_1862])).

cnf(c_42,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1444,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_5670,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
    | v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5659,c_1444])).

cnf(c_1448,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4645,plain,
    ( v1_funct_2(k2_funct_1(sK4),k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1736,c_1448])).

cnf(c_4646,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4645,c_3609])).

cnf(c_12850,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5670,c_51,c_53,c_1527,c_1606,c_1862,c_4646])).

cnf(c_12851,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12850])).

cnf(c_12954,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK4)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3609,c_12946])).

cnf(c_12963,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12954,c_1736])).

cnf(c_12964,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12963,c_1736])).

cnf(c_5669,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5659,c_1446])).

cnf(c_13868,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12964,c_51,c_53,c_1527,c_1606,c_1862,c_4646,c_5669])).

cnf(c_45,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1443,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_55,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_1731,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1443,c_51,c_53,c_55,c_1527,c_1606])).

cnf(c_1732,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1731])).

cnf(c_13881,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13868,c_1732])).

cnf(c_14078,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13881,c_2365])).

cnf(c_14079,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_14078])).

cnf(c_14082,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_12851,c_14079])).

cnf(c_14223,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13478,c_2365,c_14082])).

cnf(c_5360,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4646,c_51,c_53,c_1527,c_1606,c_1862])).

cnf(c_14257,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14223,c_5360])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1464,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2963,plain,
    ( k2_funct_1(sK4) = k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1736,c_1464])).

cnf(c_2965,plain,
    ( ~ v1_relat_1(k2_funct_1(sK4))
    | k2_funct_1(sK4) = k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2963])).

cnf(c_3048,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | k2_funct_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2963,c_50,c_48,c_1605,c_1861,c_2965])).

cnf(c_3049,plain,
    ( k2_funct_1(sK4) = k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3048])).

cnf(c_14265,plain,
    ( k2_funct_1(sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14223,c_3049])).

cnf(c_14268,plain,
    ( k2_funct_1(sK4) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_14265])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1462,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3350,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1736,c_1462])).

cnf(c_3351,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3350,c_1787])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1984,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) = k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3356,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | k2_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3351,c_48,c_1605,c_1984])).

cnf(c_3357,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3356])).

cnf(c_3606,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3512,c_3357])).

cnf(c_14264,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14223,c_3606])).

cnf(c_14270,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_14264])).

cnf(c_14277,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14257,c_14268,c_14270])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_funct_2(X0,k1_xboole_0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1445,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_1472,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1445,c_4])).

cnf(c_15771,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14277,c_1472])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_144,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_146,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X1)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1776,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1777,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1776])).

cnf(c_1779,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_1864,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1865,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1864])).

cnf(c_1469,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2688,plain,
    ( v5_relat_1(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_1454])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1466,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4277,plain,
    ( v5_relat_1(k2_funct_1(sK4),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1736,c_1466])).

cnf(c_4455,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | v5_relat_1(k2_funct_1(sK4),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4277,c_51,c_53,c_1606,c_1862])).

cnf(c_4456,plain,
    ( v5_relat_1(k2_funct_1(sK4),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4455])).

cnf(c_14262,plain,
    ( v5_relat_1(k2_funct_1(sK4),X0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14223,c_4456])).

cnf(c_14271,plain,
    ( v5_relat_1(k1_xboole_0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14262,c_14268])).

cnf(c_16271,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15771,c_51,c_53,c_146,c_1606,c_1779,c_1865,c_2688,c_14271])).

cnf(c_14545,plain,
    ( v1_funct_2(k2_funct_1(sK4),k1_xboole_0,sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14270,c_1732])).

cnf(c_14550,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14545,c_14268])).

cnf(c_14551,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14550,c_4])).

cnf(c_14731,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14551,c_146])).

cnf(c_16276,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_16271,c_14731])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:14:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.62/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.02  
% 3.62/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/1.02  
% 3.62/1.02  ------  iProver source info
% 3.62/1.02  
% 3.62/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.62/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/1.02  git: non_committed_changes: false
% 3.62/1.02  git: last_make_outside_of_git: false
% 3.62/1.02  
% 3.62/1.02  ------ 
% 3.62/1.02  
% 3.62/1.02  ------ Input Options
% 3.62/1.02  
% 3.62/1.02  --out_options                           all
% 3.62/1.02  --tptp_safe_out                         true
% 3.62/1.02  --problem_path                          ""
% 3.62/1.02  --include_path                          ""
% 3.62/1.02  --clausifier                            res/vclausify_rel
% 3.62/1.02  --clausifier_options                    ""
% 3.62/1.02  --stdin                                 false
% 3.62/1.02  --stats_out                             all
% 3.62/1.02  
% 3.62/1.02  ------ General Options
% 3.62/1.02  
% 3.62/1.02  --fof                                   false
% 3.62/1.02  --time_out_real                         305.
% 3.62/1.02  --time_out_virtual                      -1.
% 3.62/1.02  --symbol_type_check                     false
% 3.62/1.02  --clausify_out                          false
% 3.62/1.02  --sig_cnt_out                           false
% 3.62/1.02  --trig_cnt_out                          false
% 3.62/1.02  --trig_cnt_out_tolerance                1.
% 3.62/1.02  --trig_cnt_out_sk_spl                   false
% 3.62/1.02  --abstr_cl_out                          false
% 3.62/1.02  
% 3.62/1.02  ------ Global Options
% 3.62/1.02  
% 3.62/1.02  --schedule                              default
% 3.62/1.02  --add_important_lit                     false
% 3.62/1.02  --prop_solver_per_cl                    1000
% 3.62/1.02  --min_unsat_core                        false
% 3.62/1.02  --soft_assumptions                      false
% 3.62/1.02  --soft_lemma_size                       3
% 3.62/1.02  --prop_impl_unit_size                   0
% 3.62/1.02  --prop_impl_unit                        []
% 3.62/1.02  --share_sel_clauses                     true
% 3.62/1.02  --reset_solvers                         false
% 3.62/1.02  --bc_imp_inh                            [conj_cone]
% 3.62/1.02  --conj_cone_tolerance                   3.
% 3.62/1.02  --extra_neg_conj                        none
% 3.62/1.02  --large_theory_mode                     true
% 3.62/1.02  --prolific_symb_bound                   200
% 3.62/1.02  --lt_threshold                          2000
% 3.62/1.02  --clause_weak_htbl                      true
% 3.62/1.02  --gc_record_bc_elim                     false
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing Options
% 3.62/1.02  
% 3.62/1.02  --preprocessing_flag                    true
% 3.62/1.02  --time_out_prep_mult                    0.1
% 3.62/1.02  --splitting_mode                        input
% 3.62/1.02  --splitting_grd                         true
% 3.62/1.02  --splitting_cvd                         false
% 3.62/1.02  --splitting_cvd_svl                     false
% 3.62/1.02  --splitting_nvd                         32
% 3.62/1.02  --sub_typing                            true
% 3.62/1.02  --prep_gs_sim                           true
% 3.62/1.02  --prep_unflatten                        true
% 3.62/1.02  --prep_res_sim                          true
% 3.62/1.02  --prep_upred                            true
% 3.62/1.02  --prep_sem_filter                       exhaustive
% 3.62/1.02  --prep_sem_filter_out                   false
% 3.62/1.02  --pred_elim                             true
% 3.62/1.02  --res_sim_input                         true
% 3.62/1.02  --eq_ax_congr_red                       true
% 3.62/1.02  --pure_diseq_elim                       true
% 3.62/1.02  --brand_transform                       false
% 3.62/1.02  --non_eq_to_eq                          false
% 3.62/1.02  --prep_def_merge                        true
% 3.62/1.02  --prep_def_merge_prop_impl              false
% 3.62/1.02  --prep_def_merge_mbd                    true
% 3.62/1.02  --prep_def_merge_tr_red                 false
% 3.62/1.02  --prep_def_merge_tr_cl                  false
% 3.62/1.02  --smt_preprocessing                     true
% 3.62/1.02  --smt_ac_axioms                         fast
% 3.62/1.02  --preprocessed_out                      false
% 3.62/1.02  --preprocessed_stats                    false
% 3.62/1.02  
% 3.62/1.02  ------ Abstraction refinement Options
% 3.62/1.02  
% 3.62/1.02  --abstr_ref                             []
% 3.62/1.02  --abstr_ref_prep                        false
% 3.62/1.02  --abstr_ref_until_sat                   false
% 3.62/1.02  --abstr_ref_sig_restrict                funpre
% 3.62/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/1.02  --abstr_ref_under                       []
% 3.62/1.02  
% 3.62/1.02  ------ SAT Options
% 3.62/1.02  
% 3.62/1.02  --sat_mode                              false
% 3.62/1.02  --sat_fm_restart_options                ""
% 3.62/1.02  --sat_gr_def                            false
% 3.62/1.02  --sat_epr_types                         true
% 3.62/1.02  --sat_non_cyclic_types                  false
% 3.62/1.02  --sat_finite_models                     false
% 3.62/1.02  --sat_fm_lemmas                         false
% 3.62/1.02  --sat_fm_prep                           false
% 3.62/1.02  --sat_fm_uc_incr                        true
% 3.62/1.02  --sat_out_model                         small
% 3.62/1.02  --sat_out_clauses                       false
% 3.62/1.02  
% 3.62/1.02  ------ QBF Options
% 3.62/1.02  
% 3.62/1.02  --qbf_mode                              false
% 3.62/1.02  --qbf_elim_univ                         false
% 3.62/1.02  --qbf_dom_inst                          none
% 3.62/1.02  --qbf_dom_pre_inst                      false
% 3.62/1.02  --qbf_sk_in                             false
% 3.62/1.02  --qbf_pred_elim                         true
% 3.62/1.02  --qbf_split                             512
% 3.62/1.02  
% 3.62/1.02  ------ BMC1 Options
% 3.62/1.02  
% 3.62/1.02  --bmc1_incremental                      false
% 3.62/1.02  --bmc1_axioms                           reachable_all
% 3.62/1.02  --bmc1_min_bound                        0
% 3.62/1.02  --bmc1_max_bound                        -1
% 3.62/1.02  --bmc1_max_bound_default                -1
% 3.62/1.02  --bmc1_symbol_reachability              true
% 3.62/1.02  --bmc1_property_lemmas                  false
% 3.62/1.02  --bmc1_k_induction                      false
% 3.62/1.02  --bmc1_non_equiv_states                 false
% 3.62/1.02  --bmc1_deadlock                         false
% 3.62/1.02  --bmc1_ucm                              false
% 3.62/1.02  --bmc1_add_unsat_core                   none
% 3.62/1.02  --bmc1_unsat_core_children              false
% 3.62/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/1.02  --bmc1_out_stat                         full
% 3.62/1.02  --bmc1_ground_init                      false
% 3.62/1.02  --bmc1_pre_inst_next_state              false
% 3.62/1.02  --bmc1_pre_inst_state                   false
% 3.62/1.02  --bmc1_pre_inst_reach_state             false
% 3.62/1.02  --bmc1_out_unsat_core                   false
% 3.62/1.02  --bmc1_aig_witness_out                  false
% 3.62/1.02  --bmc1_verbose                          false
% 3.62/1.02  --bmc1_dump_clauses_tptp                false
% 3.62/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.62/1.02  --bmc1_dump_file                        -
% 3.62/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.62/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.62/1.02  --bmc1_ucm_extend_mode                  1
% 3.62/1.02  --bmc1_ucm_init_mode                    2
% 3.62/1.02  --bmc1_ucm_cone_mode                    none
% 3.62/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.62/1.02  --bmc1_ucm_relax_model                  4
% 3.62/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.62/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/1.02  --bmc1_ucm_layered_model                none
% 3.62/1.02  --bmc1_ucm_max_lemma_size               10
% 3.62/1.02  
% 3.62/1.02  ------ AIG Options
% 3.62/1.02  
% 3.62/1.02  --aig_mode                              false
% 3.62/1.02  
% 3.62/1.02  ------ Instantiation Options
% 3.62/1.02  
% 3.62/1.02  --instantiation_flag                    true
% 3.62/1.02  --inst_sos_flag                         true
% 3.62/1.02  --inst_sos_phase                        true
% 3.62/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/1.02  --inst_lit_sel_side                     num_symb
% 3.62/1.02  --inst_solver_per_active                1400
% 3.62/1.02  --inst_solver_calls_frac                1.
% 3.62/1.02  --inst_passive_queue_type               priority_queues
% 3.62/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/1.02  --inst_passive_queues_freq              [25;2]
% 3.62/1.02  --inst_dismatching                      true
% 3.62/1.02  --inst_eager_unprocessed_to_passive     true
% 3.62/1.02  --inst_prop_sim_given                   true
% 3.62/1.02  --inst_prop_sim_new                     false
% 3.62/1.02  --inst_subs_new                         false
% 3.62/1.02  --inst_eq_res_simp                      false
% 3.62/1.02  --inst_subs_given                       false
% 3.62/1.02  --inst_orphan_elimination               true
% 3.62/1.02  --inst_learning_loop_flag               true
% 3.62/1.02  --inst_learning_start                   3000
% 3.62/1.02  --inst_learning_factor                  2
% 3.62/1.02  --inst_start_prop_sim_after_learn       3
% 3.62/1.02  --inst_sel_renew                        solver
% 3.62/1.02  --inst_lit_activity_flag                true
% 3.62/1.02  --inst_restr_to_given                   false
% 3.62/1.02  --inst_activity_threshold               500
% 3.62/1.02  --inst_out_proof                        true
% 3.62/1.02  
% 3.62/1.02  ------ Resolution Options
% 3.62/1.02  
% 3.62/1.02  --resolution_flag                       true
% 3.62/1.02  --res_lit_sel                           adaptive
% 3.62/1.02  --res_lit_sel_side                      none
% 3.62/1.02  --res_ordering                          kbo
% 3.62/1.02  --res_to_prop_solver                    active
% 3.62/1.02  --res_prop_simpl_new                    false
% 3.62/1.02  --res_prop_simpl_given                  true
% 3.62/1.02  --res_passive_queue_type                priority_queues
% 3.62/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/1.02  --res_passive_queues_freq               [15;5]
% 3.62/1.02  --res_forward_subs                      full
% 3.62/1.02  --res_backward_subs                     full
% 3.62/1.02  --res_forward_subs_resolution           true
% 3.62/1.02  --res_backward_subs_resolution          true
% 3.62/1.02  --res_orphan_elimination                true
% 3.62/1.02  --res_time_limit                        2.
% 3.62/1.02  --res_out_proof                         true
% 3.62/1.02  
% 3.62/1.02  ------ Superposition Options
% 3.62/1.02  
% 3.62/1.02  --superposition_flag                    true
% 3.62/1.02  --sup_passive_queue_type                priority_queues
% 3.62/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.62/1.02  --demod_completeness_check              fast
% 3.62/1.02  --demod_use_ground                      true
% 3.62/1.02  --sup_to_prop_solver                    passive
% 3.62/1.02  --sup_prop_simpl_new                    true
% 3.62/1.02  --sup_prop_simpl_given                  true
% 3.62/1.02  --sup_fun_splitting                     true
% 3.62/1.02  --sup_smt_interval                      50000
% 3.62/1.02  
% 3.62/1.02  ------ Superposition Simplification Setup
% 3.62/1.02  
% 3.62/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.62/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.62/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.62/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.62/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.62/1.02  --sup_immed_triv                        [TrivRules]
% 3.62/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.02  --sup_immed_bw_main                     []
% 3.62/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.62/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.02  --sup_input_bw                          []
% 3.62/1.02  
% 3.62/1.02  ------ Combination Options
% 3.62/1.02  
% 3.62/1.02  --comb_res_mult                         3
% 3.62/1.02  --comb_sup_mult                         2
% 3.62/1.02  --comb_inst_mult                        10
% 3.62/1.02  
% 3.62/1.02  ------ Debug Options
% 3.62/1.02  
% 3.62/1.02  --dbg_backtrace                         false
% 3.62/1.02  --dbg_dump_prop_clauses                 false
% 3.62/1.02  --dbg_dump_prop_clauses_file            -
% 3.62/1.02  --dbg_out_stat                          false
% 3.62/1.02  ------ Parsing...
% 3.62/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.02  ------ Proving...
% 3.62/1.02  ------ Problem Properties 
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  clauses                                 43
% 3.62/1.02  conjectures                             5
% 3.62/1.02  EPR                                     6
% 3.62/1.02  Horn                                    40
% 3.62/1.02  unary                                   17
% 3.62/1.02  binary                                  6
% 3.62/1.02  lits                                    101
% 3.62/1.02  lits eq                                 22
% 3.62/1.02  fd_pure                                 0
% 3.62/1.02  fd_pseudo                               0
% 3.62/1.02  fd_cond                                 5
% 3.62/1.02  fd_pseudo_cond                          1
% 3.62/1.02  AC symbols                              0
% 3.62/1.02  
% 3.62/1.02  ------ Schedule dynamic 5 is on 
% 3.62/1.02  
% 3.62/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  ------ 
% 3.62/1.02  Current options:
% 3.62/1.02  ------ 
% 3.62/1.02  
% 3.62/1.02  ------ Input Options
% 3.62/1.02  
% 3.62/1.02  --out_options                           all
% 3.62/1.02  --tptp_safe_out                         true
% 3.62/1.02  --problem_path                          ""
% 3.62/1.02  --include_path                          ""
% 3.62/1.02  --clausifier                            res/vclausify_rel
% 3.62/1.02  --clausifier_options                    ""
% 3.62/1.02  --stdin                                 false
% 3.62/1.02  --stats_out                             all
% 3.62/1.02  
% 3.62/1.02  ------ General Options
% 3.62/1.02  
% 3.62/1.02  --fof                                   false
% 3.62/1.02  --time_out_real                         305.
% 3.62/1.02  --time_out_virtual                      -1.
% 3.62/1.02  --symbol_type_check                     false
% 3.62/1.02  --clausify_out                          false
% 3.62/1.02  --sig_cnt_out                           false
% 3.62/1.02  --trig_cnt_out                          false
% 3.62/1.02  --trig_cnt_out_tolerance                1.
% 3.62/1.02  --trig_cnt_out_sk_spl                   false
% 3.62/1.02  --abstr_cl_out                          false
% 3.62/1.02  
% 3.62/1.02  ------ Global Options
% 3.62/1.02  
% 3.62/1.02  --schedule                              default
% 3.62/1.02  --add_important_lit                     false
% 3.62/1.02  --prop_solver_per_cl                    1000
% 3.62/1.02  --min_unsat_core                        false
% 3.62/1.02  --soft_assumptions                      false
% 3.62/1.02  --soft_lemma_size                       3
% 3.62/1.02  --prop_impl_unit_size                   0
% 3.62/1.02  --prop_impl_unit                        []
% 3.62/1.02  --share_sel_clauses                     true
% 3.62/1.02  --reset_solvers                         false
% 3.62/1.02  --bc_imp_inh                            [conj_cone]
% 3.62/1.02  --conj_cone_tolerance                   3.
% 3.62/1.02  --extra_neg_conj                        none
% 3.62/1.02  --large_theory_mode                     true
% 3.62/1.02  --prolific_symb_bound                   200
% 3.62/1.02  --lt_threshold                          2000
% 3.62/1.02  --clause_weak_htbl                      true
% 3.62/1.02  --gc_record_bc_elim                     false
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing Options
% 3.62/1.02  
% 3.62/1.02  --preprocessing_flag                    true
% 3.62/1.02  --time_out_prep_mult                    0.1
% 3.62/1.02  --splitting_mode                        input
% 3.62/1.02  --splitting_grd                         true
% 3.62/1.02  --splitting_cvd                         false
% 3.62/1.02  --splitting_cvd_svl                     false
% 3.62/1.02  --splitting_nvd                         32
% 3.62/1.02  --sub_typing                            true
% 3.62/1.02  --prep_gs_sim                           true
% 3.62/1.02  --prep_unflatten                        true
% 3.62/1.02  --prep_res_sim                          true
% 3.62/1.02  --prep_upred                            true
% 3.62/1.02  --prep_sem_filter                       exhaustive
% 3.62/1.02  --prep_sem_filter_out                   false
% 3.62/1.02  --pred_elim                             true
% 3.62/1.02  --res_sim_input                         true
% 3.62/1.02  --eq_ax_congr_red                       true
% 3.62/1.02  --pure_diseq_elim                       true
% 3.62/1.02  --brand_transform                       false
% 3.62/1.02  --non_eq_to_eq                          false
% 3.62/1.02  --prep_def_merge                        true
% 3.62/1.02  --prep_def_merge_prop_impl              false
% 3.62/1.02  --prep_def_merge_mbd                    true
% 3.62/1.02  --prep_def_merge_tr_red                 false
% 3.62/1.02  --prep_def_merge_tr_cl                  false
% 3.62/1.02  --smt_preprocessing                     true
% 3.62/1.02  --smt_ac_axioms                         fast
% 3.62/1.02  --preprocessed_out                      false
% 3.62/1.02  --preprocessed_stats                    false
% 3.62/1.02  
% 3.62/1.02  ------ Abstraction refinement Options
% 3.62/1.02  
% 3.62/1.02  --abstr_ref                             []
% 3.62/1.02  --abstr_ref_prep                        false
% 3.62/1.02  --abstr_ref_until_sat                   false
% 3.62/1.02  --abstr_ref_sig_restrict                funpre
% 3.62/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/1.02  --abstr_ref_under                       []
% 3.62/1.02  
% 3.62/1.02  ------ SAT Options
% 3.62/1.02  
% 3.62/1.02  --sat_mode                              false
% 3.62/1.02  --sat_fm_restart_options                ""
% 3.62/1.02  --sat_gr_def                            false
% 3.62/1.02  --sat_epr_types                         true
% 3.62/1.02  --sat_non_cyclic_types                  false
% 3.62/1.02  --sat_finite_models                     false
% 3.62/1.02  --sat_fm_lemmas                         false
% 3.62/1.02  --sat_fm_prep                           false
% 3.62/1.02  --sat_fm_uc_incr                        true
% 3.62/1.02  --sat_out_model                         small
% 3.62/1.02  --sat_out_clauses                       false
% 3.62/1.02  
% 3.62/1.02  ------ QBF Options
% 3.62/1.02  
% 3.62/1.02  --qbf_mode                              false
% 3.62/1.02  --qbf_elim_univ                         false
% 3.62/1.02  --qbf_dom_inst                          none
% 3.62/1.02  --qbf_dom_pre_inst                      false
% 3.62/1.02  --qbf_sk_in                             false
% 3.62/1.02  --qbf_pred_elim                         true
% 3.62/1.02  --qbf_split                             512
% 3.62/1.02  
% 3.62/1.02  ------ BMC1 Options
% 3.62/1.02  
% 3.62/1.02  --bmc1_incremental                      false
% 3.62/1.02  --bmc1_axioms                           reachable_all
% 3.62/1.02  --bmc1_min_bound                        0
% 3.62/1.02  --bmc1_max_bound                        -1
% 3.62/1.02  --bmc1_max_bound_default                -1
% 3.62/1.02  --bmc1_symbol_reachability              true
% 3.62/1.02  --bmc1_property_lemmas                  false
% 3.62/1.02  --bmc1_k_induction                      false
% 3.62/1.02  --bmc1_non_equiv_states                 false
% 3.62/1.02  --bmc1_deadlock                         false
% 3.62/1.02  --bmc1_ucm                              false
% 3.62/1.02  --bmc1_add_unsat_core                   none
% 3.62/1.02  --bmc1_unsat_core_children              false
% 3.62/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/1.02  --bmc1_out_stat                         full
% 3.62/1.02  --bmc1_ground_init                      false
% 3.62/1.02  --bmc1_pre_inst_next_state              false
% 3.62/1.02  --bmc1_pre_inst_state                   false
% 3.62/1.02  --bmc1_pre_inst_reach_state             false
% 3.62/1.02  --bmc1_out_unsat_core                   false
% 3.62/1.02  --bmc1_aig_witness_out                  false
% 3.62/1.02  --bmc1_verbose                          false
% 3.62/1.02  --bmc1_dump_clauses_tptp                false
% 3.62/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.62/1.02  --bmc1_dump_file                        -
% 3.62/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.62/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.62/1.02  --bmc1_ucm_extend_mode                  1
% 3.62/1.02  --bmc1_ucm_init_mode                    2
% 3.62/1.02  --bmc1_ucm_cone_mode                    none
% 3.62/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.62/1.02  --bmc1_ucm_relax_model                  4
% 3.62/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.62/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/1.02  --bmc1_ucm_layered_model                none
% 3.62/1.02  --bmc1_ucm_max_lemma_size               10
% 3.62/1.02  
% 3.62/1.02  ------ AIG Options
% 3.62/1.02  
% 3.62/1.02  --aig_mode                              false
% 3.62/1.02  
% 3.62/1.02  ------ Instantiation Options
% 3.62/1.02  
% 3.62/1.02  --instantiation_flag                    true
% 3.62/1.02  --inst_sos_flag                         true
% 3.62/1.02  --inst_sos_phase                        true
% 3.62/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/1.02  --inst_lit_sel_side                     none
% 3.62/1.02  --inst_solver_per_active                1400
% 3.62/1.02  --inst_solver_calls_frac                1.
% 3.62/1.02  --inst_passive_queue_type               priority_queues
% 3.62/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/1.02  --inst_passive_queues_freq              [25;2]
% 3.62/1.02  --inst_dismatching                      true
% 3.62/1.02  --inst_eager_unprocessed_to_passive     true
% 3.62/1.02  --inst_prop_sim_given                   true
% 3.62/1.02  --inst_prop_sim_new                     false
% 3.62/1.02  --inst_subs_new                         false
% 3.62/1.02  --inst_eq_res_simp                      false
% 3.62/1.02  --inst_subs_given                       false
% 3.62/1.02  --inst_orphan_elimination               true
% 3.62/1.02  --inst_learning_loop_flag               true
% 3.62/1.02  --inst_learning_start                   3000
% 3.62/1.02  --inst_learning_factor                  2
% 3.62/1.02  --inst_start_prop_sim_after_learn       3
% 3.62/1.02  --inst_sel_renew                        solver
% 3.62/1.02  --inst_lit_activity_flag                true
% 3.62/1.02  --inst_restr_to_given                   false
% 3.62/1.02  --inst_activity_threshold               500
% 3.62/1.02  --inst_out_proof                        true
% 3.62/1.02  
% 3.62/1.02  ------ Resolution Options
% 3.62/1.02  
% 3.62/1.02  --resolution_flag                       false
% 3.62/1.02  --res_lit_sel                           adaptive
% 3.62/1.02  --res_lit_sel_side                      none
% 3.62/1.02  --res_ordering                          kbo
% 3.62/1.02  --res_to_prop_solver                    active
% 3.62/1.02  --res_prop_simpl_new                    false
% 3.62/1.02  --res_prop_simpl_given                  true
% 3.62/1.02  --res_passive_queue_type                priority_queues
% 3.62/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/1.02  --res_passive_queues_freq               [15;5]
% 3.62/1.02  --res_forward_subs                      full
% 3.62/1.02  --res_backward_subs                     full
% 3.62/1.02  --res_forward_subs_resolution           true
% 3.62/1.02  --res_backward_subs_resolution          true
% 3.62/1.02  --res_orphan_elimination                true
% 3.62/1.02  --res_time_limit                        2.
% 3.62/1.02  --res_out_proof                         true
% 3.62/1.02  
% 3.62/1.02  ------ Superposition Options
% 3.62/1.02  
% 3.62/1.02  --superposition_flag                    true
% 3.62/1.02  --sup_passive_queue_type                priority_queues
% 3.62/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.62/1.02  --demod_completeness_check              fast
% 3.62/1.02  --demod_use_ground                      true
% 3.62/1.02  --sup_to_prop_solver                    passive
% 3.62/1.02  --sup_prop_simpl_new                    true
% 3.62/1.02  --sup_prop_simpl_given                  true
% 3.62/1.02  --sup_fun_splitting                     true
% 3.62/1.02  --sup_smt_interval                      50000
% 3.62/1.02  
% 3.62/1.02  ------ Superposition Simplification Setup
% 3.62/1.02  
% 3.62/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.62/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.62/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.62/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.62/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.62/1.02  --sup_immed_triv                        [TrivRules]
% 3.62/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.02  --sup_immed_bw_main                     []
% 3.62/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.62/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.02  --sup_input_bw                          []
% 3.62/1.02  
% 3.62/1.02  ------ Combination Options
% 3.62/1.02  
% 3.62/1.02  --comb_res_mult                         3
% 3.62/1.02  --comb_sup_mult                         2
% 3.62/1.02  --comb_inst_mult                        10
% 3.62/1.02  
% 3.62/1.02  ------ Debug Options
% 3.62/1.02  
% 3.62/1.02  --dbg_backtrace                         false
% 3.62/1.02  --dbg_dump_prop_clauses                 false
% 3.62/1.02  --dbg_dump_prop_clauses_file            -
% 3.62/1.02  --dbg_out_stat                          false
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  ------ Proving...
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  % SZS status Theorem for theBenchmark.p
% 3.62/1.02  
% 3.62/1.02   Resolution empty clause
% 3.62/1.02  
% 3.62/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/1.02  
% 3.62/1.02  fof(f14,axiom,(
% 3.62/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f40,plain,(
% 3.62/1.02    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f14])).
% 3.62/1.02  
% 3.62/1.02  fof(f41,plain,(
% 3.62/1.02    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.62/1.02    inference(flattening,[],[f40])).
% 3.62/1.02  
% 3.62/1.02  fof(f90,plain,(
% 3.62/1.02    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f41])).
% 3.62/1.02  
% 3.62/1.02  fof(f22,conjecture,(
% 3.62/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f23,negated_conjecture,(
% 3.62/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.62/1.02    inference(negated_conjecture,[],[f22])).
% 3.62/1.02  
% 3.62/1.02  fof(f51,plain,(
% 3.62/1.02    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.62/1.02    inference(ennf_transformation,[],[f23])).
% 3.62/1.02  
% 3.62/1.02  fof(f52,plain,(
% 3.62/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.62/1.02    inference(flattening,[],[f51])).
% 3.62/1.02  
% 3.62/1.02  fof(f64,plain,(
% 3.62/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.62/1.02    introduced(choice_axiom,[])).
% 3.62/1.02  
% 3.62/1.02  fof(f65,plain,(
% 3.62/1.02    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.62/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f52,f64])).
% 3.62/1.02  
% 3.62/1.02  fof(f114,plain,(
% 3.62/1.02    v2_funct_1(sK4)),
% 3.62/1.02    inference(cnf_transformation,[],[f65])).
% 3.62/1.02  
% 3.62/1.02  fof(f111,plain,(
% 3.62/1.02    v1_funct_1(sK4)),
% 3.62/1.02    inference(cnf_transformation,[],[f65])).
% 3.62/1.02  
% 3.62/1.02  fof(f113,plain,(
% 3.62/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.62/1.02    inference(cnf_transformation,[],[f65])).
% 3.62/1.02  
% 3.62/1.02  fof(f15,axiom,(
% 3.62/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f42,plain,(
% 3.62/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/1.02    inference(ennf_transformation,[],[f15])).
% 3.62/1.02  
% 3.62/1.02  fof(f91,plain,(
% 3.62/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/1.02    inference(cnf_transformation,[],[f42])).
% 3.62/1.02  
% 3.62/1.02  fof(f2,axiom,(
% 3.62/1.02    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f55,plain,(
% 3.62/1.02    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.62/1.02    inference(nnf_transformation,[],[f2])).
% 3.62/1.02  
% 3.62/1.02  fof(f56,plain,(
% 3.62/1.02    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.62/1.02    inference(flattening,[],[f55])).
% 3.62/1.02  
% 3.62/1.02  fof(f71,plain,(
% 3.62/1.02    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.62/1.02    inference(cnf_transformation,[],[f56])).
% 3.62/1.02  
% 3.62/1.02  fof(f119,plain,(
% 3.62/1.02    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.62/1.02    inference(equality_resolution,[],[f71])).
% 3.62/1.02  
% 3.62/1.02  fof(f20,axiom,(
% 3.62/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f47,plain,(
% 3.62/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f20])).
% 3.62/1.02  
% 3.62/1.02  fof(f48,plain,(
% 3.62/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.62/1.02    inference(flattening,[],[f47])).
% 3.62/1.02  
% 3.62/1.02  fof(f104,plain,(
% 3.62/1.02    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f48])).
% 3.62/1.02  
% 3.62/1.02  fof(f21,axiom,(
% 3.62/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f49,plain,(
% 3.62/1.02    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.62/1.02    inference(ennf_transformation,[],[f21])).
% 3.62/1.02  
% 3.62/1.02  fof(f50,plain,(
% 3.62/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.62/1.02    inference(flattening,[],[f49])).
% 3.62/1.02  
% 3.62/1.02  fof(f109,plain,(
% 3.62/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f50])).
% 3.62/1.02  
% 3.62/1.02  fof(f103,plain,(
% 3.62/1.02    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f48])).
% 3.62/1.02  
% 3.62/1.02  fof(f12,axiom,(
% 3.62/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f38,plain,(
% 3.62/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f12])).
% 3.62/1.02  
% 3.62/1.02  fof(f39,plain,(
% 3.62/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.62/1.02    inference(flattening,[],[f38])).
% 3.62/1.02  
% 3.62/1.02  fof(f85,plain,(
% 3.62/1.02    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f39])).
% 3.62/1.02  
% 3.62/1.02  fof(f84,plain,(
% 3.62/1.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f39])).
% 3.62/1.02  
% 3.62/1.02  fof(f70,plain,(
% 3.62/1.02    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.62/1.02    inference(cnf_transformation,[],[f56])).
% 3.62/1.02  
% 3.62/1.02  fof(f120,plain,(
% 3.62/1.02    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.62/1.02    inference(equality_resolution,[],[f70])).
% 3.62/1.02  
% 3.62/1.02  fof(f16,axiom,(
% 3.62/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f43,plain,(
% 3.62/1.02    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/1.02    inference(ennf_transformation,[],[f16])).
% 3.62/1.02  
% 3.62/1.02  fof(f93,plain,(
% 3.62/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/1.02    inference(cnf_transformation,[],[f43])).
% 3.62/1.02  
% 3.62/1.02  fof(f92,plain,(
% 3.62/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/1.02    inference(cnf_transformation,[],[f43])).
% 3.62/1.02  
% 3.62/1.02  fof(f6,axiom,(
% 3.62/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f31,plain,(
% 3.62/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.62/1.02    inference(ennf_transformation,[],[f6])).
% 3.62/1.02  
% 3.62/1.02  fof(f57,plain,(
% 3.62/1.02    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.62/1.02    inference(nnf_transformation,[],[f31])).
% 3.62/1.02  
% 3.62/1.02  fof(f74,plain,(
% 3.62/1.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f57])).
% 3.62/1.02  
% 3.62/1.02  fof(f17,axiom,(
% 3.62/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f44,plain,(
% 3.62/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/1.02    inference(ennf_transformation,[],[f17])).
% 3.62/1.02  
% 3.62/1.02  fof(f94,plain,(
% 3.62/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/1.02    inference(cnf_transformation,[],[f44])).
% 3.62/1.02  
% 3.62/1.02  fof(f115,plain,(
% 3.62/1.02    k2_relset_1(sK2,sK3,sK4) = sK3),
% 3.62/1.02    inference(cnf_transformation,[],[f65])).
% 3.62/1.02  
% 3.62/1.02  fof(f89,plain,(
% 3.62/1.02    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f41])).
% 3.62/1.02  
% 3.62/1.02  fof(f107,plain,(
% 3.62/1.02    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f50])).
% 3.62/1.02  
% 3.62/1.02  fof(f116,plain,(
% 3.62/1.02    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 3.62/1.02    inference(cnf_transformation,[],[f65])).
% 3.62/1.02  
% 3.62/1.02  fof(f9,axiom,(
% 3.62/1.02    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f33,plain,(
% 3.62/1.02    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.62/1.02    inference(ennf_transformation,[],[f9])).
% 3.62/1.02  
% 3.62/1.02  fof(f34,plain,(
% 3.62/1.02    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.62/1.02    inference(flattening,[],[f33])).
% 3.62/1.02  
% 3.62/1.02  fof(f80,plain,(
% 3.62/1.02    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f34])).
% 3.62/1.02  
% 3.62/1.02  fof(f10,axiom,(
% 3.62/1.02    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f35,plain,(
% 3.62/1.02    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.62/1.02    inference(ennf_transformation,[],[f10])).
% 3.62/1.02  
% 3.62/1.02  fof(f59,plain,(
% 3.62/1.02    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.62/1.02    inference(nnf_transformation,[],[f35])).
% 3.62/1.02  
% 3.62/1.02  fof(f82,plain,(
% 3.62/1.02    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f59])).
% 3.62/1.02  
% 3.62/1.02  fof(f81,plain,(
% 3.62/1.02    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f59])).
% 3.62/1.02  
% 3.62/1.02  fof(f108,plain,(
% 3.62/1.02    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f50])).
% 3.62/1.02  
% 3.62/1.02  fof(f122,plain,(
% 3.62/1.02    ( ! [X2,X3,X1] : (v1_funct_2(X3,k1_xboole_0,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 3.62/1.02    inference(equality_resolution,[],[f108])).
% 3.62/1.02  
% 3.62/1.02  fof(f3,axiom,(
% 3.62/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f72,plain,(
% 3.62/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.62/1.02    inference(cnf_transformation,[],[f3])).
% 3.62/1.02  
% 3.62/1.02  fof(f11,axiom,(
% 3.62/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f36,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f11])).
% 3.62/1.02  
% 3.62/1.02  fof(f37,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.62/1.02    inference(flattening,[],[f36])).
% 3.62/1.02  
% 3.62/1.02  fof(f83,plain,(
% 3.62/1.02    ( ! [X0,X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f7,axiom,(
% 3.62/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f32,plain,(
% 3.62/1.02    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.62/1.02    inference(ennf_transformation,[],[f7])).
% 3.62/1.02  
% 3.62/1.02  fof(f58,plain,(
% 3.62/1.02    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.62/1.02    inference(nnf_transformation,[],[f32])).
% 3.62/1.02  
% 3.62/1.02  fof(f76,plain,(
% 3.62/1.02    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f58])).
% 3.62/1.02  
% 3.62/1.02  cnf(c_23,plain,
% 3.62/1.02      ( ~ v2_funct_1(X0)
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_relat_1(X0)
% 3.62/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f90]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_47,negated_conjecture,
% 3.62/1.02      ( v2_funct_1(sK4) ),
% 3.62/1.02      inference(cnf_transformation,[],[f114]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_570,plain,
% 3.62/1.02      ( ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_relat_1(X0)
% 3.62/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.62/1.02      | sK4 != X0 ),
% 3.62/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_47]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_571,plain,
% 3.62/1.02      ( ~ v1_funct_1(sK4)
% 3.62/1.02      | ~ v1_relat_1(sK4)
% 3.62/1.02      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.62/1.02      inference(unflattening,[status(thm)],[c_570]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_50,negated_conjecture,
% 3.62/1.02      ( v1_funct_1(sK4) ),
% 3.62/1.02      inference(cnf_transformation,[],[f111]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_573,plain,
% 3.62/1.02      ( ~ v1_relat_1(sK4) | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.62/1.02      inference(global_propositional_subsumption,[status(thm)],[c_571,c_50]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1435,plain,
% 3.62/1.02      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 3.62/1.02      | v1_relat_1(sK4) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_48,negated_conjecture,
% 3.62/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.62/1.02      inference(cnf_transformation,[],[f113]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_25,plain,
% 3.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f91]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1534,plain,
% 3.62/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK4) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_25]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1605,plain,
% 3.62/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.62/1.02      | v1_relat_1(sK4) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_1534]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1736,plain,
% 3.62/1.02      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_1435,c_50,c_48,c_571,c_1605]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3,plain,
% 3.62/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.62/1.02      inference(cnf_transformation,[],[f119]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_36,plain,
% 3.62/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_relat_1(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f104]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1449,plain,
% 3.62/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.62/1.02      | v1_funct_1(X0) != iProver_top
% 3.62/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_40,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.62/1.02      | ~ r1_tarski(X2,X3)
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | k1_xboole_0 = X2 ),
% 3.62/1.02      inference(cnf_transformation,[],[f109]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1446,plain,
% 3.62/1.02      ( k1_xboole_0 = X0
% 3.62/1.02      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.62/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.62/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 3.62/1.02      | r1_tarski(X0,X3) != iProver_top
% 3.62/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4751,plain,
% 3.62/1.02      ( k2_relat_1(X0) = k1_xboole_0
% 3.62/1.02      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
% 3.62/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.62/1.02      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.62/1.02      | v1_funct_1(X0) != iProver_top
% 3.62/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1449,c_1446]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_37,plain,
% 3.62/1.02      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_relat_1(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f103]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_63,plain,
% 3.62/1.02      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 3.62/1.02      | v1_funct_1(X0) != iProver_top
% 3.62/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_12946,plain,
% 3.62/1.02      ( k2_relat_1(X0) = k1_xboole_0
% 3.62/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.62/1.02      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.62/1.02      | v1_funct_1(X0) != iProver_top
% 3.62/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,[status(thm)],[c_4751,c_63]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_12952,plain,
% 3.62/1.02      ( k2_relat_1(X0) = k1_xboole_0
% 3.62/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.62/1.02      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.62/1.02      | v1_funct_1(X0) != iProver_top
% 3.62/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_3,c_12946]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_12984,plain,
% 3.62/1.02      ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 3.62/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1736,c_12952]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_12987,plain,
% 3.62/1.02      ( k1_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_12984,c_1736]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_51,plain,
% 3.62/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_53,plain,
% 3.62/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_18,plain,
% 3.62/1.02      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1526,plain,
% 3.62/1.02      ( v1_funct_1(k2_funct_1(sK4)) | ~ v1_funct_1(sK4) | ~ v1_relat_1(sK4) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_18]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1527,plain,
% 3.62/1.02      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 3.62/1.02      | v1_funct_1(sK4) != iProver_top
% 3.62/1.02      | v1_relat_1(sK4) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1526]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1606,plain,
% 3.62/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.62/1.02      | v1_relat_1(sK4) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1605]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_19,plain,
% 3.62/1.02      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1861,plain,
% 3.62/1.02      ( ~ v1_funct_1(sK4) | v1_relat_1(k2_funct_1(sK4)) | ~ v1_relat_1(sK4) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_19]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1862,plain,
% 3.62/1.02      ( v1_funct_1(sK4) != iProver_top
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 3.62/1.02      | v1_relat_1(sK4) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1861]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_13472,plain,
% 3.62/1.02      ( k1_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_12987,c_51,c_53,c_1527,c_1606,c_1862]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4,plain,
% 3.62/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.62/1.02      inference(cnf_transformation,[],[f120]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_26,plain,
% 3.62/1.02      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.62/1.02      inference(cnf_transformation,[],[f93]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1454,plain,
% 3.62/1.02      ( v5_relat_1(X0,X1) = iProver_top
% 3.62/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2692,plain,
% 3.62/1.02      ( v5_relat_1(X0,X1) = iProver_top
% 3.62/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_4,c_1454]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_13478,plain,
% 3.62/1.02      ( k1_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | v5_relat_1(k2_funct_1(sK4),X0) = iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),k1_xboole_0) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_13472,c_2692]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1442,plain,
% 3.62/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_27,plain,
% 3.62/1.02      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.62/1.02      inference(cnf_transformation,[],[f92]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_9,plain,
% 3.62/1.02      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_502,plain,
% 3.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.02      | r1_tarski(k1_relat_1(X0),X1)
% 3.62/1.02      | ~ v1_relat_1(X0) ),
% 3.62/1.02      inference(resolution,[status(thm)],[c_27,c_9]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_506,plain,
% 3.62/1.02      ( r1_tarski(k1_relat_1(X0),X1)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.62/1.02      inference(global_propositional_subsumption,[status(thm)],[c_502,c_25]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_507,plain,
% 3.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.02      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_506]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1438,plain,
% 3.62/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2365,plain,
% 3.62/1.02      ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1442,c_1438]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4746,plain,
% 3.62/1.02      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1736,c_1449]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_28,plain,
% 3.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f94]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1453,plain,
% 3.62/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.62/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3509,plain,
% 3.62/1.02      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1442,c_1453]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_46,negated_conjecture,
% 3.62/1.02      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 3.62/1.02      inference(cnf_transformation,[],[f115]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3512,plain,
% 3.62/1.02      ( k2_relat_1(sK4) = sK3 ),
% 3.62/1.02      inference(light_normalisation,[status(thm)],[c_3509,c_46]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_24,plain,
% 3.62/1.02      ( ~ v2_funct_1(X0)
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_relat_1(X0)
% 3.62/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_556,plain,
% 3.62/1.02      ( ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_relat_1(X0)
% 3.62/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.62/1.02      | sK4 != X0 ),
% 3.62/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_47]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_557,plain,
% 3.62/1.02      ( ~ v1_funct_1(sK4)
% 3.62/1.02      | ~ v1_relat_1(sK4)
% 3.62/1.02      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.62/1.02      inference(unflattening,[status(thm)],[c_556]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_559,plain,
% 3.62/1.02      ( ~ v1_relat_1(sK4) | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.62/1.02      inference(global_propositional_subsumption,[status(thm)],[c_557,c_50]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1436,plain,
% 3.62/1.02      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 3.62/1.02      | v1_relat_1(sK4) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_559]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1787,plain,
% 3.62/1.02      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_1436,c_50,c_48,c_557,c_1605]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3609,plain,
% 3.62/1.02      ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_3512,c_1787]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4753,plain,
% 3.62/1.02      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(light_normalisation,[status(thm)],[c_4746,c_3609]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5659,plain,
% 3.62/1.02      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_4753,c_51,c_53,c_1527,c_1606,c_1862]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_42,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.62/1.02      | v1_funct_2(X0,X1,X3)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.02      | ~ r1_tarski(X2,X3)
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | k1_xboole_0 = X2 ),
% 3.62/1.02      inference(cnf_transformation,[],[f107]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1444,plain,
% 3.62/1.02      ( k1_xboole_0 = X0
% 3.62/1.02      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.62/1.02      | v1_funct_2(X1,X2,X3) = iProver_top
% 3.62/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.62/1.02      | r1_tarski(X0,X3) != iProver_top
% 3.62/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5670,plain,
% 3.62/1.02      ( k1_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
% 3.62/1.02      | v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) != iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5659,c_1444]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1448,plain,
% 3.62/1.02      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 3.62/1.02      | v1_funct_1(X0) != iProver_top
% 3.62/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4645,plain,
% 3.62/1.02      ( v1_funct_2(k2_funct_1(sK4),k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)) = iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1736,c_1448]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4646,plain,
% 3.62/1.02      ( v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) = iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(light_normalisation,[status(thm)],[c_4645,c_3609]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_12850,plain,
% 3.62/1.02      ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 3.62/1.02      | k1_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_5670,c_51,c_53,c_1527,c_1606,c_1862,c_4646]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_12851,plain,
% 3.62/1.02      ( k1_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_12850]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_12954,plain,
% 3.62/1.02      ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 3.62/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.62/1.02      | r1_tarski(k2_relat_1(k2_funct_1(sK4)),X0) != iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_3609,c_12946]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_12963,plain,
% 3.62/1.02      ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 3.62/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(light_normalisation,[status(thm)],[c_12954,c_1736]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_12964,plain,
% 3.62/1.02      ( k1_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_12963,c_1736]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5669,plain,
% 3.62/1.02      ( k1_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) != iProver_top
% 3.62/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5659,c_1446]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_13868,plain,
% 3.62/1.02      ( k1_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_12964,c_51,c_53,c_1527,c_1606,c_1862,c_4646,c_5669]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_45,negated_conjecture,
% 3.62/1.02      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 3.62/1.02      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.62/1.02      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f116]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1443,plain,
% 3.62/1.02      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_55,plain,
% 3.62/1.02      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.62/1.02      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1731,plain,
% 3.62/1.02      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.62/1.02      | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_1443,c_51,c_53,c_55,c_1527,c_1606]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1732,plain,
% 3.62/1.02      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_1731]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_13881,plain,
% 3.62/1.02      ( k1_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_13868,c_1732]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14078,plain,
% 3.62/1.02      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 3.62/1.02      | k1_relat_1(sK4) = k1_xboole_0 ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_13881,c_2365]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14079,plain,
% 3.62/1.02      ( k1_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_14078]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14082,plain,
% 3.62/1.02      ( k1_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_12851,c_14079]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14223,plain,
% 3.62/1.02      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_13478,c_2365,c_14082]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5360,plain,
% 3.62/1.02      ( v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) = iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_4646,c_51,c_53,c_1527,c_1606,c_1862]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14257,plain,
% 3.62/1.02      ( v1_funct_2(k2_funct_1(sK4),sK3,k1_xboole_0) = iProver_top ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_14223,c_5360]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_13,plain,
% 3.62/1.02      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.62/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1464,plain,
% 3.62/1.02      ( k2_relat_1(X0) != k1_xboole_0
% 3.62/1.02      | k1_xboole_0 = X0
% 3.62/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2963,plain,
% 3.62/1.02      ( k2_funct_1(sK4) = k1_xboole_0
% 3.62/1.02      | k1_relat_1(sK4) != k1_xboole_0
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1736,c_1464]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2965,plain,
% 3.62/1.02      ( ~ v1_relat_1(k2_funct_1(sK4))
% 3.62/1.02      | k2_funct_1(sK4) = k1_xboole_0
% 3.62/1.02      | k1_relat_1(sK4) != k1_xboole_0 ),
% 3.62/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2963]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3048,plain,
% 3.62/1.02      ( k1_relat_1(sK4) != k1_xboole_0 | k2_funct_1(sK4) = k1_xboole_0 ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_2963,c_50,c_48,c_1605,c_1861,c_2965]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3049,plain,
% 3.62/1.02      ( k2_funct_1(sK4) = k1_xboole_0 | k1_relat_1(sK4) != k1_xboole_0 ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_3048]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14265,plain,
% 3.62/1.02      ( k2_funct_1(sK4) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_14223,c_3049]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14268,plain,
% 3.62/1.02      ( k2_funct_1(sK4) = k1_xboole_0 ),
% 3.62/1.02      inference(equality_resolution_simp,[status(thm)],[c_14265]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_15,plain,
% 3.62/1.02      ( ~ v1_relat_1(X0)
% 3.62/1.02      | k2_relat_1(X0) != k1_xboole_0
% 3.62/1.02      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.62/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1462,plain,
% 3.62/1.02      ( k2_relat_1(X0) != k1_xboole_0
% 3.62/1.02      | k1_relat_1(X0) = k1_xboole_0
% 3.62/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3350,plain,
% 3.62/1.02      ( k1_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 3.62/1.02      | k1_relat_1(sK4) != k1_xboole_0
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1736,c_1462]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3351,plain,
% 3.62/1.02      ( k2_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | k1_relat_1(sK4) != k1_xboole_0
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_3350,c_1787]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_16,plain,
% 3.62/1.02      ( ~ v1_relat_1(X0)
% 3.62/1.02      | k2_relat_1(X0) = k1_xboole_0
% 3.62/1.02      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.62/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1984,plain,
% 3.62/1.02      ( ~ v1_relat_1(sK4)
% 3.62/1.02      | k2_relat_1(sK4) = k1_xboole_0
% 3.62/1.02      | k1_relat_1(sK4) != k1_xboole_0 ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_16]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3356,plain,
% 3.62/1.02      ( k1_relat_1(sK4) != k1_xboole_0 | k2_relat_1(sK4) = k1_xboole_0 ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_3351,c_48,c_1605,c_1984]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3357,plain,
% 3.62/1.02      ( k2_relat_1(sK4) = k1_xboole_0 | k1_relat_1(sK4) != k1_xboole_0 ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_3356]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3606,plain,
% 3.62/1.02      ( k1_relat_1(sK4) != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_3512,c_3357]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14264,plain,
% 3.62/1.02      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_14223,c_3606]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14270,plain,
% 3.62/1.02      ( sK3 = k1_xboole_0 ),
% 3.62/1.02      inference(equality_resolution_simp,[status(thm)],[c_14264]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14277,plain,
% 3.62/1.02      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_14257,c_14268,c_14270]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_41,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.62/1.02      | v1_funct_2(X0,k1_xboole_0,X2)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.62/1.02      | ~ r1_tarski(X1,X2)
% 3.62/1.02      | ~ v1_funct_1(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f122]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1445,plain,
% 3.62/1.02      ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 3.62/1.02      | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
% 3.62/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 3.62/1.02      | r1_tarski(X1,X2) != iProver_top
% 3.62/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1472,plain,
% 3.62/1.02      ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 3.62/1.02      | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
% 3.62/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.62/1.02      | r1_tarski(X1,X2) != iProver_top
% 3.62/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_1445,c_4]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_15771,plain,
% 3.62/1.02      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 3.62/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.62/1.02      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 3.62/1.02      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_14277,c_1472]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6,plain,
% 3.62/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_144,plain,
% 3.62/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_146,plain,
% 3.62/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_144]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_17,plain,
% 3.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.02      | ~ v1_funct_1(X1)
% 3.62/1.02      | v1_funct_1(X0)
% 3.62/1.02      | ~ v1_relat_1(X1) ),
% 3.62/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1776,plain,
% 3.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
% 3.62/1.02      | v1_funct_1(X0)
% 3.62/1.02      | ~ v1_funct_1(sK4)
% 3.62/1.02      | ~ v1_relat_1(sK4) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1777,plain,
% 3.62/1.02      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 3.62/1.02      | v1_funct_1(X0) = iProver_top
% 3.62/1.02      | v1_funct_1(sK4) != iProver_top
% 3.62/1.02      | v1_relat_1(sK4) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1776]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1779,plain,
% 3.62/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
% 3.62/1.02      | v1_funct_1(sK4) != iProver_top
% 3.62/1.02      | v1_funct_1(k1_xboole_0) = iProver_top
% 3.62/1.02      | v1_relat_1(sK4) != iProver_top ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_1777]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1864,plain,
% 3.62/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
% 3.62/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1865,plain,
% 3.62/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1864]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1469,plain,
% 3.62/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2688,plain,
% 3.62/1.02      ( v5_relat_1(k1_xboole_0,X0) = iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1469,c_1454]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_11,plain,
% 3.62/1.02      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1466,plain,
% 3.62/1.02      ( v5_relat_1(X0,X1) != iProver_top
% 3.62/1.02      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.62/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4277,plain,
% 3.62/1.02      ( v5_relat_1(k2_funct_1(sK4),X0) != iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.62/1.02      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1736,c_1466]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4455,plain,
% 3.62/1.02      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 3.62/1.02      | v5_relat_1(k2_funct_1(sK4),X0) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_4277,c_51,c_53,c_1606,c_1862]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4456,plain,
% 3.62/1.02      ( v5_relat_1(k2_funct_1(sK4),X0) != iProver_top
% 3.62/1.02      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_4455]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14262,plain,
% 3.62/1.02      ( v5_relat_1(k2_funct_1(sK4),X0) != iProver_top
% 3.62/1.02      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_14223,c_4456]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14271,plain,
% 3.62/1.02      ( v5_relat_1(k1_xboole_0,X0) != iProver_top
% 3.62/1.02      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_14262,c_14268]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_16271,plain,
% 3.62/1.02      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_15771,c_51,c_53,c_146,c_1606,c_1779,c_1865,c_2688,c_14271]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14545,plain,
% 3.62/1.02      ( v1_funct_2(k2_funct_1(sK4),k1_xboole_0,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_14270,c_1732]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14550,plain,
% 3.62/1.02      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.62/1.02      inference(light_normalisation,[status(thm)],[c_14545,c_14268]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14551,plain,
% 3.62/1.02      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.62/1.02      inference(demodulation,[status(thm)],[c_14550,c_4]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_14731,plain,
% 3.62/1.02      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,[status(thm)],[c_14551,c_146]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_16276,plain,
% 3.62/1.02      ( $false ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_16271,c_14731]) ).
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/1.02  
% 3.62/1.02  ------                               Statistics
% 3.62/1.02  
% 3.62/1.02  ------ General
% 3.62/1.02  
% 3.62/1.02  abstr_ref_over_cycles:                  0
% 3.62/1.02  abstr_ref_under_cycles:                 0
% 3.62/1.02  gc_basic_clause_elim:                   0
% 3.62/1.02  forced_gc_time:                         0
% 3.62/1.02  parsing_time:                           0.012
% 3.62/1.02  unif_index_cands_time:                  0.
% 3.62/1.02  unif_index_add_time:                    0.
% 3.62/1.02  orderings_time:                         0.
% 3.62/1.02  out_proof_time:                         0.014
% 3.62/1.02  total_time:                             0.465
% 3.62/1.02  num_of_symbols:                         52
% 3.62/1.02  num_of_terms:                           13861
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing
% 3.62/1.02  
% 3.62/1.02  num_of_splits:                          0
% 3.62/1.02  num_of_split_atoms:                     0
% 3.62/1.02  num_of_reused_defs:                     0
% 3.62/1.02  num_eq_ax_congr_red:                    11
% 3.62/1.02  num_of_sem_filtered_clauses:            1
% 3.62/1.02  num_of_subtypes:                        0
% 3.62/1.02  monotx_restored_types:                  0
% 3.62/1.02  sat_num_of_epr_types:                   0
% 3.62/1.02  sat_num_of_non_cyclic_types:            0
% 3.62/1.02  sat_guarded_non_collapsed_types:        0
% 3.62/1.02  num_pure_diseq_elim:                    0
% 3.62/1.02  simp_replaced_by:                       0
% 3.62/1.02  res_preprocessed:                       204
% 3.62/1.02  prep_upred:                             0
% 3.62/1.02  prep_unflattend:                        8
% 3.62/1.02  smt_new_axioms:                         0
% 3.62/1.02  pred_elim_cands:                        6
% 3.62/1.02  pred_elim:                              3
% 3.62/1.02  pred_elim_cl:                           3
% 3.62/1.02  pred_elim_cycles:                       5
% 3.62/1.02  merged_defs:                            0
% 3.62/1.02  merged_defs_ncl:                        0
% 3.62/1.02  bin_hyper_res:                          0
% 3.62/1.02  prep_cycles:                            4
% 3.62/1.02  pred_elim_time:                         0.004
% 3.62/1.02  splitting_time:                         0.
% 3.62/1.02  sem_filter_time:                        0.
% 3.62/1.02  monotx_time:                            0.
% 3.62/1.02  subtype_inf_time:                       0.
% 3.62/1.02  
% 3.62/1.02  ------ Problem properties
% 3.62/1.02  
% 3.62/1.02  clauses:                                43
% 3.62/1.02  conjectures:                            5
% 3.62/1.02  epr:                                    6
% 3.62/1.02  horn:                                   40
% 3.62/1.02  ground:                                 11
% 3.62/1.02  unary:                                  17
% 3.62/1.02  binary:                                 6
% 3.62/1.02  lits:                                   101
% 3.62/1.02  lits_eq:                                22
% 3.62/1.02  fd_pure:                                0
% 3.62/1.02  fd_pseudo:                              0
% 3.62/1.02  fd_cond:                                5
% 3.62/1.02  fd_pseudo_cond:                         1
% 3.62/1.02  ac_symbols:                             0
% 3.62/1.02  
% 3.62/1.02  ------ Propositional Solver
% 3.62/1.02  
% 3.62/1.02  prop_solver_calls:                      32
% 3.62/1.02  prop_fast_solver_calls:                 2035
% 3.62/1.02  smt_solver_calls:                       0
% 3.62/1.02  smt_fast_solver_calls:                  0
% 3.62/1.02  prop_num_of_clauses:                    6909
% 3.62/1.02  prop_preprocess_simplified:             15551
% 3.62/1.02  prop_fo_subsumed:                       174
% 3.62/1.02  prop_solver_time:                       0.
% 3.62/1.02  smt_solver_time:                        0.
% 3.62/1.02  smt_fast_solver_time:                   0.
% 3.62/1.02  prop_fast_solver_time:                  0.
% 3.62/1.02  prop_unsat_core_time:                   0.
% 3.62/1.02  
% 3.62/1.02  ------ QBF
% 3.62/1.02  
% 3.62/1.02  qbf_q_res:                              0
% 3.62/1.02  qbf_num_tautologies:                    0
% 3.62/1.02  qbf_prep_cycles:                        0
% 3.62/1.02  
% 3.62/1.02  ------ BMC1
% 3.62/1.02  
% 3.62/1.02  bmc1_current_bound:                     -1
% 3.62/1.02  bmc1_last_solved_bound:                 -1
% 3.62/1.02  bmc1_unsat_core_size:                   -1
% 3.62/1.02  bmc1_unsat_core_parents_size:           -1
% 3.62/1.02  bmc1_merge_next_fun:                    0
% 3.62/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.62/1.02  
% 3.62/1.02  ------ Instantiation
% 3.62/1.02  
% 3.62/1.02  inst_num_of_clauses:                    2269
% 3.62/1.02  inst_num_in_passive:                    361
% 3.62/1.02  inst_num_in_active:                     929
% 3.62/1.02  inst_num_in_unprocessed:                984
% 3.62/1.02  inst_num_of_loops:                      1200
% 3.62/1.02  inst_num_of_learning_restarts:          0
% 3.62/1.02  inst_num_moves_active_passive:          266
% 3.62/1.02  inst_lit_activity:                      0
% 3.62/1.02  inst_lit_activity_moves:                0
% 3.62/1.02  inst_num_tautologies:                   0
% 3.62/1.02  inst_num_prop_implied:                  0
% 3.62/1.02  inst_num_existing_simplified:           0
% 3.62/1.02  inst_num_eq_res_simplified:             0
% 3.62/1.02  inst_num_child_elim:                    0
% 3.62/1.02  inst_num_of_dismatching_blockings:      870
% 3.62/1.02  inst_num_of_non_proper_insts:           2115
% 3.62/1.02  inst_num_of_duplicates:                 0
% 3.62/1.02  inst_inst_num_from_inst_to_res:         0
% 3.62/1.02  inst_dismatching_checking_time:         0.
% 3.62/1.02  
% 3.62/1.02  ------ Resolution
% 3.62/1.02  
% 3.62/1.02  res_num_of_clauses:                     0
% 3.62/1.02  res_num_in_passive:                     0
% 3.62/1.02  res_num_in_active:                      0
% 3.62/1.02  res_num_of_loops:                       208
% 3.62/1.02  res_forward_subset_subsumed:            169
% 3.62/1.02  res_backward_subset_subsumed:           16
% 3.62/1.02  res_forward_subsumed:                   0
% 3.62/1.02  res_backward_subsumed:                  0
% 3.62/1.02  res_forward_subsumption_resolution:     0
% 3.62/1.02  res_backward_subsumption_resolution:    0
% 3.62/1.02  res_clause_to_clause_subsumption:       1038
% 3.62/1.02  res_orphan_elimination:                 0
% 3.62/1.02  res_tautology_del:                      224
% 3.62/1.02  res_num_eq_res_simplified:              0
% 3.62/1.02  res_num_sel_changes:                    0
% 3.62/1.02  res_moves_from_active_to_pass:          0
% 3.62/1.02  
% 3.62/1.02  ------ Superposition
% 3.62/1.02  
% 3.62/1.02  sup_time_total:                         0.
% 3.62/1.02  sup_time_generating:                    0.
% 3.62/1.02  sup_time_sim_full:                      0.
% 3.62/1.02  sup_time_sim_immed:                     0.
% 3.62/1.02  
% 3.62/1.02  sup_num_of_clauses:                     158
% 3.62/1.02  sup_num_in_active:                      94
% 3.62/1.02  sup_num_in_passive:                     64
% 3.62/1.02  sup_num_of_loops:                       239
% 3.62/1.02  sup_fw_superposition:                   257
% 3.62/1.02  sup_bw_superposition:                   263
% 3.62/1.02  sup_immediate_simplified:               295
% 3.62/1.02  sup_given_eliminated:                   0
% 3.62/1.02  comparisons_done:                       0
% 3.62/1.02  comparisons_avoided:                    5
% 3.62/1.02  
% 3.62/1.02  ------ Simplifications
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  sim_fw_subset_subsumed:                 104
% 3.62/1.02  sim_bw_subset_subsumed:                 82
% 3.62/1.02  sim_fw_subsumed:                        71
% 3.62/1.02  sim_bw_subsumed:                        10
% 3.62/1.02  sim_fw_subsumption_res:                 0
% 3.62/1.02  sim_bw_subsumption_res:                 0
% 3.62/1.02  sim_tautology_del:                      13
% 3.62/1.02  sim_eq_tautology_del:                   43
% 3.62/1.02  sim_eq_res_simp:                        4
% 3.62/1.02  sim_fw_demodulated:                     84
% 3.62/1.02  sim_bw_demodulated:                     96
% 3.62/1.02  sim_light_normalised:                   90
% 3.62/1.02  sim_joinable_taut:                      0
% 3.62/1.02  sim_joinable_simp:                      0
% 3.62/1.02  sim_ac_normalised:                      0
% 3.62/1.02  sim_smt_subsumption:                    0
% 3.62/1.02  
%------------------------------------------------------------------------------

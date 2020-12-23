%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:26 EST 2020

% Result     : Theorem 8.03s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_5065)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
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

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f54,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f55,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f68,plain,
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

fof(f69,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f55,f68])).

fof(f124,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f69])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f126,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f69])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f98,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f125,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f122,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f115,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f26,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f99,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f86,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f58])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f130,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f75])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f127,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f69])).

fof(f87,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f24,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & v1_xboole_0(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & v1_xboole_0(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v5_relat_1(sK1(X0,X1),X1)
        & v4_relat_1(sK1(X0,X1),X0)
        & v1_relat_1(sK1(X0,X1))
        & v1_xboole_0(sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v5_relat_1(sK1(X0,X1),X1)
      & v4_relat_1(sK1(X0,X1),X0)
      & v1_relat_1(sK1(X0,X1))
      & v1_xboole_0(sK1(X0,X1))
      & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f66])).

fof(f109,plain,(
    ! [X0,X1] : v1_xboole_0(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f123,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f47])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_55,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2126,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2138,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5385,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2126,c_2138])).

cnf(c_53,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_5388,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_5385,c_53])).

cnf(c_29,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_54,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_749,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_54])).

cnf(c_750,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_749])).

cnf(c_57,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_752,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_750,c_57])).

cnf(c_2116,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2230,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2301,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2230])).

cnf(c_2498,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2116,c_57,c_55,c_750,c_2301])).

cnf(c_5395,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_5388,c_2498])).

cnf(c_43,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2133,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_47,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2130,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_7573,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2133,c_2130])).

cnf(c_44,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_70,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_36899,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7573,c_70])).

cnf(c_36904,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK4)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5395,c_36899])).

cnf(c_28,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_763,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_54])).

cnf(c_764,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_763])).

cnf(c_766,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_764,c_57])).

cnf(c_2115,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_2452,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2115,c_57,c_55,c_764,c_2301])).

cnf(c_36915,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_36904,c_2452])).

cnf(c_36916,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36915,c_2452])).

cnf(c_58,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_60,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_14,plain,
    ( v5_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_147,plain,
    ( v5_relat_1(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_149,plain,
    ( v5_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2222,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2223,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2222])).

cnf(c_2302,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2301])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2581,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_23,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2597,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2598,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2597])).

cnf(c_1170,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2400,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_2773,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2400])).

cnf(c_2774,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2773])).

cnf(c_1169,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2843,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_2132,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_6968,plain,
    ( v1_funct_2(k2_funct_1(sK4),k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2452,c_2132])).

cnf(c_6969,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6968,c_5395])).

cnf(c_1175,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_7771,plain,
    ( ~ v5_relat_1(X0,k1_xboole_0)
    | v5_relat_1(sK4,k1_xboole_0)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(c_7772,plain,
    ( sK4 != X0
    | v5_relat_1(X0,k1_xboole_0) != iProver_top
    | v5_relat_1(sK4,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7771])).

cnf(c_7774,plain,
    ( sK4 != k1_xboole_0
    | v5_relat_1(sK4,k1_xboole_0) = iProver_top
    | v5_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7772])).

cnf(c_7566,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2452,c_2133])).

cnf(c_7575,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7566,c_5395])).

cnf(c_8831,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7575,c_58,c_60,c_2223,c_2302,c_2598])).

cnf(c_8843,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8831,c_2130])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2152,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2156,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_32,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_32,c_11])).

cnf(c_664,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_660,c_30])).

cnf(c_665,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_664])).

cnf(c_2121,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_4117,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2156,c_2121])).

cnf(c_9208,plain,
    ( v5_relat_1(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(k2_relat_1(X0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2152,c_4117])).

cnf(c_27524,plain,
    ( v5_relat_1(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(k2_relat_1(X0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_9208])).

cnf(c_27854,plain,
    ( v5_relat_1(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5388,c_27524])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X1)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_388,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_389,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_388])).

cnf(c_470,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_funct_1(X1)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_21,c_389])).

cnf(c_2505,plain,
    ( ~ r1_tarski(X0,sK4)
    | v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_2506,plain,
    ( r1_tarski(X0,sK4) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2505])).

cnf(c_2508,plain,
    ( r1_tarski(k1_xboole_0,sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2506])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2543,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2542])).

cnf(c_2545,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2543])).

cnf(c_3087,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3171,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3172,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3171])).

cnf(c_1171,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2956,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(X3,k2_zfmisc_1(X1,X2))
    | X3 != X0 ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_4072,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK3,sK2))
    | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2))
    | k2_funct_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_2956])).

cnf(c_4073,plain,
    ( k2_funct_1(sK4) != X0
    | r1_tarski(X0,k2_zfmisc_1(sK3,sK2)) != iProver_top
    | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4072])).

cnf(c_4075,plain,
    ( k2_funct_1(sK4) != k1_xboole_0
    | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4073])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4104,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4105,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4104])).

cnf(c_4107,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4105])).

cnf(c_52,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2127,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_62,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_2447,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2127,c_58,c_60,c_62,c_2223,c_2302])).

cnf(c_2448,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2447])).

cnf(c_4118,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2156,c_2448])).

cnf(c_1184,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_2364,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | k2_funct_1(sK4) != X0
    | sK2 != X2
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1184])).

cnf(c_2572,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | k2_funct_1(sK4) != X0
    | sK2 != sK2
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_2364])).

cnf(c_4143,plain,
    ( ~ v1_funct_2(X0,sK3,sK2)
    | v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | k2_funct_1(sK4) != X0
    | sK2 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2572])).

cnf(c_4144,plain,
    ( k2_funct_1(sK4) != X0
    | sK2 != sK2
    | sK3 != sK3
    | v1_funct_2(X0,sK3,sK2) != iProver_top
    | v1_funct_2(k2_funct_1(sK4),sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4143])).

cnf(c_4146,plain,
    ( k2_funct_1(sK4) != k1_xboole_0
    | sK2 != sK2
    | sK3 != sK3
    | v1_funct_2(k2_funct_1(sK4),sK3,sK2) = iProver_top
    | v1_funct_2(k1_xboole_0,sK3,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4144])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2150,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4654,plain,
    ( k2_funct_1(sK4) = k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2452,c_2150])).

cnf(c_4656,plain,
    ( ~ v1_relat_1(k2_funct_1(sK4))
    | k2_funct_1(sK4) = k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4654])).

cnf(c_4778,plain,
    ( k1_relat_1(sK4) != k1_xboole_0
    | k2_funct_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4654,c_57,c_55,c_2301,c_2597,c_4656])).

cnf(c_4779,plain,
    ( k2_funct_1(sK4) = k1_xboole_0
    | k1_relat_1(sK4) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4778])).

cnf(c_2936,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6603,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | r1_tarski(X0,k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_2936])).

cnf(c_6604,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(sK3,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6603])).

cnf(c_6606,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6604])).

cnf(c_6633,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_6654,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6655,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6654])).

cnf(c_6657,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6655])).

cnf(c_6833,plain,
    ( v5_relat_1(sK4,X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5388,c_2152])).

cnf(c_6839,plain,
    ( v5_relat_1(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6833])).

cnf(c_41,plain,
    ( v1_xboole_0(sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2135,plain,
    ( v1_xboole_0(sK1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_2157,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2139,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7781,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2157,c_2139])).

cnf(c_10433,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2135,c_7781])).

cnf(c_6701,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2126,c_2130])).

cnf(c_56,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_59,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_7162,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6701,c_58,c_59])).

cnf(c_7163,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7162])).

cnf(c_7168,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_7163])).

cnf(c_159,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_161,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_165,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_167,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_4062,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X1)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_4063,plain,
    ( sK4 != X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK4,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4062])).

cnf(c_4065,plain,
    ( sK4 != k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4063])).

cnf(c_5230,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5231,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5230])).

cnf(c_5233,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5231])).

cnf(c_5397,plain,
    ( sK3 != k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5388,c_2150])).

cnf(c_7596,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7168,c_60,c_161,c_167,c_2302,c_4065,c_5233,c_5397])).

cnf(c_3902,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_2121])).

cnf(c_7602,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7596,c_3902])).

cnf(c_2155,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3707,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2157,c_2155])).

cnf(c_2159,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6803,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3707,c_2159])).

cnf(c_11671,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7602,c_6803])).

cnf(c_37,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_35,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_634,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(resolution,[status(thm)],[c_37,c_35])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_634,c_37,c_35])).

cnf(c_639,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_638])).

cnf(c_12917,plain,
    ( v1_funct_2(X0,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_xboole_0(sK3)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_12918,plain,
    ( v1_funct_2(X0,sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_xboole_0(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12917])).

cnf(c_12920,plain,
    ( v1_funct_2(k1_xboole_0,sK3,sK2) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_xboole_0(sK3) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12918])).

cnf(c_2684,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_13093,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_2684])).

cnf(c_13096,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13093])).

cnf(c_23280,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_23281,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23280])).

cnf(c_1182,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_27376,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1182])).

cnf(c_27377,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27376])).

cnf(c_27379,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_27377])).

cnf(c_27924,plain,
    ( v5_relat_1(sK4,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27854,c_58,c_60,c_2302,c_2508,c_2545,c_3087,c_3172,c_4075,c_4107,c_4118,c_4146,c_4779,c_6606,c_6633,c_6657,c_6839,c_10433,c_11671,c_12920,c_13096,c_23281,c_27379])).

cnf(c_37644,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36916,c_58,c_60,c_161,c_167,c_2223,c_2302,c_2508,c_2545,c_2598,c_3087,c_3172,c_4075,c_4107,c_4118,c_4146,c_4654,c_4779,c_5065,c_6606,c_6633,c_6657,c_6969,c_8843,c_9386,c_10433,c_11671,c_12920,c_13096,c_23281,c_27379])).

cnf(c_2122,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_37653,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_xboole_0(sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37644,c_2122])).

cnf(c_49,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2128,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_8844,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
    | v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8831,c_2128])).

cnf(c_38464,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37653,c_58,c_60,c_161,c_167,c_2223,c_2302,c_2508,c_2545,c_2598,c_3087,c_3172,c_4075,c_4107,c_4118,c_4146,c_4654,c_4779,c_5065,c_6606,c_6633,c_6657,c_6969,c_8844,c_9386,c_10433,c_11671,c_12920,c_13096,c_23281,c_27379])).

cnf(c_37657,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_37644,c_2448])).

cnf(c_3901,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2126,c_2121])).

cnf(c_37758,plain,
    ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37657,c_3901])).

cnf(c_38468,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_38464,c_37758])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38468,c_3901])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 13:12:37 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 8.03/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.03/1.48  
% 8.03/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.03/1.48  
% 8.03/1.48  ------  iProver source info
% 8.03/1.48  
% 8.03/1.48  git: date: 2020-06-30 10:37:57 +0100
% 8.03/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.03/1.48  git: non_committed_changes: false
% 8.03/1.48  git: last_make_outside_of_git: false
% 8.03/1.48  
% 8.03/1.48  ------ 
% 8.03/1.48  
% 8.03/1.48  ------ Input Options
% 8.03/1.48  
% 8.03/1.48  --out_options                           all
% 8.03/1.48  --tptp_safe_out                         true
% 8.03/1.48  --problem_path                          ""
% 8.03/1.48  --include_path                          ""
% 8.03/1.48  --clausifier                            res/vclausify_rel
% 8.03/1.48  --clausifier_options                    ""
% 8.03/1.48  --stdin                                 false
% 8.03/1.48  --stats_out                             all
% 8.03/1.48  
% 8.03/1.48  ------ General Options
% 8.03/1.48  
% 8.03/1.48  --fof                                   false
% 8.03/1.48  --time_out_real                         305.
% 8.03/1.48  --time_out_virtual                      -1.
% 8.03/1.48  --symbol_type_check                     false
% 8.03/1.48  --clausify_out                          false
% 8.03/1.48  --sig_cnt_out                           false
% 8.03/1.48  --trig_cnt_out                          false
% 8.03/1.48  --trig_cnt_out_tolerance                1.
% 8.03/1.48  --trig_cnt_out_sk_spl                   false
% 8.03/1.48  --abstr_cl_out                          false
% 8.03/1.48  
% 8.03/1.48  ------ Global Options
% 8.03/1.48  
% 8.03/1.48  --schedule                              default
% 8.03/1.48  --add_important_lit                     false
% 8.03/1.48  --prop_solver_per_cl                    1000
% 8.03/1.48  --min_unsat_core                        false
% 8.03/1.48  --soft_assumptions                      false
% 8.03/1.48  --soft_lemma_size                       3
% 8.03/1.48  --prop_impl_unit_size                   0
% 8.03/1.48  --prop_impl_unit                        []
% 8.03/1.48  --share_sel_clauses                     true
% 8.03/1.48  --reset_solvers                         false
% 8.03/1.48  --bc_imp_inh                            [conj_cone]
% 8.03/1.48  --conj_cone_tolerance                   3.
% 8.03/1.48  --extra_neg_conj                        none
% 8.03/1.48  --large_theory_mode                     true
% 8.03/1.48  --prolific_symb_bound                   200
% 8.03/1.48  --lt_threshold                          2000
% 8.03/1.48  --clause_weak_htbl                      true
% 8.03/1.48  --gc_record_bc_elim                     false
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing Options
% 8.03/1.48  
% 8.03/1.48  --preprocessing_flag                    true
% 8.03/1.48  --time_out_prep_mult                    0.1
% 8.03/1.48  --splitting_mode                        input
% 8.03/1.48  --splitting_grd                         true
% 8.03/1.48  --splitting_cvd                         false
% 8.03/1.48  --splitting_cvd_svl                     false
% 8.03/1.48  --splitting_nvd                         32
% 8.03/1.48  --sub_typing                            true
% 8.03/1.48  --prep_gs_sim                           true
% 8.03/1.48  --prep_unflatten                        true
% 8.03/1.48  --prep_res_sim                          true
% 8.03/1.48  --prep_upred                            true
% 8.03/1.48  --prep_sem_filter                       exhaustive
% 8.03/1.48  --prep_sem_filter_out                   false
% 8.03/1.48  --pred_elim                             true
% 8.03/1.48  --res_sim_input                         true
% 8.03/1.48  --eq_ax_congr_red                       true
% 8.03/1.48  --pure_diseq_elim                       true
% 8.03/1.48  --brand_transform                       false
% 8.03/1.48  --non_eq_to_eq                          false
% 8.03/1.48  --prep_def_merge                        true
% 8.03/1.48  --prep_def_merge_prop_impl              false
% 8.03/1.48  --prep_def_merge_mbd                    true
% 8.03/1.48  --prep_def_merge_tr_red                 false
% 8.03/1.48  --prep_def_merge_tr_cl                  false
% 8.03/1.48  --smt_preprocessing                     true
% 8.03/1.48  --smt_ac_axioms                         fast
% 8.03/1.48  --preprocessed_out                      false
% 8.03/1.48  --preprocessed_stats                    false
% 8.03/1.48  
% 8.03/1.48  ------ Abstraction refinement Options
% 8.03/1.48  
% 8.03/1.48  --abstr_ref                             []
% 8.03/1.48  --abstr_ref_prep                        false
% 8.03/1.48  --abstr_ref_until_sat                   false
% 8.03/1.48  --abstr_ref_sig_restrict                funpre
% 8.03/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.03/1.48  --abstr_ref_under                       []
% 8.03/1.48  
% 8.03/1.48  ------ SAT Options
% 8.03/1.48  
% 8.03/1.48  --sat_mode                              false
% 8.03/1.48  --sat_fm_restart_options                ""
% 8.03/1.48  --sat_gr_def                            false
% 8.03/1.48  --sat_epr_types                         true
% 8.03/1.48  --sat_non_cyclic_types                  false
% 8.03/1.48  --sat_finite_models                     false
% 8.03/1.48  --sat_fm_lemmas                         false
% 8.03/1.48  --sat_fm_prep                           false
% 8.03/1.48  --sat_fm_uc_incr                        true
% 8.03/1.48  --sat_out_model                         small
% 8.03/1.48  --sat_out_clauses                       false
% 8.03/1.48  
% 8.03/1.48  ------ QBF Options
% 8.03/1.48  
% 8.03/1.48  --qbf_mode                              false
% 8.03/1.48  --qbf_elim_univ                         false
% 8.03/1.48  --qbf_dom_inst                          none
% 8.03/1.48  --qbf_dom_pre_inst                      false
% 8.03/1.48  --qbf_sk_in                             false
% 8.03/1.48  --qbf_pred_elim                         true
% 8.03/1.48  --qbf_split                             512
% 8.03/1.48  
% 8.03/1.48  ------ BMC1 Options
% 8.03/1.48  
% 8.03/1.48  --bmc1_incremental                      false
% 8.03/1.48  --bmc1_axioms                           reachable_all
% 8.03/1.48  --bmc1_min_bound                        0
% 8.03/1.48  --bmc1_max_bound                        -1
% 8.03/1.48  --bmc1_max_bound_default                -1
% 8.03/1.48  --bmc1_symbol_reachability              true
% 8.03/1.48  --bmc1_property_lemmas                  false
% 8.03/1.48  --bmc1_k_induction                      false
% 8.03/1.48  --bmc1_non_equiv_states                 false
% 8.03/1.48  --bmc1_deadlock                         false
% 8.03/1.48  --bmc1_ucm                              false
% 8.03/1.48  --bmc1_add_unsat_core                   none
% 8.03/1.48  --bmc1_unsat_core_children              false
% 8.03/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.03/1.48  --bmc1_out_stat                         full
% 8.03/1.48  --bmc1_ground_init                      false
% 8.03/1.48  --bmc1_pre_inst_next_state              false
% 8.03/1.48  --bmc1_pre_inst_state                   false
% 8.03/1.48  --bmc1_pre_inst_reach_state             false
% 8.03/1.48  --bmc1_out_unsat_core                   false
% 8.03/1.48  --bmc1_aig_witness_out                  false
% 8.03/1.48  --bmc1_verbose                          false
% 8.03/1.48  --bmc1_dump_clauses_tptp                false
% 8.03/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.03/1.48  --bmc1_dump_file                        -
% 8.03/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.03/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.03/1.48  --bmc1_ucm_extend_mode                  1
% 8.03/1.48  --bmc1_ucm_init_mode                    2
% 8.03/1.48  --bmc1_ucm_cone_mode                    none
% 8.03/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.03/1.48  --bmc1_ucm_relax_model                  4
% 8.03/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.03/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.03/1.48  --bmc1_ucm_layered_model                none
% 8.03/1.48  --bmc1_ucm_max_lemma_size               10
% 8.03/1.48  
% 8.03/1.48  ------ AIG Options
% 8.03/1.48  
% 8.03/1.48  --aig_mode                              false
% 8.03/1.48  
% 8.03/1.48  ------ Instantiation Options
% 8.03/1.48  
% 8.03/1.48  --instantiation_flag                    true
% 8.03/1.48  --inst_sos_flag                         true
% 8.03/1.48  --inst_sos_phase                        true
% 8.03/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.03/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.03/1.48  --inst_lit_sel_side                     num_symb
% 8.03/1.48  --inst_solver_per_active                1400
% 8.03/1.48  --inst_solver_calls_frac                1.
% 8.03/1.48  --inst_passive_queue_type               priority_queues
% 8.03/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.03/1.48  --inst_passive_queues_freq              [25;2]
% 8.03/1.48  --inst_dismatching                      true
% 8.03/1.48  --inst_eager_unprocessed_to_passive     true
% 8.03/1.48  --inst_prop_sim_given                   true
% 8.03/1.48  --inst_prop_sim_new                     false
% 8.03/1.48  --inst_subs_new                         false
% 8.03/1.48  --inst_eq_res_simp                      false
% 8.03/1.48  --inst_subs_given                       false
% 8.03/1.48  --inst_orphan_elimination               true
% 8.03/1.48  --inst_learning_loop_flag               true
% 8.03/1.48  --inst_learning_start                   3000
% 8.03/1.48  --inst_learning_factor                  2
% 8.03/1.48  --inst_start_prop_sim_after_learn       3
% 8.03/1.48  --inst_sel_renew                        solver
% 8.03/1.48  --inst_lit_activity_flag                true
% 8.03/1.48  --inst_restr_to_given                   false
% 8.03/1.48  --inst_activity_threshold               500
% 8.03/1.48  --inst_out_proof                        true
% 8.03/1.48  
% 8.03/1.48  ------ Resolution Options
% 8.03/1.48  
% 8.03/1.48  --resolution_flag                       true
% 8.03/1.48  --res_lit_sel                           adaptive
% 8.03/1.48  --res_lit_sel_side                      none
% 8.03/1.48  --res_ordering                          kbo
% 8.03/1.48  --res_to_prop_solver                    active
% 8.03/1.48  --res_prop_simpl_new                    false
% 8.03/1.48  --res_prop_simpl_given                  true
% 8.03/1.48  --res_passive_queue_type                priority_queues
% 8.03/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.03/1.48  --res_passive_queues_freq               [15;5]
% 8.03/1.48  --res_forward_subs                      full
% 8.03/1.48  --res_backward_subs                     full
% 8.03/1.48  --res_forward_subs_resolution           true
% 8.03/1.48  --res_backward_subs_resolution          true
% 8.03/1.48  --res_orphan_elimination                true
% 8.03/1.48  --res_time_limit                        2.
% 8.03/1.48  --res_out_proof                         true
% 8.03/1.48  
% 8.03/1.48  ------ Superposition Options
% 8.03/1.48  
% 8.03/1.48  --superposition_flag                    true
% 8.03/1.48  --sup_passive_queue_type                priority_queues
% 8.03/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.03/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.03/1.48  --demod_completeness_check              fast
% 8.03/1.48  --demod_use_ground                      true
% 8.03/1.48  --sup_to_prop_solver                    passive
% 8.03/1.48  --sup_prop_simpl_new                    true
% 8.03/1.48  --sup_prop_simpl_given                  true
% 8.03/1.48  --sup_fun_splitting                     true
% 8.03/1.48  --sup_smt_interval                      50000
% 8.03/1.48  
% 8.03/1.48  ------ Superposition Simplification Setup
% 8.03/1.48  
% 8.03/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.03/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.03/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.03/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.03/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.03/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.03/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.03/1.48  --sup_immed_triv                        [TrivRules]
% 8.03/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_immed_bw_main                     []
% 8.03/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.03/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.03/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_input_bw                          []
% 8.03/1.48  
% 8.03/1.48  ------ Combination Options
% 8.03/1.48  
% 8.03/1.48  --comb_res_mult                         3
% 8.03/1.48  --comb_sup_mult                         2
% 8.03/1.48  --comb_inst_mult                        10
% 8.03/1.48  
% 8.03/1.48  ------ Debug Options
% 8.03/1.48  
% 8.03/1.48  --dbg_backtrace                         false
% 8.03/1.48  --dbg_dump_prop_clauses                 false
% 8.03/1.48  --dbg_dump_prop_clauses_file            -
% 8.03/1.48  --dbg_out_stat                          false
% 8.03/1.48  ------ Parsing...
% 8.03/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.48  ------ Proving...
% 8.03/1.48  ------ Problem Properties 
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  clauses                                 50
% 8.03/1.48  conjectures                             5
% 8.03/1.48  EPR                                     8
% 8.03/1.48  Horn                                    47
% 8.03/1.48  unary                                   18
% 8.03/1.48  binary                                  11
% 8.03/1.48  lits                                    116
% 8.03/1.48  lits eq                                 23
% 8.03/1.48  fd_pure                                 0
% 8.03/1.48  fd_pseudo                               0
% 8.03/1.48  fd_cond                                 5
% 8.03/1.48  fd_pseudo_cond                          1
% 8.03/1.48  AC symbols                              0
% 8.03/1.48  
% 8.03/1.48  ------ Schedule dynamic 5 is on 
% 8.03/1.48  
% 8.03/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  ------ 
% 8.03/1.48  Current options:
% 8.03/1.48  ------ 
% 8.03/1.48  
% 8.03/1.48  ------ Input Options
% 8.03/1.48  
% 8.03/1.48  --out_options                           all
% 8.03/1.48  --tptp_safe_out                         true
% 8.03/1.48  --problem_path                          ""
% 8.03/1.48  --include_path                          ""
% 8.03/1.48  --clausifier                            res/vclausify_rel
% 8.03/1.48  --clausifier_options                    ""
% 8.03/1.48  --stdin                                 false
% 8.03/1.48  --stats_out                             all
% 8.03/1.48  
% 8.03/1.48  ------ General Options
% 8.03/1.48  
% 8.03/1.48  --fof                                   false
% 8.03/1.48  --time_out_real                         305.
% 8.03/1.48  --time_out_virtual                      -1.
% 8.03/1.48  --symbol_type_check                     false
% 8.03/1.48  --clausify_out                          false
% 8.03/1.48  --sig_cnt_out                           false
% 8.03/1.48  --trig_cnt_out                          false
% 8.03/1.48  --trig_cnt_out_tolerance                1.
% 8.03/1.48  --trig_cnt_out_sk_spl                   false
% 8.03/1.48  --abstr_cl_out                          false
% 8.03/1.48  
% 8.03/1.48  ------ Global Options
% 8.03/1.48  
% 8.03/1.48  --schedule                              default
% 8.03/1.48  --add_important_lit                     false
% 8.03/1.48  --prop_solver_per_cl                    1000
% 8.03/1.48  --min_unsat_core                        false
% 8.03/1.48  --soft_assumptions                      false
% 8.03/1.48  --soft_lemma_size                       3
% 8.03/1.48  --prop_impl_unit_size                   0
% 8.03/1.48  --prop_impl_unit                        []
% 8.03/1.48  --share_sel_clauses                     true
% 8.03/1.48  --reset_solvers                         false
% 8.03/1.48  --bc_imp_inh                            [conj_cone]
% 8.03/1.48  --conj_cone_tolerance                   3.
% 8.03/1.48  --extra_neg_conj                        none
% 8.03/1.48  --large_theory_mode                     true
% 8.03/1.48  --prolific_symb_bound                   200
% 8.03/1.48  --lt_threshold                          2000
% 8.03/1.48  --clause_weak_htbl                      true
% 8.03/1.48  --gc_record_bc_elim                     false
% 8.03/1.48  
% 8.03/1.48  ------ Preprocessing Options
% 8.03/1.48  
% 8.03/1.48  --preprocessing_flag                    true
% 8.03/1.48  --time_out_prep_mult                    0.1
% 8.03/1.48  --splitting_mode                        input
% 8.03/1.48  --splitting_grd                         true
% 8.03/1.48  --splitting_cvd                         false
% 8.03/1.48  --splitting_cvd_svl                     false
% 8.03/1.48  --splitting_nvd                         32
% 8.03/1.48  --sub_typing                            true
% 8.03/1.48  --prep_gs_sim                           true
% 8.03/1.48  --prep_unflatten                        true
% 8.03/1.48  --prep_res_sim                          true
% 8.03/1.48  --prep_upred                            true
% 8.03/1.48  --prep_sem_filter                       exhaustive
% 8.03/1.48  --prep_sem_filter_out                   false
% 8.03/1.48  --pred_elim                             true
% 8.03/1.48  --res_sim_input                         true
% 8.03/1.48  --eq_ax_congr_red                       true
% 8.03/1.48  --pure_diseq_elim                       true
% 8.03/1.48  --brand_transform                       false
% 8.03/1.48  --non_eq_to_eq                          false
% 8.03/1.48  --prep_def_merge                        true
% 8.03/1.48  --prep_def_merge_prop_impl              false
% 8.03/1.48  --prep_def_merge_mbd                    true
% 8.03/1.48  --prep_def_merge_tr_red                 false
% 8.03/1.48  --prep_def_merge_tr_cl                  false
% 8.03/1.48  --smt_preprocessing                     true
% 8.03/1.48  --smt_ac_axioms                         fast
% 8.03/1.48  --preprocessed_out                      false
% 8.03/1.48  --preprocessed_stats                    false
% 8.03/1.48  
% 8.03/1.48  ------ Abstraction refinement Options
% 8.03/1.48  
% 8.03/1.48  --abstr_ref                             []
% 8.03/1.48  --abstr_ref_prep                        false
% 8.03/1.48  --abstr_ref_until_sat                   false
% 8.03/1.48  --abstr_ref_sig_restrict                funpre
% 8.03/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.03/1.48  --abstr_ref_under                       []
% 8.03/1.48  
% 8.03/1.48  ------ SAT Options
% 8.03/1.48  
% 8.03/1.48  --sat_mode                              false
% 8.03/1.48  --sat_fm_restart_options                ""
% 8.03/1.48  --sat_gr_def                            false
% 8.03/1.48  --sat_epr_types                         true
% 8.03/1.48  --sat_non_cyclic_types                  false
% 8.03/1.48  --sat_finite_models                     false
% 8.03/1.48  --sat_fm_lemmas                         false
% 8.03/1.48  --sat_fm_prep                           false
% 8.03/1.48  --sat_fm_uc_incr                        true
% 8.03/1.48  --sat_out_model                         small
% 8.03/1.48  --sat_out_clauses                       false
% 8.03/1.48  
% 8.03/1.48  ------ QBF Options
% 8.03/1.48  
% 8.03/1.48  --qbf_mode                              false
% 8.03/1.48  --qbf_elim_univ                         false
% 8.03/1.48  --qbf_dom_inst                          none
% 8.03/1.48  --qbf_dom_pre_inst                      false
% 8.03/1.48  --qbf_sk_in                             false
% 8.03/1.48  --qbf_pred_elim                         true
% 8.03/1.48  --qbf_split                             512
% 8.03/1.48  
% 8.03/1.48  ------ BMC1 Options
% 8.03/1.48  
% 8.03/1.48  --bmc1_incremental                      false
% 8.03/1.48  --bmc1_axioms                           reachable_all
% 8.03/1.48  --bmc1_min_bound                        0
% 8.03/1.48  --bmc1_max_bound                        -1
% 8.03/1.48  --bmc1_max_bound_default                -1
% 8.03/1.48  --bmc1_symbol_reachability              true
% 8.03/1.48  --bmc1_property_lemmas                  false
% 8.03/1.48  --bmc1_k_induction                      false
% 8.03/1.48  --bmc1_non_equiv_states                 false
% 8.03/1.48  --bmc1_deadlock                         false
% 8.03/1.48  --bmc1_ucm                              false
% 8.03/1.48  --bmc1_add_unsat_core                   none
% 8.03/1.48  --bmc1_unsat_core_children              false
% 8.03/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.03/1.48  --bmc1_out_stat                         full
% 8.03/1.48  --bmc1_ground_init                      false
% 8.03/1.48  --bmc1_pre_inst_next_state              false
% 8.03/1.48  --bmc1_pre_inst_state                   false
% 8.03/1.48  --bmc1_pre_inst_reach_state             false
% 8.03/1.48  --bmc1_out_unsat_core                   false
% 8.03/1.48  --bmc1_aig_witness_out                  false
% 8.03/1.48  --bmc1_verbose                          false
% 8.03/1.48  --bmc1_dump_clauses_tptp                false
% 8.03/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.03/1.48  --bmc1_dump_file                        -
% 8.03/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.03/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.03/1.48  --bmc1_ucm_extend_mode                  1
% 8.03/1.48  --bmc1_ucm_init_mode                    2
% 8.03/1.48  --bmc1_ucm_cone_mode                    none
% 8.03/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.03/1.48  --bmc1_ucm_relax_model                  4
% 8.03/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.03/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.03/1.48  --bmc1_ucm_layered_model                none
% 8.03/1.48  --bmc1_ucm_max_lemma_size               10
% 8.03/1.48  
% 8.03/1.48  ------ AIG Options
% 8.03/1.48  
% 8.03/1.48  --aig_mode                              false
% 8.03/1.48  
% 8.03/1.48  ------ Instantiation Options
% 8.03/1.48  
% 8.03/1.48  --instantiation_flag                    true
% 8.03/1.48  --inst_sos_flag                         true
% 8.03/1.48  --inst_sos_phase                        true
% 8.03/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.03/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.03/1.48  --inst_lit_sel_side                     none
% 8.03/1.48  --inst_solver_per_active                1400
% 8.03/1.48  --inst_solver_calls_frac                1.
% 8.03/1.48  --inst_passive_queue_type               priority_queues
% 8.03/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.03/1.48  --inst_passive_queues_freq              [25;2]
% 8.03/1.48  --inst_dismatching                      true
% 8.03/1.48  --inst_eager_unprocessed_to_passive     true
% 8.03/1.48  --inst_prop_sim_given                   true
% 8.03/1.48  --inst_prop_sim_new                     false
% 8.03/1.48  --inst_subs_new                         false
% 8.03/1.48  --inst_eq_res_simp                      false
% 8.03/1.48  --inst_subs_given                       false
% 8.03/1.48  --inst_orphan_elimination               true
% 8.03/1.48  --inst_learning_loop_flag               true
% 8.03/1.48  --inst_learning_start                   3000
% 8.03/1.48  --inst_learning_factor                  2
% 8.03/1.48  --inst_start_prop_sim_after_learn       3
% 8.03/1.48  --inst_sel_renew                        solver
% 8.03/1.48  --inst_lit_activity_flag                true
% 8.03/1.48  --inst_restr_to_given                   false
% 8.03/1.48  --inst_activity_threshold               500
% 8.03/1.48  --inst_out_proof                        true
% 8.03/1.48  
% 8.03/1.48  ------ Resolution Options
% 8.03/1.48  
% 8.03/1.48  --resolution_flag                       false
% 8.03/1.48  --res_lit_sel                           adaptive
% 8.03/1.48  --res_lit_sel_side                      none
% 8.03/1.48  --res_ordering                          kbo
% 8.03/1.48  --res_to_prop_solver                    active
% 8.03/1.48  --res_prop_simpl_new                    false
% 8.03/1.48  --res_prop_simpl_given                  true
% 8.03/1.48  --res_passive_queue_type                priority_queues
% 8.03/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.03/1.48  --res_passive_queues_freq               [15;5]
% 8.03/1.48  --res_forward_subs                      full
% 8.03/1.48  --res_backward_subs                     full
% 8.03/1.48  --res_forward_subs_resolution           true
% 8.03/1.48  --res_backward_subs_resolution          true
% 8.03/1.48  --res_orphan_elimination                true
% 8.03/1.48  --res_time_limit                        2.
% 8.03/1.48  --res_out_proof                         true
% 8.03/1.48  
% 8.03/1.48  ------ Superposition Options
% 8.03/1.48  
% 8.03/1.48  --superposition_flag                    true
% 8.03/1.48  --sup_passive_queue_type                priority_queues
% 8.03/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.03/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.03/1.48  --demod_completeness_check              fast
% 8.03/1.48  --demod_use_ground                      true
% 8.03/1.48  --sup_to_prop_solver                    passive
% 8.03/1.48  --sup_prop_simpl_new                    true
% 8.03/1.48  --sup_prop_simpl_given                  true
% 8.03/1.48  --sup_fun_splitting                     true
% 8.03/1.48  --sup_smt_interval                      50000
% 8.03/1.48  
% 8.03/1.48  ------ Superposition Simplification Setup
% 8.03/1.48  
% 8.03/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.03/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.03/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.03/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.03/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.03/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.03/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.03/1.48  --sup_immed_triv                        [TrivRules]
% 8.03/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_immed_bw_main                     []
% 8.03/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.03/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.03/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.03/1.48  --sup_input_bw                          []
% 8.03/1.48  
% 8.03/1.48  ------ Combination Options
% 8.03/1.48  
% 8.03/1.48  --comb_res_mult                         3
% 8.03/1.48  --comb_sup_mult                         2
% 8.03/1.48  --comb_inst_mult                        10
% 8.03/1.48  
% 8.03/1.48  ------ Debug Options
% 8.03/1.48  
% 8.03/1.48  --dbg_backtrace                         false
% 8.03/1.48  --dbg_dump_prop_clauses                 false
% 8.03/1.48  --dbg_dump_prop_clauses_file            -
% 8.03/1.48  --dbg_out_stat                          false
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  ------ Proving...
% 8.03/1.48  
% 8.03/1.48  
% 8.03/1.48  % SZS status Theorem for theBenchmark.p
% 8.03/1.48  
% 8.03/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 8.03/1.48  
% 8.03/1.48  fof(f27,conjecture,(
% 8.03/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f28,negated_conjecture,(
% 8.03/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 8.03/1.48    inference(negated_conjecture,[],[f27])).
% 8.03/1.48  
% 8.03/1.48  fof(f54,plain,(
% 8.03/1.48    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 8.03/1.48    inference(ennf_transformation,[],[f28])).
% 8.03/1.48  
% 8.03/1.48  fof(f55,plain,(
% 8.03/1.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 8.03/1.48    inference(flattening,[],[f54])).
% 8.03/1.48  
% 8.03/1.48  fof(f68,plain,(
% 8.03/1.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 8.03/1.48    introduced(choice_axiom,[])).
% 8.03/1.48  
% 8.03/1.48  fof(f69,plain,(
% 8.03/1.48    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 8.03/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f55,f68])).
% 8.03/1.48  
% 8.03/1.48  fof(f124,plain,(
% 8.03/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 8.03/1.48    inference(cnf_transformation,[],[f69])).
% 8.03/1.48  
% 8.03/1.48  fof(f21,axiom,(
% 8.03/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f46,plain,(
% 8.03/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.03/1.48    inference(ennf_transformation,[],[f21])).
% 8.03/1.48  
% 8.03/1.48  fof(f104,plain,(
% 8.03/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.03/1.48    inference(cnf_transformation,[],[f46])).
% 8.03/1.48  
% 8.03/1.48  fof(f126,plain,(
% 8.03/1.48    k2_relset_1(sK2,sK3,sK4) = sK3),
% 8.03/1.48    inference(cnf_transformation,[],[f69])).
% 8.03/1.48  
% 8.03/1.48  fof(f17,axiom,(
% 8.03/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f41,plain,(
% 8.03/1.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.03/1.48    inference(ennf_transformation,[],[f17])).
% 8.03/1.48  
% 8.03/1.48  fof(f42,plain,(
% 8.03/1.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.03/1.48    inference(flattening,[],[f41])).
% 8.03/1.48  
% 8.03/1.48  fof(f98,plain,(
% 8.03/1.48    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f42])).
% 8.03/1.48  
% 8.03/1.48  fof(f125,plain,(
% 8.03/1.48    v2_funct_1(sK4)),
% 8.03/1.48    inference(cnf_transformation,[],[f69])).
% 8.03/1.48  
% 8.03/1.48  fof(f122,plain,(
% 8.03/1.48    v1_funct_1(sK4)),
% 8.03/1.48    inference(cnf_transformation,[],[f69])).
% 8.03/1.48  
% 8.03/1.48  fof(f18,axiom,(
% 8.03/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f43,plain,(
% 8.03/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.03/1.48    inference(ennf_transformation,[],[f18])).
% 8.03/1.48  
% 8.03/1.48  fof(f100,plain,(
% 8.03/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.03/1.48    inference(cnf_transformation,[],[f43])).
% 8.03/1.48  
% 8.03/1.48  fof(f25,axiom,(
% 8.03/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f50,plain,(
% 8.03/1.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.03/1.48    inference(ennf_transformation,[],[f25])).
% 8.03/1.48  
% 8.03/1.48  fof(f51,plain,(
% 8.03/1.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.03/1.48    inference(flattening,[],[f50])).
% 8.03/1.48  
% 8.03/1.48  fof(f115,plain,(
% 8.03/1.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f51])).
% 8.03/1.48  
% 8.03/1.48  fof(f26,axiom,(
% 8.03/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f52,plain,(
% 8.03/1.48    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 8.03/1.48    inference(ennf_transformation,[],[f26])).
% 8.03/1.48  
% 8.03/1.48  fof(f53,plain,(
% 8.03/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 8.03/1.48    inference(flattening,[],[f52])).
% 8.03/1.48  
% 8.03/1.48  fof(f120,plain,(
% 8.03/1.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f53])).
% 8.03/1.48  
% 8.03/1.48  fof(f114,plain,(
% 8.03/1.48    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f51])).
% 8.03/1.48  
% 8.03/1.48  fof(f99,plain,(
% 8.03/1.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f42])).
% 8.03/1.48  
% 8.03/1.48  fof(f9,axiom,(
% 8.03/1.48    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f85,plain,(
% 8.03/1.48    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f9])).
% 8.03/1.48  
% 8.03/1.48  fof(f14,axiom,(
% 8.03/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f39,plain,(
% 8.03/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.03/1.48    inference(ennf_transformation,[],[f14])).
% 8.03/1.48  
% 8.03/1.48  fof(f40,plain,(
% 8.03/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.03/1.48    inference(flattening,[],[f39])).
% 8.03/1.48  
% 8.03/1.48  fof(f93,plain,(
% 8.03/1.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f40])).
% 8.03/1.48  
% 8.03/1.48  fof(f10,axiom,(
% 8.03/1.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f34,plain,(
% 8.03/1.48    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f10])).
% 8.03/1.48  
% 8.03/1.48  fof(f35,plain,(
% 8.03/1.48    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 8.03/1.48    inference(flattening,[],[f34])).
% 8.03/1.48  
% 8.03/1.48  fof(f86,plain,(
% 8.03/1.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f35])).
% 8.03/1.48  
% 8.03/1.48  fof(f92,plain,(
% 8.03/1.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f40])).
% 8.03/1.48  
% 8.03/1.48  fof(f2,axiom,(
% 8.03/1.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f58,plain,(
% 8.03/1.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 8.03/1.48    inference(nnf_transformation,[],[f2])).
% 8.03/1.48  
% 8.03/1.48  fof(f59,plain,(
% 8.03/1.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 8.03/1.48    inference(flattening,[],[f58])).
% 8.03/1.48  
% 8.03/1.48  fof(f75,plain,(
% 8.03/1.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 8.03/1.48    inference(cnf_transformation,[],[f59])).
% 8.03/1.48  
% 8.03/1.48  fof(f130,plain,(
% 8.03/1.48    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 8.03/1.48    inference(equality_resolution,[],[f75])).
% 8.03/1.48  
% 8.03/1.48  fof(f8,axiom,(
% 8.03/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f33,plain,(
% 8.03/1.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 8.03/1.48    inference(ennf_transformation,[],[f8])).
% 8.03/1.48  
% 8.03/1.48  fof(f62,plain,(
% 8.03/1.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 8.03/1.48    inference(nnf_transformation,[],[f33])).
% 8.03/1.48  
% 8.03/1.48  fof(f82,plain,(
% 8.03/1.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f62])).
% 8.03/1.48  
% 8.03/1.48  fof(f4,axiom,(
% 8.03/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f60,plain,(
% 8.03/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.03/1.48    inference(nnf_transformation,[],[f4])).
% 8.03/1.48  
% 8.03/1.48  fof(f78,plain,(
% 8.03/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f60])).
% 8.03/1.48  
% 8.03/1.48  fof(f19,axiom,(
% 8.03/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f44,plain,(
% 8.03/1.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.03/1.48    inference(ennf_transformation,[],[f19])).
% 8.03/1.48  
% 8.03/1.48  fof(f101,plain,(
% 8.03/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.03/1.48    inference(cnf_transformation,[],[f44])).
% 8.03/1.48  
% 8.03/1.48  fof(f7,axiom,(
% 8.03/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f32,plain,(
% 8.03/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 8.03/1.48    inference(ennf_transformation,[],[f7])).
% 8.03/1.48  
% 8.03/1.48  fof(f61,plain,(
% 8.03/1.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 8.03/1.48    inference(nnf_transformation,[],[f32])).
% 8.03/1.48  
% 8.03/1.48  fof(f80,plain,(
% 8.03/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f61])).
% 8.03/1.48  
% 8.03/1.48  fof(f13,axiom,(
% 8.03/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f37,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.03/1.48    inference(ennf_transformation,[],[f13])).
% 8.03/1.48  
% 8.03/1.48  fof(f38,plain,(
% 8.03/1.48    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.03/1.48    inference(flattening,[],[f37])).
% 8.03/1.48  
% 8.03/1.48  fof(f91,plain,(
% 8.03/1.48    ( ! [X0,X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f38])).
% 8.03/1.48  
% 8.03/1.48  fof(f77,plain,(
% 8.03/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 8.03/1.48    inference(cnf_transformation,[],[f60])).
% 8.03/1.48  
% 8.03/1.48  fof(f3,axiom,(
% 8.03/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f76,plain,(
% 8.03/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 8.03/1.48    inference(cnf_transformation,[],[f3])).
% 8.03/1.48  
% 8.03/1.48  fof(f1,axiom,(
% 8.03/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f56,plain,(
% 8.03/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.03/1.48    inference(nnf_transformation,[],[f1])).
% 8.03/1.48  
% 8.03/1.48  fof(f57,plain,(
% 8.03/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.03/1.48    inference(flattening,[],[f56])).
% 8.03/1.48  
% 8.03/1.48  fof(f72,plain,(
% 8.03/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f57])).
% 8.03/1.48  
% 8.03/1.48  fof(f127,plain,(
% 8.03/1.48    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 8.03/1.48    inference(cnf_transformation,[],[f69])).
% 8.03/1.48  
% 8.03/1.48  fof(f87,plain,(
% 8.03/1.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f35])).
% 8.03/1.48  
% 8.03/1.48  fof(f24,axiom,(
% 8.03/1.48    ! [X0,X1] : ? [X2] : (v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f66,plain,(
% 8.03/1.48    ! [X1,X0] : (? [X2] : (v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v5_relat_1(sK1(X0,X1),X1) & v4_relat_1(sK1(X0,X1),X0) & v1_relat_1(sK1(X0,X1)) & v1_xboole_0(sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 8.03/1.48    introduced(choice_axiom,[])).
% 8.03/1.48  
% 8.03/1.48  fof(f67,plain,(
% 8.03/1.48    ! [X0,X1] : (v5_relat_1(sK1(X0,X1),X1) & v4_relat_1(sK1(X0,X1),X0) & v1_relat_1(sK1(X0,X1)) & v1_xboole_0(sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.03/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f66])).
% 8.03/1.48  
% 8.03/1.48  fof(f109,plain,(
% 8.03/1.48    ( ! [X0,X1] : (v1_xboole_0(sK1(X0,X1))) )),
% 8.03/1.48    inference(cnf_transformation,[],[f67])).
% 8.03/1.48  
% 8.03/1.48  fof(f20,axiom,(
% 8.03/1.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f45,plain,(
% 8.03/1.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f20])).
% 8.03/1.48  
% 8.03/1.48  fof(f103,plain,(
% 8.03/1.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f45])).
% 8.03/1.48  
% 8.03/1.48  fof(f123,plain,(
% 8.03/1.48    v1_funct_2(sK4,sK2,sK3)),
% 8.03/1.48    inference(cnf_transformation,[],[f69])).
% 8.03/1.48  
% 8.03/1.48  fof(f23,axiom,(
% 8.03/1.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 8.03/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.48  
% 8.03/1.48  fof(f49,plain,(
% 8.03/1.48    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 8.03/1.48    inference(ennf_transformation,[],[f23])).
% 8.03/1.48  
% 8.03/1.48  fof(f107,plain,(
% 8.03/1.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 8.03/1.48    inference(cnf_transformation,[],[f49])).
% 8.03/1.48  
% 8.03/1.48  fof(f22,axiom,(
% 8.03/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 8.03/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.03/1.49  
% 8.03/1.49  fof(f47,plain,(
% 8.03/1.49    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.03/1.49    inference(ennf_transformation,[],[f22])).
% 8.03/1.49  
% 8.03/1.49  fof(f48,plain,(
% 8.03/1.49    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.03/1.49    inference(flattening,[],[f47])).
% 8.03/1.49  
% 8.03/1.49  fof(f106,plain,(
% 8.03/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.03/1.49    inference(cnf_transformation,[],[f48])).
% 8.03/1.49  
% 8.03/1.49  fof(f118,plain,(
% 8.03/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 8.03/1.49    inference(cnf_transformation,[],[f53])).
% 8.03/1.49  
% 8.03/1.49  cnf(c_55,negated_conjecture,
% 8.03/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 8.03/1.49      inference(cnf_transformation,[],[f124]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2126,plain,
% 8.03/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_34,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f104]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2138,plain,
% 8.03/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 8.03/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5385,plain,
% 8.03/1.49      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2126,c_2138]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_53,negated_conjecture,
% 8.03/1.49      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 8.03/1.49      inference(cnf_transformation,[],[f126]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5388,plain,
% 8.03/1.49      ( k2_relat_1(sK4) = sK3 ),
% 8.03/1.49      inference(light_normalisation,[status(thm)],[c_5385,c_53]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_29,plain,
% 8.03/1.49      ( ~ v2_funct_1(X0)
% 8.03/1.49      | ~ v1_funct_1(X0)
% 8.03/1.49      | ~ v1_relat_1(X0)
% 8.03/1.49      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f98]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_54,negated_conjecture,
% 8.03/1.49      ( v2_funct_1(sK4) ),
% 8.03/1.49      inference(cnf_transformation,[],[f125]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_749,plain,
% 8.03/1.49      ( ~ v1_funct_1(X0)
% 8.03/1.49      | ~ v1_relat_1(X0)
% 8.03/1.49      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 8.03/1.49      | sK4 != X0 ),
% 8.03/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_54]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_750,plain,
% 8.03/1.49      ( ~ v1_funct_1(sK4)
% 8.03/1.49      | ~ v1_relat_1(sK4)
% 8.03/1.49      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 8.03/1.49      inference(unflattening,[status(thm)],[c_749]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_57,negated_conjecture,
% 8.03/1.49      ( v1_funct_1(sK4) ),
% 8.03/1.49      inference(cnf_transformation,[],[f122]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_752,plain,
% 8.03/1.49      ( ~ v1_relat_1(sK4)
% 8.03/1.49      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_750,c_57]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2116,plain,
% 8.03/1.49      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 8.03/1.49      | v1_relat_1(sK4) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_30,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | v1_relat_1(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f100]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2230,plain,
% 8.03/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.03/1.49      | v1_relat_1(sK4) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_30]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2301,plain,
% 8.03/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 8.03/1.49      | v1_relat_1(sK4) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2230]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2498,plain,
% 8.03/1.49      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_2116,c_57,c_55,c_750,c_2301]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5395,plain,
% 8.03/1.49      ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
% 8.03/1.49      inference(demodulation,[status(thm)],[c_5388,c_2498]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_43,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 8.03/1.49      | ~ v1_funct_1(X0)
% 8.03/1.49      | ~ v1_relat_1(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f115]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2133,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 8.03/1.49      | v1_funct_1(X0) != iProver_top
% 8.03/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_47,plain,
% 8.03/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 8.03/1.49      | ~ r1_tarski(X2,X3)
% 8.03/1.49      | ~ v1_funct_1(X0)
% 8.03/1.49      | k1_xboole_0 = X2 ),
% 8.03/1.49      inference(cnf_transformation,[],[f120]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2130,plain,
% 8.03/1.49      ( k1_xboole_0 = X0
% 8.03/1.49      | v1_funct_2(X1,X2,X0) != iProver_top
% 8.03/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 8.03/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 8.03/1.49      | r1_tarski(X0,X3) != iProver_top
% 8.03/1.49      | v1_funct_1(X1) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7573,plain,
% 8.03/1.49      ( k2_relat_1(X0) = k1_xboole_0
% 8.03/1.49      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
% 8.03/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 8.03/1.49      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 8.03/1.49      | v1_funct_1(X0) != iProver_top
% 8.03/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2133,c_2130]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_44,plain,
% 8.03/1.49      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 8.03/1.49      | ~ v1_funct_1(X0)
% 8.03/1.49      | ~ v1_relat_1(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f114]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_70,plain,
% 8.03/1.49      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 8.03/1.49      | v1_funct_1(X0) != iProver_top
% 8.03/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_36899,plain,
% 8.03/1.49      ( k2_relat_1(X0) = k1_xboole_0
% 8.03/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 8.03/1.49      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 8.03/1.49      | v1_funct_1(X0) != iProver_top
% 8.03/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_7573,c_70]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_36904,plain,
% 8.03/1.49      ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 8.03/1.49      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 8.03/1.49      | r1_tarski(k2_relat_1(k2_funct_1(sK4)),X0) != iProver_top
% 8.03/1.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 8.03/1.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_5395,c_36899]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_28,plain,
% 8.03/1.49      ( ~ v2_funct_1(X0)
% 8.03/1.49      | ~ v1_funct_1(X0)
% 8.03/1.49      | ~ v1_relat_1(X0)
% 8.03/1.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f99]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_763,plain,
% 8.03/1.49      ( ~ v1_funct_1(X0)
% 8.03/1.49      | ~ v1_relat_1(X0)
% 8.03/1.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 8.03/1.49      | sK4 != X0 ),
% 8.03/1.49      inference(resolution_lifted,[status(thm)],[c_28,c_54]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_764,plain,
% 8.03/1.49      ( ~ v1_funct_1(sK4)
% 8.03/1.49      | ~ v1_relat_1(sK4)
% 8.03/1.49      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 8.03/1.49      inference(unflattening,[status(thm)],[c_763]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_766,plain,
% 8.03/1.49      ( ~ v1_relat_1(sK4)
% 8.03/1.49      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_764,c_57]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2115,plain,
% 8.03/1.49      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 8.03/1.49      | v1_relat_1(sK4) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2452,plain,
% 8.03/1.49      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_2115,c_57,c_55,c_764,c_2301]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_36915,plain,
% 8.03/1.49      ( k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 8.03/1.49      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 8.03/1.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 8.03/1.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(light_normalisation,[status(thm)],[c_36904,c_2452]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_36916,plain,
% 8.03/1.49      ( k1_relat_1(sK4) = k1_xboole_0
% 8.03/1.49      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 8.03/1.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 8.03/1.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(demodulation,[status(thm)],[c_36915,c_2452]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_58,plain,
% 8.03/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_60,plain,
% 8.03/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_14,plain,
% 8.03/1.49      ( v5_relat_1(k1_xboole_0,X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f85]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_147,plain,
% 8.03/1.49      ( v5_relat_1(k1_xboole_0,X0) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_149,plain,
% 8.03/1.49      ( v5_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_147]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_22,plain,
% 8.03/1.49      ( ~ v1_funct_1(X0)
% 8.03/1.49      | v1_funct_1(k2_funct_1(X0))
% 8.03/1.49      | ~ v1_relat_1(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f93]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2222,plain,
% 8.03/1.49      ( v1_funct_1(k2_funct_1(sK4))
% 8.03/1.49      | ~ v1_funct_1(sK4)
% 8.03/1.49      | ~ v1_relat_1(sK4) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_22]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2223,plain,
% 8.03/1.49      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 8.03/1.49      | v1_funct_1(sK4) != iProver_top
% 8.03/1.49      | v1_relat_1(sK4) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_2222]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2302,plain,
% 8.03/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 8.03/1.49      | v1_relat_1(sK4) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_2301]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_17,plain,
% 8.03/1.49      ( ~ v1_relat_1(X0)
% 8.03/1.49      | k1_relat_1(X0) != k1_xboole_0
% 8.03/1.49      | k1_xboole_0 = X0 ),
% 8.03/1.49      inference(cnf_transformation,[],[f86]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2581,plain,
% 8.03/1.49      ( ~ v1_relat_1(sK4)
% 8.03/1.49      | k1_relat_1(sK4) != k1_xboole_0
% 8.03/1.49      | k1_xboole_0 = sK4 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_23,plain,
% 8.03/1.49      ( ~ v1_funct_1(X0)
% 8.03/1.49      | ~ v1_relat_1(X0)
% 8.03/1.49      | v1_relat_1(k2_funct_1(X0)) ),
% 8.03/1.49      inference(cnf_transformation,[],[f92]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2597,plain,
% 8.03/1.49      ( ~ v1_funct_1(sK4)
% 8.03/1.49      | v1_relat_1(k2_funct_1(sK4))
% 8.03/1.49      | ~ v1_relat_1(sK4) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_23]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2598,plain,
% 8.03/1.49      ( v1_funct_1(sK4) != iProver_top
% 8.03/1.49      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 8.03/1.49      | v1_relat_1(sK4) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_2597]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1170,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2400,plain,
% 8.03/1.49      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1170]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2773,plain,
% 8.03/1.49      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2400]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2774,plain,
% 8.03/1.49      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2773]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1169,plain,( X0 = X0 ),theory(equality) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2843,plain,
% 8.03/1.49      ( sK4 = sK4 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1169]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2132,plain,
% 8.03/1.49      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 8.03/1.49      | v1_funct_1(X0) != iProver_top
% 8.03/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6968,plain,
% 8.03/1.49      ( v1_funct_2(k2_funct_1(sK4),k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)) = iProver_top
% 8.03/1.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 8.03/1.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2452,c_2132]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6969,plain,
% 8.03/1.49      ( v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) = iProver_top
% 8.03/1.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 8.03/1.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(light_normalisation,[status(thm)],[c_6968,c_5395]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1175,plain,
% 8.03/1.49      ( ~ v5_relat_1(X0,X1) | v5_relat_1(X2,X1) | X2 != X0 ),
% 8.03/1.49      theory(equality) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7771,plain,
% 8.03/1.49      ( ~ v5_relat_1(X0,k1_xboole_0)
% 8.03/1.49      | v5_relat_1(sK4,k1_xboole_0)
% 8.03/1.49      | sK4 != X0 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1175]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7772,plain,
% 8.03/1.49      ( sK4 != X0
% 8.03/1.49      | v5_relat_1(X0,k1_xboole_0) != iProver_top
% 8.03/1.49      | v5_relat_1(sK4,k1_xboole_0) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_7771]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7774,plain,
% 8.03/1.49      ( sK4 != k1_xboole_0
% 8.03/1.49      | v5_relat_1(sK4,k1_xboole_0) = iProver_top
% 8.03/1.49      | v5_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_7772]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7566,plain,
% 8.03/1.49      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
% 8.03/1.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 8.03/1.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2452,c_2133]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7575,plain,
% 8.03/1.49      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
% 8.03/1.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 8.03/1.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(light_normalisation,[status(thm)],[c_7566,c_5395]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_8831,plain,
% 8.03/1.49      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_7575,c_58,c_60,c_2223,c_2302,c_2598]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_8843,plain,
% 8.03/1.49      ( k1_relat_1(sK4) = k1_xboole_0
% 8.03/1.49      | v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) != iProver_top
% 8.03/1.49      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 8.03/1.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_8831,c_2130]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3,plain,
% 8.03/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 8.03/1.49      inference(cnf_transformation,[],[f130]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_13,plain,
% 8.03/1.49      ( ~ v5_relat_1(X0,X1)
% 8.03/1.49      | r1_tarski(k2_relat_1(X0),X1)
% 8.03/1.49      | ~ v1_relat_1(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f82]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2152,plain,
% 8.03/1.49      ( v5_relat_1(X0,X1) != iProver_top
% 8.03/1.49      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 8.03/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f78]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2156,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 8.03/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_32,plain,
% 8.03/1.49      ( v4_relat_1(X0,X1)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 8.03/1.49      inference(cnf_transformation,[],[f101]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_11,plain,
% 8.03/1.49      ( ~ v4_relat_1(X0,X1)
% 8.03/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 8.03/1.49      | ~ v1_relat_1(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f80]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_660,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 8.03/1.49      | ~ v1_relat_1(X0) ),
% 8.03/1.49      inference(resolution,[status(thm)],[c_32,c_11]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_664,plain,
% 8.03/1.49      ( r1_tarski(k1_relat_1(X0),X1)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_660,c_30]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_665,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | r1_tarski(k1_relat_1(X0),X1) ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_664]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2121,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4117,plain,
% 8.03/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2156,c_2121]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_9208,plain,
% 8.03/1.49      ( v5_relat_1(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(k2_relat_1(X0)),X1) = iProver_top
% 8.03/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2152,c_4117]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_27524,plain,
% 8.03/1.49      ( v5_relat_1(X0,k1_xboole_0) != iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(k2_relat_1(X0)),X1) = iProver_top
% 8.03/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_3,c_9208]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_27854,plain,
% 8.03/1.49      ( v5_relat_1(sK4,k1_xboole_0) != iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 8.03/1.49      | v1_relat_1(sK4) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_5388,c_27524]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_21,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.03/1.49      | ~ v1_funct_1(X1)
% 8.03/1.49      | v1_funct_1(X0)
% 8.03/1.49      | ~ v1_relat_1(X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f91]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_388,plain,
% 8.03/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.03/1.49      inference(prop_impl,[status(thm)],[c_7]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_389,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_388]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_470,plain,
% 8.03/1.49      ( ~ r1_tarski(X0,X1)
% 8.03/1.49      | ~ v1_funct_1(X1)
% 8.03/1.49      | v1_funct_1(X0)
% 8.03/1.49      | ~ v1_relat_1(X1) ),
% 8.03/1.49      inference(bin_hyper_res,[status(thm)],[c_21,c_389]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2505,plain,
% 8.03/1.49      ( ~ r1_tarski(X0,sK4)
% 8.03/1.49      | v1_funct_1(X0)
% 8.03/1.49      | ~ v1_funct_1(sK4)
% 8.03/1.49      | ~ v1_relat_1(sK4) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_470]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2506,plain,
% 8.03/1.49      ( r1_tarski(X0,sK4) != iProver_top
% 8.03/1.49      | v1_funct_1(X0) = iProver_top
% 8.03/1.49      | v1_funct_1(sK4) != iProver_top
% 8.03/1.49      | v1_relat_1(sK4) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_2505]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2508,plain,
% 8.03/1.49      ( r1_tarski(k1_xboole_0,sK4) != iProver_top
% 8.03/1.49      | v1_funct_1(sK4) != iProver_top
% 8.03/1.49      | v1_funct_1(k1_xboole_0) = iProver_top
% 8.03/1.49      | v1_relat_1(sK4) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2506]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_8,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f77]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2542,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4)) | r1_tarski(X0,sK4) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2543,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 8.03/1.49      | r1_tarski(X0,sK4) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_2542]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2545,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
% 8.03/1.49      | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2543]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3087,plain,
% 8.03/1.49      ( sK2 = sK2 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1169]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 8.03/1.49      inference(cnf_transformation,[],[f76]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3171,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3172,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_3171]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1171,plain,
% 8.03/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 8.03/1.49      theory(equality) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2956,plain,
% 8.03/1.49      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 8.03/1.49      | r1_tarski(X3,k2_zfmisc_1(X1,X2))
% 8.03/1.49      | X3 != X0 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1171]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4072,plain,
% 8.03/1.49      ( ~ r1_tarski(X0,k2_zfmisc_1(sK3,sK2))
% 8.03/1.49      | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2))
% 8.03/1.49      | k2_funct_1(sK4) != X0 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2956]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4073,plain,
% 8.03/1.49      ( k2_funct_1(sK4) != X0
% 8.03/1.49      | r1_tarski(X0,k2_zfmisc_1(sK3,sK2)) != iProver_top
% 8.03/1.49      | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_4072]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4075,plain,
% 8.03/1.49      ( k2_funct_1(sK4) != k1_xboole_0
% 8.03/1.49      | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) = iProver_top
% 8.03/1.49      | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK2)) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_4073]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_0,plain,
% 8.03/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 8.03/1.49      inference(cnf_transformation,[],[f72]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4104,plain,
% 8.03/1.49      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4105,plain,
% 8.03/1.49      ( sK3 = X0
% 8.03/1.49      | r1_tarski(X0,sK3) != iProver_top
% 8.03/1.49      | r1_tarski(sK3,X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_4104]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4107,plain,
% 8.03/1.49      ( sK3 = k1_xboole_0
% 8.03/1.49      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 8.03/1.49      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_4105]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_52,negated_conjecture,
% 8.03/1.49      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 8.03/1.49      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.03/1.49      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 8.03/1.49      inference(cnf_transformation,[],[f127]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2127,plain,
% 8.03/1.49      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 8.03/1.49      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.03/1.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_62,plain,
% 8.03/1.49      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 8.03/1.49      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.03/1.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2447,plain,
% 8.03/1.49      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.03/1.49      | v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_2127,c_58,c_60,c_62,c_2223,c_2302]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2448,plain,
% 8.03/1.49      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 8.03/1.49      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_2447]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4118,plain,
% 8.03/1.49      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 8.03/1.49      | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2156,c_2448]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1184,plain,
% 8.03/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 8.03/1.49      | v1_funct_2(X3,X4,X5)
% 8.03/1.49      | X3 != X0
% 8.03/1.49      | X4 != X1
% 8.03/1.49      | X5 != X2 ),
% 8.03/1.49      theory(equality) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2364,plain,
% 8.03/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 8.03/1.49      | v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 8.03/1.49      | k2_funct_1(sK4) != X0
% 8.03/1.49      | sK2 != X2
% 8.03/1.49      | sK3 != X1 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1184]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2572,plain,
% 8.03/1.49      ( ~ v1_funct_2(X0,X1,sK2)
% 8.03/1.49      | v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 8.03/1.49      | k2_funct_1(sK4) != X0
% 8.03/1.49      | sK2 != sK2
% 8.03/1.49      | sK3 != X1 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2364]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4143,plain,
% 8.03/1.49      ( ~ v1_funct_2(X0,sK3,sK2)
% 8.03/1.49      | v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 8.03/1.49      | k2_funct_1(sK4) != X0
% 8.03/1.49      | sK2 != sK2
% 8.03/1.49      | sK3 != sK3 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2572]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4144,plain,
% 8.03/1.49      ( k2_funct_1(sK4) != X0
% 8.03/1.49      | sK2 != sK2
% 8.03/1.49      | sK3 != sK3
% 8.03/1.49      | v1_funct_2(X0,sK3,sK2) != iProver_top
% 8.03/1.49      | v1_funct_2(k2_funct_1(sK4),sK3,sK2) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_4143]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4146,plain,
% 8.03/1.49      ( k2_funct_1(sK4) != k1_xboole_0
% 8.03/1.49      | sK2 != sK2
% 8.03/1.49      | sK3 != sK3
% 8.03/1.49      | v1_funct_2(k2_funct_1(sK4),sK3,sK2) = iProver_top
% 8.03/1.49      | v1_funct_2(k1_xboole_0,sK3,sK2) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_4144]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_16,plain,
% 8.03/1.49      ( ~ v1_relat_1(X0)
% 8.03/1.49      | k2_relat_1(X0) != k1_xboole_0
% 8.03/1.49      | k1_xboole_0 = X0 ),
% 8.03/1.49      inference(cnf_transformation,[],[f87]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2150,plain,
% 8.03/1.49      ( k2_relat_1(X0) != k1_xboole_0
% 8.03/1.49      | k1_xboole_0 = X0
% 8.03/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4654,plain,
% 8.03/1.49      ( k2_funct_1(sK4) = k1_xboole_0
% 8.03/1.49      | k1_relat_1(sK4) != k1_xboole_0
% 8.03/1.49      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2452,c_2150]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4656,plain,
% 8.03/1.49      ( ~ v1_relat_1(k2_funct_1(sK4))
% 8.03/1.49      | k2_funct_1(sK4) = k1_xboole_0
% 8.03/1.49      | k1_relat_1(sK4) != k1_xboole_0 ),
% 8.03/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4654]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4778,plain,
% 8.03/1.49      ( k1_relat_1(sK4) != k1_xboole_0 | k2_funct_1(sK4) = k1_xboole_0 ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_4654,c_57,c_55,c_2301,c_2597,c_4656]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4779,plain,
% 8.03/1.49      ( k2_funct_1(sK4) = k1_xboole_0 | k1_relat_1(sK4) != k1_xboole_0 ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_4778]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2936,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6603,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.03/1.49      | r1_tarski(X0,k2_zfmisc_1(sK3,sK2)) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2936]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6604,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.03/1.49      | r1_tarski(X0,k2_zfmisc_1(sK3,sK2)) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_6603]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6606,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.03/1.49      | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK3,sK2)) = iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_6604]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6633,plain,
% 8.03/1.49      ( sK3 = sK3 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1169]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6654,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6655,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 8.03/1.49      | r1_tarski(X0,sK3) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_6654]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6657,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 8.03/1.49      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_6655]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6833,plain,
% 8.03/1.49      ( v5_relat_1(sK4,X0) != iProver_top
% 8.03/1.49      | r1_tarski(sK3,X0) = iProver_top
% 8.03/1.49      | v1_relat_1(sK4) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_5388,c_2152]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6839,plain,
% 8.03/1.49      ( v5_relat_1(sK4,k1_xboole_0) != iProver_top
% 8.03/1.49      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 8.03/1.49      | v1_relat_1(sK4) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_6833]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_41,plain,
% 8.03/1.49      ( v1_xboole_0(sK1(X0,X1)) ),
% 8.03/1.49      inference(cnf_transformation,[],[f109]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2135,plain,
% 8.03/1.49      ( v1_xboole_0(sK1(X0,X1)) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2157,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_33,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | ~ v1_xboole_0(X1)
% 8.03/1.49      | v1_xboole_0(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f103]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2139,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.03/1.49      | v1_xboole_0(X1) != iProver_top
% 8.03/1.49      | v1_xboole_0(X0) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7781,plain,
% 8.03/1.49      ( v1_xboole_0(X0) != iProver_top
% 8.03/1.49      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2157,c_2139]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_10433,plain,
% 8.03/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2135,c_7781]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6701,plain,
% 8.03/1.49      ( sK3 = k1_xboole_0
% 8.03/1.49      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 8.03/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 8.03/1.49      | r1_tarski(sK3,X0) != iProver_top
% 8.03/1.49      | v1_funct_1(sK4) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2126,c_2130]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_56,negated_conjecture,
% 8.03/1.49      ( v1_funct_2(sK4,sK2,sK3) ),
% 8.03/1.49      inference(cnf_transformation,[],[f123]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_59,plain,
% 8.03/1.49      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7162,plain,
% 8.03/1.49      ( r1_tarski(sK3,X0) != iProver_top
% 8.03/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 8.03/1.49      | sK3 = k1_xboole_0 ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_6701,c_58,c_59]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7163,plain,
% 8.03/1.49      ( sK3 = k1_xboole_0
% 8.03/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 8.03/1.49      | r1_tarski(sK3,X0) != iProver_top ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_7162]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7168,plain,
% 8.03/1.49      ( sK3 = k1_xboole_0
% 8.03/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 8.03/1.49      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_3,c_7163]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_159,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.03/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_161,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 8.03/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_159]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_165,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_167,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_165]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4062,plain,
% 8.03/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X1) | sK4 != X0 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1171]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4063,plain,
% 8.03/1.49      ( sK4 != X0
% 8.03/1.49      | r1_tarski(X0,X1) != iProver_top
% 8.03/1.49      | r1_tarski(sK4,X1) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_4062]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_4065,plain,
% 8.03/1.49      ( sK4 != k1_xboole_0
% 8.03/1.49      | r1_tarski(sK4,k1_xboole_0) = iProver_top
% 8.03/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_4063]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5230,plain,
% 8.03/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~ r1_tarski(sK4,X0) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5231,plain,
% 8.03/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top
% 8.03/1.49      | r1_tarski(sK4,X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_5230]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5233,plain,
% 8.03/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 8.03/1.49      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_5231]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_5397,plain,
% 8.03/1.49      ( sK3 != k1_xboole_0
% 8.03/1.49      | sK4 = k1_xboole_0
% 8.03/1.49      | v1_relat_1(sK4) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_5388,c_2150]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7596,plain,
% 8.03/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 8.03/1.49      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_7168,c_60,c_161,c_167,c_2302,c_4065,c_5233,c_5397]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3902,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_3,c_2121]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_7602,plain,
% 8.03/1.49      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 8.03/1.49      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_7596,c_3902]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2155,plain,
% 8.03/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.03/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3707,plain,
% 8.03/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2157,c_2155]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2159,plain,
% 8.03/1.49      ( X0 = X1
% 8.03/1.49      | r1_tarski(X0,X1) != iProver_top
% 8.03/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_6803,plain,
% 8.03/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_3707,c_2159]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_11671,plain,
% 8.03/1.49      ( k1_relat_1(sK4) = k1_xboole_0
% 8.03/1.49      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_7602,c_6803]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_37,plain,
% 8.03/1.49      ( v1_partfun1(X0,X1)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | ~ v1_xboole_0(X1) ),
% 8.03/1.49      inference(cnf_transformation,[],[f107]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_35,plain,
% 8.03/1.49      ( v1_funct_2(X0,X1,X2)
% 8.03/1.49      | ~ v1_partfun1(X0,X1)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | ~ v1_funct_1(X0) ),
% 8.03/1.49      inference(cnf_transformation,[],[f106]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_634,plain,
% 8.03/1.49      ( v1_funct_2(X0,X1,X2)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 8.03/1.49      | ~ v1_xboole_0(X1)
% 8.03/1.49      | ~ v1_funct_1(X0) ),
% 8.03/1.49      inference(resolution,[status(thm)],[c_37,c_35]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_638,plain,
% 8.03/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | v1_funct_2(X0,X1,X2)
% 8.03/1.49      | ~ v1_xboole_0(X1)
% 8.03/1.49      | ~ v1_funct_1(X0) ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_634,c_37,c_35]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_639,plain,
% 8.03/1.49      ( v1_funct_2(X0,X1,X2)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | ~ v1_xboole_0(X1)
% 8.03/1.49      | ~ v1_funct_1(X0) ),
% 8.03/1.49      inference(renaming,[status(thm)],[c_638]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_12917,plain,
% 8.03/1.49      ( v1_funct_2(X0,sK3,sK2)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 8.03/1.49      | ~ v1_xboole_0(sK3)
% 8.03/1.49      | ~ v1_funct_1(X0) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_639]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_12918,plain,
% 8.03/1.49      ( v1_funct_2(X0,sK3,sK2) = iProver_top
% 8.03/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.03/1.49      | v1_xboole_0(sK3) != iProver_top
% 8.03/1.49      | v1_funct_1(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_12917]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_12920,plain,
% 8.03/1.49      ( v1_funct_2(k1_xboole_0,sK3,sK2) = iProver_top
% 8.03/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 8.03/1.49      | v1_xboole_0(sK3) != iProver_top
% 8.03/1.49      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_12918]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2684,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_13093,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_2684]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_13096,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_13093]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_23280,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_23281,plain,
% 8.03/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_23280]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_1182,plain,
% 8.03/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 8.03/1.49      theory(equality) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_27376,plain,
% 8.03/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_1182]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_27377,plain,
% 8.03/1.49      ( sK3 != X0
% 8.03/1.49      | v1_xboole_0(X0) != iProver_top
% 8.03/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_27376]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_27379,plain,
% 8.03/1.49      ( sK3 != k1_xboole_0
% 8.03/1.49      | v1_xboole_0(sK3) = iProver_top
% 8.03/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 8.03/1.49      inference(instantiation,[status(thm)],[c_27377]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_27924,plain,
% 8.03/1.49      ( v5_relat_1(sK4,k1_xboole_0) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_27854,c_58,c_60,c_2302,c_2508,c_2545,c_3087,c_3172,
% 8.03/1.49                 c_4075,c_4107,c_4118,c_4146,c_4779,c_6606,c_6633,c_6657,
% 8.03/1.49                 c_6839,c_10433,c_11671,c_12920,c_13096,c_23281,c_27379]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_37644,plain,
% 8.03/1.49      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_36916,c_58,c_60,c_161,c_167,c_2223,c_2302,c_2508,
% 8.03/1.49                 c_2545,c_2598,c_3087,c_3172,c_4075,c_4107,c_4118,c_4146,
% 8.03/1.49                 c_4654,c_4779,c_5065,c_6606,c_6633,c_6657,c_6969,c_8843,
% 8.03/1.49                 c_9386,c_10433,c_11671,c_12920,c_13096,c_23281,c_27379]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2122,plain,
% 8.03/1.49      ( v1_funct_2(X0,X1,X2) = iProver_top
% 8.03/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.03/1.49      | v1_xboole_0(X1) != iProver_top
% 8.03/1.49      | v1_funct_1(X0) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_37653,plain,
% 8.03/1.49      ( v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 8.03/1.49      | v1_xboole_0(sK3) != iProver_top
% 8.03/1.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_37644,c_2122]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_49,plain,
% 8.03/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 8.03/1.49      | v1_funct_2(X0,X1,X3)
% 8.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.03/1.49      | ~ r1_tarski(X2,X3)
% 8.03/1.49      | ~ v1_funct_1(X0)
% 8.03/1.49      | k1_xboole_0 = X2 ),
% 8.03/1.49      inference(cnf_transformation,[],[f118]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_2128,plain,
% 8.03/1.49      ( k1_xboole_0 = X0
% 8.03/1.49      | v1_funct_2(X1,X2,X0) != iProver_top
% 8.03/1.49      | v1_funct_2(X1,X2,X3) = iProver_top
% 8.03/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 8.03/1.49      | r1_tarski(X0,X3) != iProver_top
% 8.03/1.49      | v1_funct_1(X1) != iProver_top ),
% 8.03/1.49      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_8844,plain,
% 8.03/1.49      ( k1_relat_1(sK4) = k1_xboole_0
% 8.03/1.49      | v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
% 8.03/1.49      | v1_funct_2(k2_funct_1(sK4),sK3,k1_relat_1(sK4)) != iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 8.03/1.49      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_8831,c_2128]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_38464,plain,
% 8.03/1.49      ( v1_funct_2(k2_funct_1(sK4),sK3,X0) = iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_37653,c_58,c_60,c_161,c_167,c_2223,c_2302,c_2508,
% 8.03/1.49                 c_2545,c_2598,c_3087,c_3172,c_4075,c_4107,c_4118,c_4146,
% 8.03/1.49                 c_4654,c_4779,c_5065,c_6606,c_6633,c_6657,c_6969,c_8844,
% 8.03/1.49                 c_9386,c_10433,c_11671,c_12920,c_13096,c_23281,c_27379]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_37657,plain,
% 8.03/1.49      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top
% 8.03/1.49      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_37644,c_2448]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_3901,plain,
% 8.03/1.49      ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_2126,c_2121]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_37758,plain,
% 8.03/1.49      ( v1_funct_2(k2_funct_1(sK4),sK3,sK2) != iProver_top ),
% 8.03/1.49      inference(global_propositional_subsumption,
% 8.03/1.49                [status(thm)],
% 8.03/1.49                [c_37657,c_3901]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(c_38468,plain,
% 8.03/1.49      ( r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 8.03/1.49      inference(superposition,[status(thm)],[c_38464,c_37758]) ).
% 8.03/1.49  
% 8.03/1.49  cnf(contradiction,plain,
% 8.03/1.49      ( $false ),
% 8.03/1.49      inference(minisat,[status(thm)],[c_38468,c_3901]) ).
% 8.03/1.49  
% 8.03/1.49  
% 8.03/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.03/1.49  
% 8.03/1.49  ------                               Statistics
% 8.03/1.49  
% 8.03/1.49  ------ General
% 8.03/1.49  
% 8.03/1.49  abstr_ref_over_cycles:                  0
% 8.03/1.49  abstr_ref_under_cycles:                 0
% 8.03/1.49  gc_basic_clause_elim:                   0
% 8.03/1.49  forced_gc_time:                         0
% 8.03/1.49  parsing_time:                           0.01
% 8.03/1.49  unif_index_cands_time:                  0.
% 8.03/1.49  unif_index_add_time:                    0.
% 8.03/1.49  orderings_time:                         0.
% 8.03/1.49  out_proof_time:                         0.02
% 8.03/1.49  total_time:                             0.958
% 8.03/1.49  num_of_symbols:                         54
% 8.03/1.49  num_of_terms:                           29242
% 8.03/1.49  
% 8.03/1.49  ------ Preprocessing
% 8.03/1.49  
% 8.03/1.49  num_of_splits:                          0
% 8.03/1.49  num_of_split_atoms:                     0
% 8.03/1.49  num_of_reused_defs:                     0
% 8.03/1.49  num_eq_ax_congr_red:                    15
% 8.03/1.49  num_of_sem_filtered_clauses:            1
% 8.03/1.49  num_of_subtypes:                        0
% 8.03/1.49  monotx_restored_types:                  0
% 8.03/1.49  sat_num_of_epr_types:                   0
% 8.03/1.49  sat_num_of_non_cyclic_types:            0
% 8.03/1.49  sat_guarded_non_collapsed_types:        0
% 8.03/1.49  num_pure_diseq_elim:                    0
% 8.03/1.49  simp_replaced_by:                       0
% 8.03/1.49  res_preprocessed:                       236
% 8.03/1.49  prep_upred:                             0
% 8.03/1.49  prep_unflattend:                        8
% 8.03/1.49  smt_new_axioms:                         0
% 8.03/1.49  pred_elim_cands:                        7
% 8.03/1.49  pred_elim:                              3
% 8.03/1.49  pred_elim_cl:                           3
% 8.03/1.49  pred_elim_cycles:                       5
% 8.03/1.49  merged_defs:                            8
% 8.03/1.49  merged_defs_ncl:                        0
% 8.03/1.49  bin_hyper_res:                          9
% 8.03/1.49  prep_cycles:                            4
% 8.03/1.49  pred_elim_time:                         0.004
% 8.03/1.49  splitting_time:                         0.
% 8.03/1.49  sem_filter_time:                        0.
% 8.03/1.49  monotx_time:                            0.001
% 8.03/1.49  subtype_inf_time:                       0.
% 8.03/1.49  
% 8.03/1.49  ------ Problem properties
% 8.03/1.49  
% 8.03/1.49  clauses:                                50
% 8.03/1.49  conjectures:                            5
% 8.03/1.49  epr:                                    8
% 8.03/1.49  horn:                                   47
% 8.03/1.49  ground:                                 10
% 8.03/1.49  unary:                                  18
% 8.03/1.49  binary:                                 11
% 8.03/1.49  lits:                                   116
% 8.03/1.49  lits_eq:                                23
% 8.03/1.49  fd_pure:                                0
% 8.03/1.49  fd_pseudo:                              0
% 8.03/1.49  fd_cond:                                5
% 8.03/1.49  fd_pseudo_cond:                         1
% 8.03/1.49  ac_symbols:                             0
% 8.03/1.49  
% 8.03/1.49  ------ Propositional Solver
% 8.03/1.49  
% 8.03/1.49  prop_solver_calls:                      31
% 8.03/1.49  prop_fast_solver_calls:                 2802
% 8.03/1.49  smt_solver_calls:                       0
% 8.03/1.49  smt_fast_solver_calls:                  0
% 8.03/1.49  prop_num_of_clauses:                    14765
% 8.03/1.49  prop_preprocess_simplified:             31105
% 8.03/1.49  prop_fo_subsumed:                       193
% 8.03/1.49  prop_solver_time:                       0.
% 8.03/1.49  smt_solver_time:                        0.
% 8.03/1.49  smt_fast_solver_time:                   0.
% 8.03/1.49  prop_fast_solver_time:                  0.
% 8.03/1.49  prop_unsat_core_time:                   0.001
% 8.03/1.49  
% 8.03/1.49  ------ QBF
% 8.03/1.49  
% 8.03/1.49  qbf_q_res:                              0
% 8.03/1.49  qbf_num_tautologies:                    0
% 8.03/1.49  qbf_prep_cycles:                        0
% 8.03/1.49  
% 8.03/1.49  ------ BMC1
% 8.03/1.49  
% 8.03/1.49  bmc1_current_bound:                     -1
% 8.03/1.49  bmc1_last_solved_bound:                 -1
% 8.03/1.49  bmc1_unsat_core_size:                   -1
% 8.03/1.49  bmc1_unsat_core_parents_size:           -1
% 8.03/1.49  bmc1_merge_next_fun:                    0
% 8.03/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.03/1.49  
% 8.03/1.49  ------ Instantiation
% 8.03/1.49  
% 8.03/1.49  inst_num_of_clauses:                    4216
% 8.03/1.49  inst_num_in_passive:                    706
% 8.03/1.49  inst_num_in_active:                     1899
% 8.03/1.49  inst_num_in_unprocessed:                1654
% 8.03/1.49  inst_num_of_loops:                      2140
% 8.03/1.49  inst_num_of_learning_restarts:          0
% 8.03/1.49  inst_num_moves_active_passive:          238
% 8.03/1.49  inst_lit_activity:                      0
% 8.03/1.49  inst_lit_activity_moves:                0
% 8.03/1.49  inst_num_tautologies:                   0
% 8.03/1.49  inst_num_prop_implied:                  0
% 8.03/1.49  inst_num_existing_simplified:           0
% 8.03/1.49  inst_num_eq_res_simplified:             0
% 8.03/1.49  inst_num_child_elim:                    0
% 8.03/1.49  inst_num_of_dismatching_blockings:      3759
% 8.03/1.49  inst_num_of_non_proper_insts:           5788
% 8.03/1.49  inst_num_of_duplicates:                 0
% 8.03/1.49  inst_inst_num_from_inst_to_res:         0
% 8.03/1.49  inst_dismatching_checking_time:         0.
% 8.03/1.49  
% 8.03/1.49  ------ Resolution
% 8.03/1.49  
% 8.03/1.49  res_num_of_clauses:                     0
% 8.03/1.49  res_num_in_passive:                     0
% 8.03/1.49  res_num_in_active:                      0
% 8.03/1.49  res_num_of_loops:                       240
% 8.03/1.49  res_forward_subset_subsumed:            293
% 8.03/1.49  res_backward_subset_subsumed:           112
% 8.03/1.49  res_forward_subsumed:                   0
% 8.03/1.49  res_backward_subsumed:                  0
% 8.03/1.49  res_forward_subsumption_resolution:     0
% 8.03/1.49  res_backward_subsumption_resolution:    0
% 8.03/1.49  res_clause_to_clause_subsumption:       2641
% 8.03/1.49  res_orphan_elimination:                 0
% 8.03/1.49  res_tautology_del:                      572
% 8.03/1.49  res_num_eq_res_simplified:              0
% 8.03/1.49  res_num_sel_changes:                    0
% 8.03/1.49  res_moves_from_active_to_pass:          0
% 8.03/1.49  
% 8.03/1.49  ------ Superposition
% 8.03/1.49  
% 8.03/1.49  sup_time_total:                         0.
% 8.03/1.49  sup_time_generating:                    0.
% 8.03/1.49  sup_time_sim_full:                      0.
% 8.03/1.49  sup_time_sim_immed:                     0.
% 8.03/1.49  
% 8.03/1.49  sup_num_of_clauses:                     704
% 8.03/1.49  sup_num_in_active:                      371
% 8.03/1.49  sup_num_in_passive:                     333
% 8.03/1.49  sup_num_of_loops:                       427
% 8.03/1.49  sup_fw_superposition:                   839
% 8.03/1.49  sup_bw_superposition:                   657
% 8.03/1.49  sup_immediate_simplified:               484
% 8.03/1.49  sup_given_eliminated:                   0
% 8.03/1.49  comparisons_done:                       0
% 8.03/1.49  comparisons_avoided:                    69
% 8.03/1.49  
% 8.03/1.49  ------ Simplifications
% 8.03/1.49  
% 8.03/1.49  
% 8.03/1.49  sim_fw_subset_subsumed:                 123
% 8.03/1.49  sim_bw_subset_subsumed:                 57
% 8.03/1.49  sim_fw_subsumed:                        115
% 8.03/1.49  sim_bw_subsumed:                        34
% 8.03/1.49  sim_fw_subsumption_res:                 0
% 8.03/1.49  sim_bw_subsumption_res:                 0
% 8.03/1.49  sim_tautology_del:                      32
% 8.03/1.49  sim_eq_tautology_del:                   91
% 8.03/1.49  sim_eq_res_simp:                        0
% 8.03/1.49  sim_fw_demodulated:                     86
% 8.03/1.49  sim_bw_demodulated:                     6
% 8.03/1.49  sim_light_normalised:                   222
% 8.03/1.49  sim_joinable_taut:                      0
% 8.03/1.49  sim_joinable_simp:                      0
% 8.03/1.49  sim_ac_normalised:                      0
% 8.03/1.49  sim_smt_subsumption:                    0
% 8.03/1.49  
%------------------------------------------------------------------------------

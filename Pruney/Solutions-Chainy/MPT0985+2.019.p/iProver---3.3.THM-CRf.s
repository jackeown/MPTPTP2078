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
% DateTime   : Thu Dec  3 12:02:23 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  242 (7214 expanded)
%              Number of clauses        :  157 (2388 expanded)
%              Number of leaves         :   23 (1379 expanded)
%              Depth                    :   25
%              Number of atoms          :  732 (37119 expanded)
%              Number of equality atoms :  360 (7447 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f61,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
        | ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
        | ~ v1_funct_1(k2_funct_1(sK5)) )
      & k2_relset_1(sK3,sK4,sK5) = sK4
      & v2_funct_1(sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
      | ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
      | ~ v1_funct_1(k2_funct_1(sK5)) )
    & k2_relset_1(sK3,sK4,sK5) = sK4
    & v2_funct_1(sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f46,f61])).

fof(f104,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f62])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f106,plain,(
    k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f62])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f101,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f80,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f105,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f18,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

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
    inference(nnf_transformation,[],[f42])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f113,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f92])).

fof(f107,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
    | ~ v1_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f62])).

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

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f82,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f103,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f84,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f100,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f112,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f93])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f108,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f19,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f24,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK2(X0,X1),X0,X1)
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK2(X0,X1),X0,X1)
      & v1_funct_1(sK2(X0,X1))
      & v1_relat_1(sK2(X0,X1))
      & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f59])).

fof(f98,plain,(
    ! [X0,X1] : v1_funct_2(sK2(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f60])).

fof(f95,plain,(
    ! [X0,X1] : m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f60])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1936,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1941,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3364,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1936,c_1941])).

cnf(c_40,negated_conjecture,
    ( k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3379,plain,
    ( k2_relat_1(sK5) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_3364,c_40])).

cnf(c_36,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1937,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3471,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3379,c_1937])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2318,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2319,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2318])).

cnf(c_3786,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3471,c_45,c_47,c_2319])).

cnf(c_1944,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4004,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3786,c_1944])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_41,negated_conjecture,
    ( v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_559,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_41])).

cnf(c_560,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k2_funct_1(sK5) = k4_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_562,plain,
    ( ~ v1_relat_1(sK5)
    | k2_funct_1(sK5) = k4_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_560,c_44])).

cnf(c_1931,plain,
    ( k2_funct_1(sK5) = k4_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_4234,plain,
    ( k2_funct_1(sK5) = k4_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4004,c_1931])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_39,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_816,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK5) != X0
    | sK3 != X1
    | sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_39])).

cnf(c_817,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_1926,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2176,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1926,c_8])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2419,plain,
    ( v1_funct_1(k2_funct_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2420,plain,
    ( v1_funct_1(k2_funct_1(sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2419])).

cnf(c_2608,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | sK4 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2176,c_45,c_47,c_2319,c_2420])).

cnf(c_2609,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2608])).

cnf(c_4364,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k4_relat_1(sK5)) != k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4234,c_2609])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_899,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_43])).

cnf(c_900,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_902,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_42])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1942,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3857,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1936,c_1942])).

cnf(c_4126,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_902,c_3857])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_545,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_41])).

cnf(c_546,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_548,plain,
    ( ~ v1_relat_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_44])).

cnf(c_1932,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_4233,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4004,c_1932])).

cnf(c_4237,plain,
    ( k2_relat_1(k4_relat_1(sK5)) = k1_relat_1(sK5) ),
    inference(light_normalisation,[status(thm)],[c_4233,c_4234])).

cnf(c_21,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_531,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_41])).

cnf(c_532,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_534,plain,
    ( ~ v1_relat_1(sK5)
    | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_44])).

cnf(c_1933,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_2333,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1933,c_44,c_42,c_532,c_2318])).

cnf(c_2975,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK5),k2_relat_1(k2_funct_1(sK5))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_1937])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2418,plain,
    ( ~ v1_funct_1(sK5)
    | v1_relat_1(k2_funct_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2422,plain,
    ( v1_funct_1(sK5) != iProver_top
    | v1_relat_1(k2_funct_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2418])).

cnf(c_3079,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK5),k2_relat_1(k2_funct_1(sK5))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2975,c_45,c_47,c_2319,c_2420,c_2422])).

cnf(c_3450,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k2_relat_1(k2_funct_1(sK5))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3379,c_3079])).

cnf(c_4360,plain,
    ( m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k2_relat_1(k4_relat_1(sK5))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4234,c_3450])).

cnf(c_5347,plain,
    ( m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4237,c_4360])).

cnf(c_5618,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4126,c_5347])).

cnf(c_37,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_923,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK5))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK4
    | k2_funct_1(sK5) != X0
    | k2_relat_1(X0) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_39])).

cnf(c_924,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | ~ v1_relat_1(k2_funct_1(sK5))
    | k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
    inference(unflattening,[status(thm)],[c_923])).

cnf(c_936,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_924,c_22])).

cnf(c_1921,plain,
    ( k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_925,plain,
    ( k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_924])).

cnf(c_2530,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | k2_relat_1(k2_funct_1(sK5)) != sK3
    | k1_relat_1(k2_funct_1(sK5)) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1921,c_45,c_47,c_925,c_2319,c_2420,c_2422])).

cnf(c_2531,plain,
    ( k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2530])).

cnf(c_2534,plain,
    ( k2_relat_1(k2_funct_1(sK5)) != sK3
    | k2_relat_1(sK5) != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2531,c_2333])).

cnf(c_3452,plain,
    ( k2_relat_1(k2_funct_1(sK5)) != sK3
    | sK4 != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3379,c_2534])).

cnf(c_3456,plain,
    ( k2_relat_1(k2_funct_1(sK5)) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3452])).

cnf(c_5061,plain,
    ( k2_relat_1(k4_relat_1(sK5)) != sK3
    | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3456,c_4234])).

cnf(c_5345,plain,
    ( k1_relat_1(sK5) != sK3
    | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4237,c_5061])).

cnf(c_5634,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5618,c_4126,c_5345])).

cnf(c_5936,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k4_relat_1(sK5)) != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4364,c_4126,c_5345,c_5618])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1954,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_15,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1948,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1953,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2941,plain,
    ( k4_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1948,c_1953])).

cnf(c_3138,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1954,c_2941])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_735,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k2_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_37])).

cnf(c_736,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_752,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_736,c_22])).

cnf(c_1929,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2165,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1929,c_7])).

cnf(c_5539,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3379,c_2165])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X1
    | sK4 != k1_xboole_0
    | sK5 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_43])).

cnf(c_762,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_1928,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_2103,plain,
    ( sK3 = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1928,c_7])).

cnf(c_1022,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2660,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_1023,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2661,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_3098,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2661])).

cnf(c_3099,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3098])).

cnf(c_3575,plain,
    ( ~ v1_xboole_0(sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1024,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3690,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_3692,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3690])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1943,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4539,plain,
    ( v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1936,c_1943])).

cnf(c_4586,plain,
    ( ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4539])).

cnf(c_5609,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sK5 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5539,c_5,c_2103,c_2660,c_3099,c_3575,c_3692,c_4586])).

cnf(c_5610,plain,
    ( sK4 != k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5609])).

cnf(c_5638,plain,
    ( sK5 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5634,c_5610])).

cnf(c_5719,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5638])).

cnf(c_5658,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5634,c_1936])).

cnf(c_5663,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5658,c_7])).

cnf(c_5722,plain,
    ( sK5 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5719,c_5663])).

cnf(c_5940,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5936,c_3138,c_5634,c_5722])).

cnf(c_32,plain,
    ( v1_funct_2(sK2(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_720,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | X2 != X1
    | sK2(X2,X3) != X0
    | k1_xboole_0 != X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_721,plain,
    ( ~ m1_subset_1(sK2(X0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK2(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_35,plain,
    ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_731,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = sK2(X0,k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_721,c_35])).

cnf(c_1938,plain,
    ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2765,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_1938])).

cnf(c_2774,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2765,c_7])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_326,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_327,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_326])).

cnf(c_619,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(resolution,[status(thm)],[c_3,c_327])).

cnf(c_620,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_622,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_644,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(resolution,[status(thm)],[c_2,c_327])).

cnf(c_645,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_647,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_2978,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2774,c_622,c_647])).

cnf(c_3861,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1942])).

cnf(c_4749,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2978,c_3861])).

cnf(c_5941,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5940,c_8,c_4749])).

cnf(c_5944,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5941,c_2978])).

cnf(c_3453,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = sK4 ),
    inference(demodulation,[status(thm)],[c_3379,c_2333])).

cnf(c_4362,plain,
    ( k1_relat_1(k4_relat_1(sK5)) = sK4 ),
    inference(demodulation,[status(thm)],[c_4234,c_3453])).

cnf(c_5647,plain,
    ( k1_relat_1(k4_relat_1(sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5634,c_4362])).

cnf(c_5729,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5722,c_5647])).

cnf(c_5749,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5729,c_3138])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5944,c_5749])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.25/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.02  
% 3.25/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.25/1.02  
% 3.25/1.02  ------  iProver source info
% 3.25/1.02  
% 3.25/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.25/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.25/1.02  git: non_committed_changes: false
% 3.25/1.02  git: last_make_outside_of_git: false
% 3.25/1.02  
% 3.25/1.02  ------ 
% 3.25/1.02  
% 3.25/1.02  ------ Input Options
% 3.25/1.02  
% 3.25/1.02  --out_options                           all
% 3.25/1.02  --tptp_safe_out                         true
% 3.25/1.02  --problem_path                          ""
% 3.25/1.02  --include_path                          ""
% 3.25/1.02  --clausifier                            res/vclausify_rel
% 3.25/1.02  --clausifier_options                    --mode clausify
% 3.25/1.02  --stdin                                 false
% 3.25/1.02  --stats_out                             all
% 3.25/1.02  
% 3.25/1.02  ------ General Options
% 3.25/1.02  
% 3.25/1.02  --fof                                   false
% 3.25/1.02  --time_out_real                         305.
% 3.25/1.02  --time_out_virtual                      -1.
% 3.25/1.02  --symbol_type_check                     false
% 3.25/1.02  --clausify_out                          false
% 3.25/1.02  --sig_cnt_out                           false
% 3.25/1.02  --trig_cnt_out                          false
% 3.25/1.02  --trig_cnt_out_tolerance                1.
% 3.25/1.02  --trig_cnt_out_sk_spl                   false
% 3.25/1.02  --abstr_cl_out                          false
% 3.25/1.02  
% 3.25/1.02  ------ Global Options
% 3.25/1.02  
% 3.25/1.02  --schedule                              default
% 3.25/1.02  --add_important_lit                     false
% 3.25/1.02  --prop_solver_per_cl                    1000
% 3.25/1.02  --min_unsat_core                        false
% 3.25/1.02  --soft_assumptions                      false
% 3.25/1.02  --soft_lemma_size                       3
% 3.25/1.02  --prop_impl_unit_size                   0
% 3.25/1.02  --prop_impl_unit                        []
% 3.25/1.02  --share_sel_clauses                     true
% 3.25/1.02  --reset_solvers                         false
% 3.25/1.02  --bc_imp_inh                            [conj_cone]
% 3.25/1.02  --conj_cone_tolerance                   3.
% 3.25/1.02  --extra_neg_conj                        none
% 3.25/1.02  --large_theory_mode                     true
% 3.25/1.02  --prolific_symb_bound                   200
% 3.25/1.02  --lt_threshold                          2000
% 3.25/1.02  --clause_weak_htbl                      true
% 3.25/1.02  --gc_record_bc_elim                     false
% 3.25/1.02  
% 3.25/1.02  ------ Preprocessing Options
% 3.25/1.02  
% 3.25/1.02  --preprocessing_flag                    true
% 3.25/1.02  --time_out_prep_mult                    0.1
% 3.25/1.02  --splitting_mode                        input
% 3.25/1.02  --splitting_grd                         true
% 3.25/1.02  --splitting_cvd                         false
% 3.25/1.02  --splitting_cvd_svl                     false
% 3.25/1.02  --splitting_nvd                         32
% 3.25/1.02  --sub_typing                            true
% 3.25/1.02  --prep_gs_sim                           true
% 3.25/1.02  --prep_unflatten                        true
% 3.25/1.02  --prep_res_sim                          true
% 3.25/1.02  --prep_upred                            true
% 3.25/1.02  --prep_sem_filter                       exhaustive
% 3.25/1.02  --prep_sem_filter_out                   false
% 3.25/1.02  --pred_elim                             true
% 3.25/1.02  --res_sim_input                         true
% 3.25/1.02  --eq_ax_congr_red                       true
% 3.25/1.02  --pure_diseq_elim                       true
% 3.25/1.02  --brand_transform                       false
% 3.25/1.02  --non_eq_to_eq                          false
% 3.25/1.02  --prep_def_merge                        true
% 3.25/1.02  --prep_def_merge_prop_impl              false
% 3.25/1.02  --prep_def_merge_mbd                    true
% 3.25/1.02  --prep_def_merge_tr_red                 false
% 3.25/1.02  --prep_def_merge_tr_cl                  false
% 3.25/1.02  --smt_preprocessing                     true
% 3.25/1.02  --smt_ac_axioms                         fast
% 3.25/1.02  --preprocessed_out                      false
% 3.25/1.02  --preprocessed_stats                    false
% 3.25/1.02  
% 3.25/1.02  ------ Abstraction refinement Options
% 3.25/1.02  
% 3.25/1.02  --abstr_ref                             []
% 3.25/1.02  --abstr_ref_prep                        false
% 3.25/1.02  --abstr_ref_until_sat                   false
% 3.25/1.02  --abstr_ref_sig_restrict                funpre
% 3.25/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/1.02  --abstr_ref_under                       []
% 3.25/1.02  
% 3.25/1.02  ------ SAT Options
% 3.25/1.02  
% 3.25/1.02  --sat_mode                              false
% 3.25/1.02  --sat_fm_restart_options                ""
% 3.25/1.02  --sat_gr_def                            false
% 3.25/1.02  --sat_epr_types                         true
% 3.25/1.02  --sat_non_cyclic_types                  false
% 3.25/1.02  --sat_finite_models                     false
% 3.25/1.02  --sat_fm_lemmas                         false
% 3.25/1.02  --sat_fm_prep                           false
% 3.25/1.02  --sat_fm_uc_incr                        true
% 3.25/1.02  --sat_out_model                         small
% 3.25/1.02  --sat_out_clauses                       false
% 3.25/1.02  
% 3.25/1.02  ------ QBF Options
% 3.25/1.02  
% 3.25/1.02  --qbf_mode                              false
% 3.25/1.02  --qbf_elim_univ                         false
% 3.25/1.02  --qbf_dom_inst                          none
% 3.25/1.02  --qbf_dom_pre_inst                      false
% 3.25/1.02  --qbf_sk_in                             false
% 3.25/1.02  --qbf_pred_elim                         true
% 3.25/1.02  --qbf_split                             512
% 3.25/1.02  
% 3.25/1.02  ------ BMC1 Options
% 3.25/1.02  
% 3.25/1.02  --bmc1_incremental                      false
% 3.25/1.02  --bmc1_axioms                           reachable_all
% 3.25/1.02  --bmc1_min_bound                        0
% 3.25/1.02  --bmc1_max_bound                        -1
% 3.25/1.02  --bmc1_max_bound_default                -1
% 3.25/1.02  --bmc1_symbol_reachability              true
% 3.25/1.02  --bmc1_property_lemmas                  false
% 3.25/1.02  --bmc1_k_induction                      false
% 3.25/1.02  --bmc1_non_equiv_states                 false
% 3.25/1.02  --bmc1_deadlock                         false
% 3.25/1.02  --bmc1_ucm                              false
% 3.25/1.02  --bmc1_add_unsat_core                   none
% 3.25/1.02  --bmc1_unsat_core_children              false
% 3.25/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/1.02  --bmc1_out_stat                         full
% 3.25/1.02  --bmc1_ground_init                      false
% 3.25/1.02  --bmc1_pre_inst_next_state              false
% 3.25/1.02  --bmc1_pre_inst_state                   false
% 3.25/1.02  --bmc1_pre_inst_reach_state             false
% 3.25/1.02  --bmc1_out_unsat_core                   false
% 3.25/1.02  --bmc1_aig_witness_out                  false
% 3.25/1.02  --bmc1_verbose                          false
% 3.25/1.02  --bmc1_dump_clauses_tptp                false
% 3.25/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.25/1.02  --bmc1_dump_file                        -
% 3.25/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.25/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.25/1.02  --bmc1_ucm_extend_mode                  1
% 3.25/1.02  --bmc1_ucm_init_mode                    2
% 3.25/1.02  --bmc1_ucm_cone_mode                    none
% 3.25/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.25/1.02  --bmc1_ucm_relax_model                  4
% 3.25/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.25/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/1.02  --bmc1_ucm_layered_model                none
% 3.25/1.02  --bmc1_ucm_max_lemma_size               10
% 3.25/1.02  
% 3.25/1.02  ------ AIG Options
% 3.25/1.02  
% 3.25/1.02  --aig_mode                              false
% 3.25/1.02  
% 3.25/1.02  ------ Instantiation Options
% 3.25/1.02  
% 3.25/1.02  --instantiation_flag                    true
% 3.25/1.02  --inst_sos_flag                         false
% 3.25/1.02  --inst_sos_phase                        true
% 3.25/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/1.02  --inst_lit_sel_side                     num_symb
% 3.25/1.02  --inst_solver_per_active                1400
% 3.25/1.02  --inst_solver_calls_frac                1.
% 3.25/1.02  --inst_passive_queue_type               priority_queues
% 3.25/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/1.02  --inst_passive_queues_freq              [25;2]
% 3.25/1.02  --inst_dismatching                      true
% 3.25/1.02  --inst_eager_unprocessed_to_passive     true
% 3.25/1.02  --inst_prop_sim_given                   true
% 3.25/1.02  --inst_prop_sim_new                     false
% 3.25/1.02  --inst_subs_new                         false
% 3.25/1.02  --inst_eq_res_simp                      false
% 3.25/1.02  --inst_subs_given                       false
% 3.25/1.02  --inst_orphan_elimination               true
% 3.25/1.02  --inst_learning_loop_flag               true
% 3.25/1.02  --inst_learning_start                   3000
% 3.25/1.02  --inst_learning_factor                  2
% 3.25/1.02  --inst_start_prop_sim_after_learn       3
% 3.25/1.02  --inst_sel_renew                        solver
% 3.25/1.02  --inst_lit_activity_flag                true
% 3.25/1.02  --inst_restr_to_given                   false
% 3.25/1.02  --inst_activity_threshold               500
% 3.25/1.02  --inst_out_proof                        true
% 3.25/1.02  
% 3.25/1.02  ------ Resolution Options
% 3.25/1.02  
% 3.25/1.02  --resolution_flag                       true
% 3.25/1.02  --res_lit_sel                           adaptive
% 3.25/1.02  --res_lit_sel_side                      none
% 3.25/1.02  --res_ordering                          kbo
% 3.25/1.02  --res_to_prop_solver                    active
% 3.25/1.02  --res_prop_simpl_new                    false
% 3.25/1.02  --res_prop_simpl_given                  true
% 3.25/1.02  --res_passive_queue_type                priority_queues
% 3.25/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/1.02  --res_passive_queues_freq               [15;5]
% 3.25/1.02  --res_forward_subs                      full
% 3.25/1.02  --res_backward_subs                     full
% 3.25/1.02  --res_forward_subs_resolution           true
% 3.25/1.02  --res_backward_subs_resolution          true
% 3.25/1.02  --res_orphan_elimination                true
% 3.25/1.02  --res_time_limit                        2.
% 3.25/1.02  --res_out_proof                         true
% 3.25/1.02  
% 3.25/1.02  ------ Superposition Options
% 3.25/1.02  
% 3.25/1.02  --superposition_flag                    true
% 3.25/1.02  --sup_passive_queue_type                priority_queues
% 3.25/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.25/1.02  --demod_completeness_check              fast
% 3.25/1.02  --demod_use_ground                      true
% 3.25/1.02  --sup_to_prop_solver                    passive
% 3.25/1.02  --sup_prop_simpl_new                    true
% 3.25/1.02  --sup_prop_simpl_given                  true
% 3.25/1.02  --sup_fun_splitting                     false
% 3.25/1.02  --sup_smt_interval                      50000
% 3.25/1.02  
% 3.25/1.02  ------ Superposition Simplification Setup
% 3.25/1.02  
% 3.25/1.02  --sup_indices_passive                   []
% 3.25/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.02  --sup_full_bw                           [BwDemod]
% 3.25/1.02  --sup_immed_triv                        [TrivRules]
% 3.25/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.02  --sup_immed_bw_main                     []
% 3.25/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/1.02  
% 3.25/1.02  ------ Combination Options
% 3.25/1.02  
% 3.25/1.02  --comb_res_mult                         3
% 3.25/1.02  --comb_sup_mult                         2
% 3.25/1.02  --comb_inst_mult                        10
% 3.25/1.02  
% 3.25/1.02  ------ Debug Options
% 3.25/1.02  
% 3.25/1.02  --dbg_backtrace                         false
% 3.25/1.02  --dbg_dump_prop_clauses                 false
% 3.25/1.02  --dbg_dump_prop_clauses_file            -
% 3.25/1.02  --dbg_out_stat                          false
% 3.25/1.02  ------ Parsing...
% 3.25/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.25/1.02  
% 3.25/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.25/1.02  
% 3.25/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.25/1.02  
% 3.25/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.25/1.02  ------ Proving...
% 3.25/1.02  ------ Problem Properties 
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  clauses                                 48
% 3.25/1.02  conjectures                             3
% 3.25/1.02  EPR                                     7
% 3.25/1.02  Horn                                    39
% 3.25/1.02  unary                                   10
% 3.25/1.02  binary                                  20
% 3.25/1.02  lits                                    117
% 3.25/1.02  lits eq                                 43
% 3.25/1.02  fd_pure                                 0
% 3.25/1.02  fd_pseudo                               0
% 3.25/1.02  fd_cond                                 4
% 3.25/1.02  fd_pseudo_cond                          0
% 3.25/1.02  AC symbols                              0
% 3.25/1.02  
% 3.25/1.02  ------ Schedule dynamic 5 is on 
% 3.25/1.02  
% 3.25/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  ------ 
% 3.25/1.02  Current options:
% 3.25/1.02  ------ 
% 3.25/1.02  
% 3.25/1.02  ------ Input Options
% 3.25/1.02  
% 3.25/1.02  --out_options                           all
% 3.25/1.02  --tptp_safe_out                         true
% 3.25/1.02  --problem_path                          ""
% 3.25/1.02  --include_path                          ""
% 3.25/1.02  --clausifier                            res/vclausify_rel
% 3.25/1.02  --clausifier_options                    --mode clausify
% 3.25/1.02  --stdin                                 false
% 3.25/1.02  --stats_out                             all
% 3.25/1.02  
% 3.25/1.02  ------ General Options
% 3.25/1.02  
% 3.25/1.02  --fof                                   false
% 3.25/1.02  --time_out_real                         305.
% 3.25/1.02  --time_out_virtual                      -1.
% 3.25/1.02  --symbol_type_check                     false
% 3.25/1.02  --clausify_out                          false
% 3.25/1.02  --sig_cnt_out                           false
% 3.25/1.02  --trig_cnt_out                          false
% 3.25/1.02  --trig_cnt_out_tolerance                1.
% 3.25/1.02  --trig_cnt_out_sk_spl                   false
% 3.25/1.02  --abstr_cl_out                          false
% 3.25/1.02  
% 3.25/1.02  ------ Global Options
% 3.25/1.02  
% 3.25/1.02  --schedule                              default
% 3.25/1.02  --add_important_lit                     false
% 3.25/1.02  --prop_solver_per_cl                    1000
% 3.25/1.02  --min_unsat_core                        false
% 3.25/1.02  --soft_assumptions                      false
% 3.25/1.02  --soft_lemma_size                       3
% 3.25/1.02  --prop_impl_unit_size                   0
% 3.25/1.02  --prop_impl_unit                        []
% 3.25/1.02  --share_sel_clauses                     true
% 3.25/1.02  --reset_solvers                         false
% 3.25/1.02  --bc_imp_inh                            [conj_cone]
% 3.25/1.02  --conj_cone_tolerance                   3.
% 3.25/1.02  --extra_neg_conj                        none
% 3.25/1.02  --large_theory_mode                     true
% 3.25/1.02  --prolific_symb_bound                   200
% 3.25/1.02  --lt_threshold                          2000
% 3.25/1.02  --clause_weak_htbl                      true
% 3.25/1.02  --gc_record_bc_elim                     false
% 3.25/1.02  
% 3.25/1.02  ------ Preprocessing Options
% 3.25/1.02  
% 3.25/1.02  --preprocessing_flag                    true
% 3.25/1.02  --time_out_prep_mult                    0.1
% 3.25/1.02  --splitting_mode                        input
% 3.25/1.02  --splitting_grd                         true
% 3.25/1.02  --splitting_cvd                         false
% 3.25/1.02  --splitting_cvd_svl                     false
% 3.25/1.02  --splitting_nvd                         32
% 3.25/1.02  --sub_typing                            true
% 3.25/1.02  --prep_gs_sim                           true
% 3.25/1.02  --prep_unflatten                        true
% 3.25/1.02  --prep_res_sim                          true
% 3.25/1.02  --prep_upred                            true
% 3.25/1.02  --prep_sem_filter                       exhaustive
% 3.25/1.02  --prep_sem_filter_out                   false
% 3.25/1.02  --pred_elim                             true
% 3.25/1.02  --res_sim_input                         true
% 3.25/1.02  --eq_ax_congr_red                       true
% 3.25/1.02  --pure_diseq_elim                       true
% 3.25/1.02  --brand_transform                       false
% 3.25/1.02  --non_eq_to_eq                          false
% 3.25/1.02  --prep_def_merge                        true
% 3.25/1.02  --prep_def_merge_prop_impl              false
% 3.25/1.02  --prep_def_merge_mbd                    true
% 3.25/1.02  --prep_def_merge_tr_red                 false
% 3.25/1.02  --prep_def_merge_tr_cl                  false
% 3.25/1.02  --smt_preprocessing                     true
% 3.25/1.02  --smt_ac_axioms                         fast
% 3.25/1.02  --preprocessed_out                      false
% 3.25/1.02  --preprocessed_stats                    false
% 3.25/1.02  
% 3.25/1.02  ------ Abstraction refinement Options
% 3.25/1.02  
% 3.25/1.02  --abstr_ref                             []
% 3.25/1.02  --abstr_ref_prep                        false
% 3.25/1.02  --abstr_ref_until_sat                   false
% 3.25/1.02  --abstr_ref_sig_restrict                funpre
% 3.25/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/1.02  --abstr_ref_under                       []
% 3.25/1.02  
% 3.25/1.02  ------ SAT Options
% 3.25/1.02  
% 3.25/1.02  --sat_mode                              false
% 3.25/1.02  --sat_fm_restart_options                ""
% 3.25/1.02  --sat_gr_def                            false
% 3.25/1.02  --sat_epr_types                         true
% 3.25/1.02  --sat_non_cyclic_types                  false
% 3.25/1.02  --sat_finite_models                     false
% 3.25/1.02  --sat_fm_lemmas                         false
% 3.25/1.02  --sat_fm_prep                           false
% 3.25/1.02  --sat_fm_uc_incr                        true
% 3.25/1.02  --sat_out_model                         small
% 3.25/1.02  --sat_out_clauses                       false
% 3.25/1.02  
% 3.25/1.02  ------ QBF Options
% 3.25/1.02  
% 3.25/1.02  --qbf_mode                              false
% 3.25/1.02  --qbf_elim_univ                         false
% 3.25/1.02  --qbf_dom_inst                          none
% 3.25/1.02  --qbf_dom_pre_inst                      false
% 3.25/1.02  --qbf_sk_in                             false
% 3.25/1.02  --qbf_pred_elim                         true
% 3.25/1.02  --qbf_split                             512
% 3.25/1.02  
% 3.25/1.02  ------ BMC1 Options
% 3.25/1.02  
% 3.25/1.02  --bmc1_incremental                      false
% 3.25/1.02  --bmc1_axioms                           reachable_all
% 3.25/1.02  --bmc1_min_bound                        0
% 3.25/1.02  --bmc1_max_bound                        -1
% 3.25/1.02  --bmc1_max_bound_default                -1
% 3.25/1.02  --bmc1_symbol_reachability              true
% 3.25/1.02  --bmc1_property_lemmas                  false
% 3.25/1.02  --bmc1_k_induction                      false
% 3.25/1.02  --bmc1_non_equiv_states                 false
% 3.25/1.02  --bmc1_deadlock                         false
% 3.25/1.02  --bmc1_ucm                              false
% 3.25/1.02  --bmc1_add_unsat_core                   none
% 3.25/1.02  --bmc1_unsat_core_children              false
% 3.25/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/1.02  --bmc1_out_stat                         full
% 3.25/1.02  --bmc1_ground_init                      false
% 3.25/1.02  --bmc1_pre_inst_next_state              false
% 3.25/1.02  --bmc1_pre_inst_state                   false
% 3.25/1.02  --bmc1_pre_inst_reach_state             false
% 3.25/1.02  --bmc1_out_unsat_core                   false
% 3.25/1.02  --bmc1_aig_witness_out                  false
% 3.25/1.02  --bmc1_verbose                          false
% 3.25/1.02  --bmc1_dump_clauses_tptp                false
% 3.25/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.25/1.02  --bmc1_dump_file                        -
% 3.25/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.25/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.25/1.02  --bmc1_ucm_extend_mode                  1
% 3.25/1.02  --bmc1_ucm_init_mode                    2
% 3.25/1.02  --bmc1_ucm_cone_mode                    none
% 3.25/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.25/1.02  --bmc1_ucm_relax_model                  4
% 3.25/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.25/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/1.02  --bmc1_ucm_layered_model                none
% 3.25/1.02  --bmc1_ucm_max_lemma_size               10
% 3.25/1.02  
% 3.25/1.02  ------ AIG Options
% 3.25/1.02  
% 3.25/1.02  --aig_mode                              false
% 3.25/1.02  
% 3.25/1.02  ------ Instantiation Options
% 3.25/1.02  
% 3.25/1.02  --instantiation_flag                    true
% 3.25/1.02  --inst_sos_flag                         false
% 3.25/1.02  --inst_sos_phase                        true
% 3.25/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/1.02  --inst_lit_sel_side                     none
% 3.25/1.02  --inst_solver_per_active                1400
% 3.25/1.02  --inst_solver_calls_frac                1.
% 3.25/1.02  --inst_passive_queue_type               priority_queues
% 3.25/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/1.02  --inst_passive_queues_freq              [25;2]
% 3.25/1.02  --inst_dismatching                      true
% 3.25/1.02  --inst_eager_unprocessed_to_passive     true
% 3.25/1.02  --inst_prop_sim_given                   true
% 3.25/1.02  --inst_prop_sim_new                     false
% 3.25/1.02  --inst_subs_new                         false
% 3.25/1.02  --inst_eq_res_simp                      false
% 3.25/1.02  --inst_subs_given                       false
% 3.25/1.02  --inst_orphan_elimination               true
% 3.25/1.02  --inst_learning_loop_flag               true
% 3.25/1.02  --inst_learning_start                   3000
% 3.25/1.02  --inst_learning_factor                  2
% 3.25/1.02  --inst_start_prop_sim_after_learn       3
% 3.25/1.02  --inst_sel_renew                        solver
% 3.25/1.02  --inst_lit_activity_flag                true
% 3.25/1.02  --inst_restr_to_given                   false
% 3.25/1.02  --inst_activity_threshold               500
% 3.25/1.02  --inst_out_proof                        true
% 3.25/1.02  
% 3.25/1.02  ------ Resolution Options
% 3.25/1.02  
% 3.25/1.02  --resolution_flag                       false
% 3.25/1.02  --res_lit_sel                           adaptive
% 3.25/1.02  --res_lit_sel_side                      none
% 3.25/1.02  --res_ordering                          kbo
% 3.25/1.02  --res_to_prop_solver                    active
% 3.25/1.02  --res_prop_simpl_new                    false
% 3.25/1.02  --res_prop_simpl_given                  true
% 3.25/1.02  --res_passive_queue_type                priority_queues
% 3.25/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/1.02  --res_passive_queues_freq               [15;5]
% 3.25/1.02  --res_forward_subs                      full
% 3.25/1.02  --res_backward_subs                     full
% 3.25/1.02  --res_forward_subs_resolution           true
% 3.25/1.02  --res_backward_subs_resolution          true
% 3.25/1.02  --res_orphan_elimination                true
% 3.25/1.02  --res_time_limit                        2.
% 3.25/1.02  --res_out_proof                         true
% 3.25/1.02  
% 3.25/1.02  ------ Superposition Options
% 3.25/1.02  
% 3.25/1.02  --superposition_flag                    true
% 3.25/1.02  --sup_passive_queue_type                priority_queues
% 3.25/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.25/1.02  --demod_completeness_check              fast
% 3.25/1.02  --demod_use_ground                      true
% 3.25/1.02  --sup_to_prop_solver                    passive
% 3.25/1.02  --sup_prop_simpl_new                    true
% 3.25/1.02  --sup_prop_simpl_given                  true
% 3.25/1.02  --sup_fun_splitting                     false
% 3.25/1.02  --sup_smt_interval                      50000
% 3.25/1.02  
% 3.25/1.02  ------ Superposition Simplification Setup
% 3.25/1.02  
% 3.25/1.02  --sup_indices_passive                   []
% 3.25/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.02  --sup_full_bw                           [BwDemod]
% 3.25/1.02  --sup_immed_triv                        [TrivRules]
% 3.25/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.02  --sup_immed_bw_main                     []
% 3.25/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/1.02  
% 3.25/1.02  ------ Combination Options
% 3.25/1.02  
% 3.25/1.02  --comb_res_mult                         3
% 3.25/1.02  --comb_sup_mult                         2
% 3.25/1.02  --comb_inst_mult                        10
% 3.25/1.02  
% 3.25/1.02  ------ Debug Options
% 3.25/1.02  
% 3.25/1.02  --dbg_backtrace                         false
% 3.25/1.02  --dbg_dump_prop_clauses                 false
% 3.25/1.02  --dbg_dump_prop_clauses_file            -
% 3.25/1.02  --dbg_out_stat                          false
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  ------ Proving...
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  % SZS status Theorem for theBenchmark.p
% 3.25/1.02  
% 3.25/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.25/1.02  
% 3.25/1.02  fof(f21,conjecture,(
% 3.25/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f22,negated_conjecture,(
% 3.25/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.25/1.02    inference(negated_conjecture,[],[f21])).
% 3.25/1.02  
% 3.25/1.02  fof(f45,plain,(
% 3.25/1.02    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.25/1.02    inference(ennf_transformation,[],[f22])).
% 3.25/1.02  
% 3.25/1.02  fof(f46,plain,(
% 3.25/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.25/1.02    inference(flattening,[],[f45])).
% 3.25/1.02  
% 3.25/1.02  fof(f61,plain,(
% 3.25/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))) & k2_relset_1(sK3,sK4,sK5) = sK4 & v2_funct_1(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.25/1.02    introduced(choice_axiom,[])).
% 3.25/1.02  
% 3.25/1.02  fof(f62,plain,(
% 3.25/1.02    (~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))) & k2_relset_1(sK3,sK4,sK5) = sK4 & v2_funct_1(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.25/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f46,f61])).
% 3.25/1.02  
% 3.25/1.02  fof(f104,plain,(
% 3.25/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.25/1.02    inference(cnf_transformation,[],[f62])).
% 3.25/1.02  
% 3.25/1.02  fof(f17,axiom,(
% 3.25/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f40,plain,(
% 3.25/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(ennf_transformation,[],[f17])).
% 3.25/1.02  
% 3.25/1.02  fof(f88,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f40])).
% 3.25/1.02  
% 3.25/1.02  fof(f106,plain,(
% 3.25/1.02    k2_relset_1(sK3,sK4,sK5) = sK4),
% 3.25/1.02    inference(cnf_transformation,[],[f62])).
% 3.25/1.02  
% 3.25/1.02  fof(f20,axiom,(
% 3.25/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f43,plain,(
% 3.25/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.25/1.02    inference(ennf_transformation,[],[f20])).
% 3.25/1.02  
% 3.25/1.02  fof(f44,plain,(
% 3.25/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.25/1.02    inference(flattening,[],[f43])).
% 3.25/1.02  
% 3.25/1.02  fof(f101,plain,(
% 3.25/1.02    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f44])).
% 3.25/1.02  
% 3.25/1.02  fof(f102,plain,(
% 3.25/1.02    v1_funct_1(sK5)),
% 3.25/1.02    inference(cnf_transformation,[],[f62])).
% 3.25/1.02  
% 3.25/1.02  fof(f14,axiom,(
% 3.25/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f37,plain,(
% 3.25/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(ennf_transformation,[],[f14])).
% 3.25/1.02  
% 3.25/1.02  fof(f85,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f37])).
% 3.25/1.02  
% 3.25/1.02  fof(f11,axiom,(
% 3.25/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f31,plain,(
% 3.25/1.02    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.25/1.02    inference(ennf_transformation,[],[f11])).
% 3.25/1.02  
% 3.25/1.02  fof(f32,plain,(
% 3.25/1.02    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.25/1.02    inference(flattening,[],[f31])).
% 3.25/1.02  
% 3.25/1.02  fof(f80,plain,(
% 3.25/1.02    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f32])).
% 3.25/1.02  
% 3.25/1.02  fof(f105,plain,(
% 3.25/1.02    v2_funct_1(sK5)),
% 3.25/1.02    inference(cnf_transformation,[],[f62])).
% 3.25/1.02  
% 3.25/1.02  fof(f18,axiom,(
% 3.25/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f41,plain,(
% 3.25/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(ennf_transformation,[],[f18])).
% 3.25/1.02  
% 3.25/1.02  fof(f42,plain,(
% 3.25/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(flattening,[],[f41])).
% 3.25/1.02  
% 3.25/1.02  fof(f58,plain,(
% 3.25/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(nnf_transformation,[],[f42])).
% 3.25/1.02  
% 3.25/1.02  fof(f92,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f58])).
% 3.25/1.02  
% 3.25/1.02  fof(f113,plain,(
% 3.25/1.02    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.25/1.02    inference(equality_resolution,[],[f92])).
% 3.25/1.02  
% 3.25/1.02  fof(f107,plain,(
% 3.25/1.02    ~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))),
% 3.25/1.02    inference(cnf_transformation,[],[f62])).
% 3.25/1.02  
% 3.25/1.02  fof(f5,axiom,(
% 3.25/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f55,plain,(
% 3.25/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.25/1.02    inference(nnf_transformation,[],[f5])).
% 3.25/1.02  
% 3.25/1.02  fof(f56,plain,(
% 3.25/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.25/1.02    inference(flattening,[],[f55])).
% 3.25/1.02  
% 3.25/1.02  fof(f71,plain,(
% 3.25/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.25/1.02    inference(cnf_transformation,[],[f56])).
% 3.25/1.02  
% 3.25/1.02  fof(f109,plain,(
% 3.25/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.25/1.02    inference(equality_resolution,[],[f71])).
% 3.25/1.02  
% 3.25/1.02  fof(f12,axiom,(
% 3.25/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f33,plain,(
% 3.25/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.25/1.02    inference(ennf_transformation,[],[f12])).
% 3.25/1.02  
% 3.25/1.02  fof(f34,plain,(
% 3.25/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.25/1.02    inference(flattening,[],[f33])).
% 3.25/1.02  
% 3.25/1.02  fof(f82,plain,(
% 3.25/1.02    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f34])).
% 3.25/1.02  
% 3.25/1.02  fof(f89,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f58])).
% 3.25/1.02  
% 3.25/1.02  fof(f103,plain,(
% 3.25/1.02    v1_funct_2(sK5,sK3,sK4)),
% 3.25/1.02    inference(cnf_transformation,[],[f62])).
% 3.25/1.02  
% 3.25/1.02  fof(f16,axiom,(
% 3.25/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f39,plain,(
% 3.25/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(ennf_transformation,[],[f16])).
% 3.25/1.02  
% 3.25/1.02  fof(f87,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f39])).
% 3.25/1.02  
% 3.25/1.02  fof(f13,axiom,(
% 3.25/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f35,plain,(
% 3.25/1.02    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.25/1.02    inference(ennf_transformation,[],[f13])).
% 3.25/1.02  
% 3.25/1.02  fof(f36,plain,(
% 3.25/1.02    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.25/1.02    inference(flattening,[],[f35])).
% 3.25/1.02  
% 3.25/1.02  fof(f84,plain,(
% 3.25/1.02    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f36])).
% 3.25/1.02  
% 3.25/1.02  fof(f83,plain,(
% 3.25/1.02    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f36])).
% 3.25/1.02  
% 3.25/1.02  fof(f81,plain,(
% 3.25/1.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f34])).
% 3.25/1.02  
% 3.25/1.02  fof(f100,plain,(
% 3.25/1.02    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f44])).
% 3.25/1.02  
% 3.25/1.02  fof(f3,axiom,(
% 3.25/1.02    v1_xboole_0(k1_xboole_0)),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f68,plain,(
% 3.25/1.02    v1_xboole_0(k1_xboole_0)),
% 3.25/1.02    inference(cnf_transformation,[],[f3])).
% 3.25/1.02  
% 3.25/1.02  fof(f9,axiom,(
% 3.25/1.02    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f29,plain,(
% 3.25/1.02    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 3.25/1.02    inference(ennf_transformation,[],[f9])).
% 3.25/1.02  
% 3.25/1.02  fof(f77,plain,(
% 3.25/1.02    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f29])).
% 3.25/1.02  
% 3.25/1.02  fof(f4,axiom,(
% 3.25/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f26,plain,(
% 3.25/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.25/1.02    inference(ennf_transformation,[],[f4])).
% 3.25/1.02  
% 3.25/1.02  fof(f69,plain,(
% 3.25/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f26])).
% 3.25/1.02  
% 3.25/1.02  fof(f93,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f58])).
% 3.25/1.02  
% 3.25/1.02  fof(f112,plain,(
% 3.25/1.02    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.25/1.02    inference(equality_resolution,[],[f93])).
% 3.25/1.02  
% 3.25/1.02  fof(f72,plain,(
% 3.25/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.25/1.02    inference(cnf_transformation,[],[f56])).
% 3.25/1.02  
% 3.25/1.02  fof(f108,plain,(
% 3.25/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.25/1.02    inference(equality_resolution,[],[f72])).
% 3.25/1.02  
% 3.25/1.02  fof(f15,axiom,(
% 3.25/1.02    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f38,plain,(
% 3.25/1.02    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.25/1.02    inference(ennf_transformation,[],[f15])).
% 3.25/1.02  
% 3.25/1.02  fof(f86,plain,(
% 3.25/1.02    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f38])).
% 3.25/1.02  
% 3.25/1.02  fof(f19,axiom,(
% 3.25/1.02    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f23,plain,(
% 3.25/1.02    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(pure_predicate_removal,[],[f19])).
% 3.25/1.02  
% 3.25/1.02  fof(f24,plain,(
% 3.25/1.02    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(pure_predicate_removal,[],[f23])).
% 3.25/1.02  
% 3.25/1.02  fof(f59,plain,(
% 3.25/1.02    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK2(X0,X1),X0,X1) & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.25/1.02    introduced(choice_axiom,[])).
% 3.25/1.02  
% 3.25/1.02  fof(f60,plain,(
% 3.25/1.02    ! [X0,X1] : (v1_funct_2(sK2(X0,X1),X0,X1) & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f59])).
% 3.25/1.02  
% 3.25/1.02  fof(f98,plain,(
% 3.25/1.02    ( ! [X0,X1] : (v1_funct_2(sK2(X0,X1),X0,X1)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f60])).
% 3.25/1.02  
% 3.25/1.02  fof(f95,plain,(
% 3.25/1.02    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.02    inference(cnf_transformation,[],[f60])).
% 3.25/1.02  
% 3.25/1.02  fof(f2,axiom,(
% 3.25/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f25,plain,(
% 3.25/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.25/1.02    inference(ennf_transformation,[],[f2])).
% 3.25/1.02  
% 3.25/1.02  fof(f51,plain,(
% 3.25/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.25/1.02    inference(nnf_transformation,[],[f25])).
% 3.25/1.02  
% 3.25/1.02  fof(f52,plain,(
% 3.25/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.25/1.02    inference(rectify,[],[f51])).
% 3.25/1.02  
% 3.25/1.02  fof(f53,plain,(
% 3.25/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.25/1.02    introduced(choice_axiom,[])).
% 3.25/1.02  
% 3.25/1.02  fof(f54,plain,(
% 3.25/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.25/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).
% 3.25/1.02  
% 3.25/1.02  fof(f66,plain,(
% 3.25/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f54])).
% 3.25/1.02  
% 3.25/1.02  fof(f7,axiom,(
% 3.25/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.25/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.02  
% 3.25/1.02  fof(f57,plain,(
% 3.25/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.25/1.02    inference(nnf_transformation,[],[f7])).
% 3.25/1.02  
% 3.25/1.02  fof(f75,plain,(
% 3.25/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f57])).
% 3.25/1.02  
% 3.25/1.02  fof(f67,plain,(
% 3.25/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 3.25/1.02    inference(cnf_transformation,[],[f54])).
% 3.25/1.02  
% 3.25/1.02  cnf(c_42,negated_conjecture,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.25/1.02      inference(cnf_transformation,[],[f104]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1936,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_25,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f88]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1941,plain,
% 3.25/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.25/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3364,plain,
% 3.25/1.02      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_1936,c_1941]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_40,negated_conjecture,
% 3.25/1.02      ( k2_relset_1(sK3,sK4,sK5) = sK4 ),
% 3.25/1.02      inference(cnf_transformation,[],[f106]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3379,plain,
% 3.25/1.02      ( k2_relat_1(sK5) = sK4 ),
% 3.25/1.02      inference(light_normalisation,[status(thm)],[c_3364,c_40]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_36,plain,
% 3.25/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.25/1.02      | ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f101]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1937,plain,
% 3.25/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.25/1.02      | v1_funct_1(X0) != iProver_top
% 3.25/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3471,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top
% 3.25/1.02      | v1_funct_1(sK5) != iProver_top
% 3.25/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_3379,c_1937]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_44,negated_conjecture,
% 3.25/1.02      ( v1_funct_1(sK5) ),
% 3.25/1.02      inference(cnf_transformation,[],[f102]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_45,plain,
% 3.25/1.02      ( v1_funct_1(sK5) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_47,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_22,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | v1_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2318,plain,
% 3.25/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/1.02      | v1_relat_1(sK5) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_22]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2319,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.25/1.02      | v1_relat_1(sK5) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_2318]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3786,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_3471,c_45,c_47,c_2319]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1944,plain,
% 3.25/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.25/1.02      | v1_relat_1(X0) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4004,plain,
% 3.25/1.02      ( v1_relat_1(sK5) = iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_3786,c_1944]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_17,plain,
% 3.25/1.02      ( ~ v2_funct_1(X0)
% 3.25/1.02      | ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_41,negated_conjecture,
% 3.25/1.02      ( v2_funct_1(sK5) ),
% 3.25/1.02      inference(cnf_transformation,[],[f105]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_559,plain,
% 3.25/1.02      ( ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.25/1.02      | sK5 != X0 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_41]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_560,plain,
% 3.25/1.02      ( ~ v1_funct_1(sK5)
% 3.25/1.02      | ~ v1_relat_1(sK5)
% 3.25/1.02      | k2_funct_1(sK5) = k4_relat_1(sK5) ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_559]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_562,plain,
% 3.25/1.02      ( ~ v1_relat_1(sK5) | k2_funct_1(sK5) = k4_relat_1(sK5) ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_560,c_44]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1931,plain,
% 3.25/1.02      ( k2_funct_1(sK5) = k4_relat_1(sK5)
% 3.25/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4234,plain,
% 3.25/1.02      ( k2_funct_1(sK5) = k4_relat_1(sK5) ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_4004,c_1931]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_28,plain,
% 3.25/1.02      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.25/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.25/1.02      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.25/1.02      inference(cnf_transformation,[],[f113]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_39,negated_conjecture,
% 3.25/1.02      ( ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
% 3.25/1.02      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.25/1.02      | ~ v1_funct_1(k2_funct_1(sK5)) ),
% 3.25/1.02      inference(cnf_transformation,[],[f107]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_816,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.25/1.02      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.25/1.02      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.25/1.02      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.25/1.02      | k2_funct_1(sK5) != X0
% 3.25/1.02      | sK3 != X1
% 3.25/1.02      | sK4 != k1_xboole_0 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_28,c_39]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_817,plain,
% 3.25/1.02      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.25/1.02      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.25/1.02      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.25/1.02      | k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
% 3.25/1.02      | sK4 != k1_xboole_0 ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_816]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1926,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 3.25/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_8,plain,
% 3.25/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.25/1.02      inference(cnf_transformation,[],[f109]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2176,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.25/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_1926,c_8]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_18,plain,
% 3.25/1.02      ( ~ v1_funct_1(X0)
% 3.25/1.02      | v1_funct_1(k2_funct_1(X0))
% 3.25/1.02      | ~ v1_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2419,plain,
% 3.25/1.02      ( v1_funct_1(k2_funct_1(sK5))
% 3.25/1.02      | ~ v1_funct_1(sK5)
% 3.25/1.02      | ~ v1_relat_1(sK5) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_18]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2420,plain,
% 3.25/1.02      ( v1_funct_1(k2_funct_1(sK5)) = iProver_top
% 3.25/1.02      | v1_funct_1(sK5) != iProver_top
% 3.25/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_2419]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2608,plain,
% 3.25/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0 ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_2176,c_45,c_47,c_2319,c_2420]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2609,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(renaming,[status(thm)],[c_2608]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4364,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,sK3,k4_relat_1(sK5)) != k1_xboole_0
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.25/1.02      | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_4234,c_2609]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_31,plain,
% 3.25/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.25/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.25/1.02      | k1_xboole_0 = X2 ),
% 3.25/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_43,negated_conjecture,
% 3.25/1.02      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.25/1.02      inference(cnf_transformation,[],[f103]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_899,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.25/1.02      | sK3 != X1
% 3.25/1.02      | sK4 != X2
% 3.25/1.02      | sK5 != X0
% 3.25/1.02      | k1_xboole_0 = X2 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_31,c_43]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_900,plain,
% 3.25/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.25/1.02      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.25/1.02      | k1_xboole_0 = sK4 ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_899]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_902,plain,
% 3.25/1.02      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_900,c_42]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_24,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1942,plain,
% 3.25/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.25/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3857,plain,
% 3.25/1.02      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_1936,c_1942]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4126,plain,
% 3.25/1.02      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_902,c_3857]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_20,plain,
% 3.25/1.02      ( ~ v2_funct_1(X0)
% 3.25/1.02      | ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_545,plain,
% 3.25/1.02      ( ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.25/1.02      | sK5 != X0 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_41]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_546,plain,
% 3.25/1.02      ( ~ v1_funct_1(sK5)
% 3.25/1.02      | ~ v1_relat_1(sK5)
% 3.25/1.02      | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_545]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_548,plain,
% 3.25/1.02      ( ~ v1_relat_1(sK5)
% 3.25/1.02      | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_546,c_44]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1932,plain,
% 3.25/1.02      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
% 3.25/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4233,plain,
% 3.25/1.02      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_4004,c_1932]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4237,plain,
% 3.25/1.02      ( k2_relat_1(k4_relat_1(sK5)) = k1_relat_1(sK5) ),
% 3.25/1.02      inference(light_normalisation,[status(thm)],[c_4233,c_4234]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_21,plain,
% 3.25/1.02      ( ~ v2_funct_1(X0)
% 3.25/1.02      | ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_531,plain,
% 3.25/1.02      ( ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.25/1.02      | sK5 != X0 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_41]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_532,plain,
% 3.25/1.02      ( ~ v1_funct_1(sK5)
% 3.25/1.02      | ~ v1_relat_1(sK5)
% 3.25/1.02      | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_531]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_534,plain,
% 3.25/1.02      ( ~ v1_relat_1(sK5)
% 3.25/1.02      | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_532,c_44]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1933,plain,
% 3.25/1.02      ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
% 3.25/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2333,plain,
% 3.25/1.02      ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_1933,c_44,c_42,c_532,c_2318]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2975,plain,
% 3.25/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK5),k2_relat_1(k2_funct_1(sK5))))) = iProver_top
% 3.25/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 3.25/1.02      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_2333,c_1937]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_19,plain,
% 3.25/1.02      ( ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | v1_relat_1(k2_funct_1(X0)) ),
% 3.25/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2418,plain,
% 3.25/1.02      ( ~ v1_funct_1(sK5)
% 3.25/1.02      | v1_relat_1(k2_funct_1(sK5))
% 3.25/1.02      | ~ v1_relat_1(sK5) ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_19]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2422,plain,
% 3.25/1.02      ( v1_funct_1(sK5) != iProver_top
% 3.25/1.02      | v1_relat_1(k2_funct_1(sK5)) = iProver_top
% 3.25/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_2418]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3079,plain,
% 3.25/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK5),k2_relat_1(k2_funct_1(sK5))))) = iProver_top ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_2975,c_45,c_47,c_2319,c_2420,c_2422]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3450,plain,
% 3.25/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k2_relat_1(k2_funct_1(sK5))))) = iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_3379,c_3079]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4360,plain,
% 3.25/1.02      ( m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k2_relat_1(k4_relat_1(sK5))))) = iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_4234,c_3450]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5347,plain,
% 3.25/1.02      ( m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_4237,c_4360]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5618,plain,
% 3.25/1.02      ( sK4 = k1_xboole_0
% 3.25/1.02      | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_4126,c_5347]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_37,plain,
% 3.25/1.02      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.25/1.02      | ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_relat_1(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f100]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_923,plain,
% 3.25/1.02      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.25/1.02      | ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | k1_relat_1(X0) != sK4
% 3.25/1.02      | k2_funct_1(sK5) != X0
% 3.25/1.02      | k2_relat_1(X0) != sK3 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_37,c_39]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_924,plain,
% 3.25/1.02      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.25/1.02      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.25/1.02      | ~ v1_relat_1(k2_funct_1(sK5))
% 3.25/1.02      | k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.25/1.02      | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_923]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_936,plain,
% 3.25/1.02      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.25/1.02      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.25/1.02      | k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.25/1.02      | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
% 3.25/1.02      inference(forward_subsumption_resolution,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_924,c_22]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1921,plain,
% 3.25/1.02      ( k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.25/1.02      | k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.25/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_925,plain,
% 3.25/1.02      ( k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.25/1.02      | k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.25/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 3.25/1.02      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_924]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2530,plain,
% 3.25/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.25/1.02      | k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.25/1.02      | k1_relat_1(k2_funct_1(sK5)) != sK4 ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_1921,c_45,c_47,c_925,c_2319,c_2420,c_2422]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2531,plain,
% 3.25/1.02      ( k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.25/1.02      | k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.25/1.02      inference(renaming,[status(thm)],[c_2530]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2534,plain,
% 3.25/1.02      ( k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.25/1.02      | k2_relat_1(sK5) != sK4
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.25/1.02      inference(light_normalisation,[status(thm)],[c_2531,c_2333]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3452,plain,
% 3.25/1.02      ( k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.25/1.02      | sK4 != sK4
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_3379,c_2534]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3456,plain,
% 3.25/1.02      ( k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.25/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.25/1.02      inference(equality_resolution_simp,[status(thm)],[c_3452]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5061,plain,
% 3.25/1.02      ( k2_relat_1(k4_relat_1(sK5)) != sK3
% 3.25/1.02      | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.25/1.02      inference(light_normalisation,[status(thm)],[c_3456,c_4234]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5345,plain,
% 3.25/1.02      ( k1_relat_1(sK5) != sK3
% 3.25/1.02      | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_4237,c_5061]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5634,plain,
% 3.25/1.02      ( sK4 = k1_xboole_0 ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_5618,c_4126,c_5345]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5936,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,sK3,k4_relat_1(sK5)) != k1_xboole_0
% 3.25/1.02      | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.25/1.02      | m1_subset_1(k4_relat_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_4364,c_4126,c_5345,c_5618]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5,plain,
% 3.25/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1954,plain,
% 3.25/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_15,plain,
% 3.25/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(k4_relat_1(X0)) ),
% 3.25/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1948,plain,
% 3.25/1.02      ( v1_xboole_0(X0) != iProver_top
% 3.25/1.02      | v1_xboole_0(k4_relat_1(X0)) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_6,plain,
% 3.25/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.25/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1953,plain,
% 3.25/1.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2941,plain,
% 3.25/1.02      ( k4_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_1948,c_1953]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3138,plain,
% 3.25/1.02      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_1954,c_2941]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_27,plain,
% 3.25/1.02      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.25/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.25/1.02      | k1_xboole_0 = X1
% 3.25/1.02      | k1_xboole_0 = X0 ),
% 3.25/1.02      inference(cnf_transformation,[],[f112]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_735,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.25/1.02      | ~ v1_funct_1(X2)
% 3.25/1.02      | ~ v1_relat_1(X2)
% 3.25/1.02      | X2 != X0
% 3.25/1.02      | k1_relat_1(X2) != X1
% 3.25/1.02      | k2_relat_1(X2) != k1_xboole_0
% 3.25/1.02      | k1_xboole_0 = X0
% 3.25/1.02      | k1_xboole_0 = X1 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_27,c_37]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_736,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.25/1.02      | ~ v1_funct_1(X0)
% 3.25/1.02      | ~ v1_relat_1(X0)
% 3.25/1.02      | k2_relat_1(X0) != k1_xboole_0
% 3.25/1.02      | k1_xboole_0 = X0
% 3.25/1.02      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_735]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_752,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.25/1.02      | ~ v1_funct_1(X0)
% 3.25/1.02      | k2_relat_1(X0) != k1_xboole_0
% 3.25/1.02      | k1_xboole_0 = X0
% 3.25/1.02      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.25/1.02      inference(forward_subsumption_resolution,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_736,c_22]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1929,plain,
% 3.25/1.02      ( k2_relat_1(X0) != k1_xboole_0
% 3.25/1.02      | k1_xboole_0 = X0
% 3.25/1.02      | k1_xboole_0 = k1_relat_1(X0)
% 3.25/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
% 3.25/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_7,plain,
% 3.25/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.25/1.02      inference(cnf_transformation,[],[f108]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2165,plain,
% 3.25/1.02      ( k1_relat_1(X0) = k1_xboole_0
% 3.25/1.02      | k2_relat_1(X0) != k1_xboole_0
% 3.25/1.02      | k1_xboole_0 = X0
% 3.25/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.25/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_1929,c_7]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5539,plain,
% 3.25/1.02      ( k1_relat_1(sK5) = k1_xboole_0
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | sK5 = k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.25/1.02      | v1_funct_1(sK5) != iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_3379,c_2165]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_761,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.25/1.02      | sK3 != X1
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | sK5 != X0
% 3.25/1.02      | k1_xboole_0 = X0
% 3.25/1.02      | k1_xboole_0 = X1 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_27,c_43]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_762,plain,
% 3.25/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | k1_xboole_0 = sK3
% 3.25/1.02      | k1_xboole_0 = sK5 ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_761]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1928,plain,
% 3.25/1.02      ( sK4 != k1_xboole_0
% 3.25/1.02      | k1_xboole_0 = sK3
% 3.25/1.02      | k1_xboole_0 = sK5
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2103,plain,
% 3.25/1.02      ( sK3 = k1_xboole_0
% 3.25/1.02      | sK4 != k1_xboole_0
% 3.25/1.02      | sK5 = k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_1928,c_7]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1022,plain,( X0 = X0 ),theory(equality) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2660,plain,
% 3.25/1.02      ( sK5 = sK5 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_1022]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1023,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2661,plain,
% 3.25/1.02      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_1023]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3098,plain,
% 3.25/1.02      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_2661]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3099,plain,
% 3.25/1.02      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_3098]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3575,plain,
% 3.25/1.02      ( ~ v1_xboole_0(sK5) | k1_xboole_0 = sK5 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1024,plain,
% 3.25/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.25/1.02      theory(equality) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3690,plain,
% 3.25/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_1024]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3692,plain,
% 3.25/1.02      ( v1_xboole_0(sK3)
% 3.25/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 3.25/1.02      | sK3 != k1_xboole_0 ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_3690]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_23,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.02      | ~ v1_xboole_0(X1)
% 3.25/1.02      | v1_xboole_0(X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1943,plain,
% 3.25/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.25/1.02      | v1_xboole_0(X1) != iProver_top
% 3.25/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4539,plain,
% 3.25/1.02      ( v1_xboole_0(sK3) != iProver_top
% 3.25/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_1936,c_1943]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4586,plain,
% 3.25/1.02      ( ~ v1_xboole_0(sK3) | v1_xboole_0(sK5) ),
% 3.25/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4539]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5609,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.25/1.02      | sK5 = k1_xboole_0
% 3.25/1.02      | sK4 != k1_xboole_0 ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_5539,c_5,c_2103,c_2660,c_3099,c_3575,c_3692,c_4586]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5610,plain,
% 3.25/1.02      ( sK4 != k1_xboole_0
% 3.25/1.02      | sK5 = k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(renaming,[status(thm)],[c_5609]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5638,plain,
% 3.25/1.02      ( sK5 = k1_xboole_0
% 3.25/1.02      | k1_xboole_0 != k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_5634,c_5610]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5719,plain,
% 3.25/1.02      ( sK5 = k1_xboole_0
% 3.25/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(equality_resolution_simp,[status(thm)],[c_5638]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5658,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_5634,c_1936]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5663,plain,
% 3.25/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_5658,c_7]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5722,plain,
% 3.25/1.02      ( sK5 = k1_xboole_0 ),
% 3.25/1.02      inference(forward_subsumption_resolution,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_5719,c_5663]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5940,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,sK3,k1_xboole_0) != k1_xboole_0
% 3.25/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 3.25/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(light_normalisation,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_5936,c_3138,c_5634,c_5722]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_32,plain,
% 3.25/1.02      ( v1_funct_2(sK2(X0,X1),X0,X1) ),
% 3.25/1.02      inference(cnf_transformation,[],[f98]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_720,plain,
% 3.25/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.25/1.02      | X2 != X1
% 3.25/1.02      | sK2(X2,X3) != X0
% 3.25/1.02      | k1_xboole_0 != X3
% 3.25/1.02      | k1_xboole_0 = X0
% 3.25/1.02      | k1_xboole_0 = X1 ),
% 3.25/1.02      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_721,plain,
% 3.25/1.02      ( ~ m1_subset_1(sK2(X0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.25/1.02      | k1_xboole_0 = X0
% 3.25/1.02      | k1_xboole_0 = sK2(X0,k1_xboole_0) ),
% 3.25/1.02      inference(unflattening,[status(thm)],[c_720]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_35,plain,
% 3.25/1.02      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.25/1.02      inference(cnf_transformation,[],[f95]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_731,plain,
% 3.25/1.02      ( k1_xboole_0 = X0 | k1_xboole_0 = sK2(X0,k1_xboole_0) ),
% 3.25/1.02      inference(forward_subsumption_resolution,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_721,c_35]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_1938,plain,
% 3.25/1.02      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2765,plain,
% 3.25/1.02      ( k1_xboole_0 = X0
% 3.25/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_731,c_1938]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2774,plain,
% 3.25/1.02      ( k1_xboole_0 = X0
% 3.25/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.25/1.02      inference(light_normalisation,[status(thm)],[c_2765,c_7]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3,plain,
% 3.25/1.02      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.25/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_11,plain,
% 3.25/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.25/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_326,plain,
% 3.25/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.25/1.02      inference(prop_impl,[status(thm)],[c_11]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_327,plain,
% 3.25/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.25/1.02      inference(renaming,[status(thm)],[c_326]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_619,plain,
% 3.25/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(sK1(X0,X1),X0) ),
% 3.25/1.02      inference(resolution,[status(thm)],[c_3,c_327]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_620,plain,
% 3.25/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.25/1.02      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_622,plain,
% 3.25/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.25/1.02      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_620]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2,plain,
% 3.25/1.02      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 3.25/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_644,plain,
% 3.25/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 3.25/1.02      inference(resolution,[status(thm)],[c_2,c_327]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_645,plain,
% 3.25/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.25/1.02      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 3.25/1.02      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_647,plain,
% 3.25/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.25/1.02      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 3.25/1.02      inference(instantiation,[status(thm)],[c_645]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_2978,plain,
% 3.25/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.25/1.02      inference(global_propositional_subsumption,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_2774,c_622,c_647]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3861,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.25/1.02      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_8,c_1942]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4749,plain,
% 3.25/1.02      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.25/1.02      inference(superposition,[status(thm)],[c_2978,c_3861]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5941,plain,
% 3.25/1.02      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 3.25/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_5940,c_8,c_4749]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5944,plain,
% 3.25/1.02      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 3.25/1.02      inference(forward_subsumption_resolution,
% 3.25/1.02                [status(thm)],
% 3.25/1.02                [c_5941,c_2978]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_3453,plain,
% 3.25/1.02      ( k1_relat_1(k2_funct_1(sK5)) = sK4 ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_3379,c_2333]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_4362,plain,
% 3.25/1.02      ( k1_relat_1(k4_relat_1(sK5)) = sK4 ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_4234,c_3453]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5647,plain,
% 3.25/1.02      ( k1_relat_1(k4_relat_1(sK5)) = k1_xboole_0 ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_5634,c_4362]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5729,plain,
% 3.25/1.02      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.25/1.02      inference(demodulation,[status(thm)],[c_5722,c_5647]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(c_5749,plain,
% 3.25/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.25/1.02      inference(light_normalisation,[status(thm)],[c_5729,c_3138]) ).
% 3.25/1.02  
% 3.25/1.02  cnf(contradiction,plain,
% 3.25/1.02      ( $false ),
% 3.25/1.02      inference(minisat,[status(thm)],[c_5944,c_5749]) ).
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.25/1.02  
% 3.25/1.02  ------                               Statistics
% 3.25/1.02  
% 3.25/1.02  ------ General
% 3.25/1.02  
% 3.25/1.02  abstr_ref_over_cycles:                  0
% 3.25/1.02  abstr_ref_under_cycles:                 0
% 3.25/1.02  gc_basic_clause_elim:                   0
% 3.25/1.02  forced_gc_time:                         0
% 3.25/1.02  parsing_time:                           0.012
% 3.25/1.02  unif_index_cands_time:                  0.
% 3.25/1.02  unif_index_add_time:                    0.
% 3.25/1.02  orderings_time:                         0.
% 3.25/1.02  out_proof_time:                         0.014
% 3.25/1.02  total_time:                             0.195
% 3.25/1.02  num_of_symbols:                         54
% 3.25/1.02  num_of_terms:                           3996
% 3.25/1.02  
% 3.25/1.02  ------ Preprocessing
% 3.25/1.02  
% 3.25/1.02  num_of_splits:                          0
% 3.25/1.02  num_of_split_atoms:                     0
% 3.25/1.02  num_of_reused_defs:                     0
% 3.25/1.02  num_eq_ax_congr_red:                    17
% 3.25/1.02  num_of_sem_filtered_clauses:            1
% 3.25/1.02  num_of_subtypes:                        0
% 3.25/1.02  monotx_restored_types:                  0
% 3.25/1.02  sat_num_of_epr_types:                   0
% 3.25/1.02  sat_num_of_non_cyclic_types:            0
% 3.25/1.02  sat_guarded_non_collapsed_types:        0
% 3.25/1.02  num_pure_diseq_elim:                    0
% 3.25/1.02  simp_replaced_by:                       0
% 3.25/1.02  res_preprocessed:                       173
% 3.25/1.02  prep_upred:                             0
% 3.25/1.02  prep_unflattend:                        55
% 3.25/1.02  smt_new_axioms:                         0
% 3.25/1.02  pred_elim_cands:                        8
% 3.25/1.02  pred_elim:                              2
% 3.25/1.02  pred_elim_cl:                           -4
% 3.25/1.02  pred_elim_cycles:                       4
% 3.25/1.02  merged_defs:                            6
% 3.25/1.02  merged_defs_ncl:                        0
% 3.25/1.02  bin_hyper_res:                          7
% 3.25/1.02  prep_cycles:                            3
% 3.25/1.02  pred_elim_time:                         0.01
% 3.25/1.02  splitting_time:                         0.
% 3.25/1.02  sem_filter_time:                        0.
% 3.25/1.02  monotx_time:                            0.
% 3.25/1.02  subtype_inf_time:                       0.
% 3.25/1.02  
% 3.25/1.02  ------ Problem properties
% 3.25/1.02  
% 3.25/1.02  clauses:                                48
% 3.25/1.02  conjectures:                            3
% 3.25/1.02  epr:                                    7
% 3.25/1.02  horn:                                   39
% 3.25/1.02  ground:                                 16
% 3.25/1.02  unary:                                  10
% 3.25/1.02  binary:                                 20
% 3.25/1.02  lits:                                   117
% 3.25/1.02  lits_eq:                                43
% 3.25/1.02  fd_pure:                                0
% 3.25/1.02  fd_pseudo:                              0
% 3.25/1.02  fd_cond:                                4
% 3.25/1.02  fd_pseudo_cond:                         0
% 3.25/1.02  ac_symbols:                             0
% 3.25/1.02  
% 3.25/1.02  ------ Propositional Solver
% 3.25/1.02  
% 3.25/1.02  prop_solver_calls:                      24
% 3.25/1.02  prop_fast_solver_calls:                 1242
% 3.25/1.02  smt_solver_calls:                       0
% 3.25/1.02  smt_fast_solver_calls:                  0
% 3.25/1.02  prop_num_of_clauses:                    1677
% 3.25/1.02  prop_preprocess_simplified:             6514
% 3.25/1.02  prop_fo_subsumed:                       35
% 3.25/1.02  prop_solver_time:                       0.
% 3.25/1.02  smt_solver_time:                        0.
% 3.25/1.02  smt_fast_solver_time:                   0.
% 3.25/1.02  prop_fast_solver_time:                  0.
% 3.25/1.02  prop_unsat_core_time:                   0.
% 3.25/1.02  
% 3.25/1.02  ------ QBF
% 3.25/1.02  
% 3.25/1.02  qbf_q_res:                              0
% 3.25/1.02  qbf_num_tautologies:                    0
% 3.25/1.02  qbf_prep_cycles:                        0
% 3.25/1.02  
% 3.25/1.02  ------ BMC1
% 3.25/1.02  
% 3.25/1.02  bmc1_current_bound:                     -1
% 3.25/1.02  bmc1_last_solved_bound:                 -1
% 3.25/1.02  bmc1_unsat_core_size:                   -1
% 3.25/1.02  bmc1_unsat_core_parents_size:           -1
% 3.25/1.02  bmc1_merge_next_fun:                    0
% 3.25/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.25/1.02  
% 3.25/1.02  ------ Instantiation
% 3.25/1.02  
% 3.25/1.02  inst_num_of_clauses:                    609
% 3.25/1.02  inst_num_in_passive:                    171
% 3.25/1.02  inst_num_in_active:                     357
% 3.25/1.02  inst_num_in_unprocessed:                81
% 3.25/1.02  inst_num_of_loops:                      550
% 3.25/1.02  inst_num_of_learning_restarts:          0
% 3.25/1.02  inst_num_moves_active_passive:          190
% 3.25/1.02  inst_lit_activity:                      0
% 3.25/1.02  inst_lit_activity_moves:                0
% 3.25/1.02  inst_num_tautologies:                   0
% 3.25/1.02  inst_num_prop_implied:                  0
% 3.25/1.02  inst_num_existing_simplified:           0
% 3.25/1.02  inst_num_eq_res_simplified:             0
% 3.25/1.02  inst_num_child_elim:                    0
% 3.25/1.02  inst_num_of_dismatching_blockings:      135
% 3.25/1.02  inst_num_of_non_proper_insts:           493
% 3.25/1.02  inst_num_of_duplicates:                 0
% 3.25/1.02  inst_inst_num_from_inst_to_res:         0
% 3.25/1.02  inst_dismatching_checking_time:         0.
% 3.25/1.02  
% 3.25/1.02  ------ Resolution
% 3.25/1.02  
% 3.25/1.02  res_num_of_clauses:                     0
% 3.25/1.02  res_num_in_passive:                     0
% 3.25/1.02  res_num_in_active:                      0
% 3.25/1.02  res_num_of_loops:                       176
% 3.25/1.02  res_forward_subset_subsumed:            19
% 3.25/1.02  res_backward_subset_subsumed:           4
% 3.25/1.02  res_forward_subsumed:                   1
% 3.25/1.02  res_backward_subsumed:                  0
% 3.25/1.02  res_forward_subsumption_resolution:     5
% 3.25/1.02  res_backward_subsumption_resolution:    0
% 3.25/1.02  res_clause_to_clause_subsumption:       333
% 3.25/1.02  res_orphan_elimination:                 0
% 3.25/1.02  res_tautology_del:                      71
% 3.25/1.02  res_num_eq_res_simplified:              0
% 3.25/1.02  res_num_sel_changes:                    0
% 3.25/1.02  res_moves_from_active_to_pass:          0
% 3.25/1.02  
% 3.25/1.02  ------ Superposition
% 3.25/1.02  
% 3.25/1.02  sup_time_total:                         0.
% 3.25/1.02  sup_time_generating:                    0.
% 3.25/1.02  sup_time_sim_full:                      0.
% 3.25/1.02  sup_time_sim_immed:                     0.
% 3.25/1.02  
% 3.25/1.02  sup_num_of_clauses:                     126
% 3.25/1.02  sup_num_in_active:                      58
% 3.25/1.02  sup_num_in_passive:                     68
% 3.25/1.02  sup_num_of_loops:                       109
% 3.25/1.02  sup_fw_superposition:                   102
% 3.25/1.02  sup_bw_superposition:                   53
% 3.25/1.02  sup_immediate_simplified:               80
% 3.25/1.02  sup_given_eliminated:                   0
% 3.25/1.02  comparisons_done:                       0
% 3.25/1.02  comparisons_avoided:                    13
% 3.25/1.02  
% 3.25/1.02  ------ Simplifications
% 3.25/1.02  
% 3.25/1.02  
% 3.25/1.02  sim_fw_subset_subsumed:                 19
% 3.25/1.02  sim_bw_subset_subsumed:                 3
% 3.25/1.02  sim_fw_subsumed:                        7
% 3.25/1.02  sim_bw_subsumed:                        2
% 3.25/1.02  sim_fw_subsumption_res:                 5
% 3.25/1.02  sim_bw_subsumption_res:                 0
% 3.25/1.02  sim_tautology_del:                      5
% 3.25/1.02  sim_eq_tautology_del:                   9
% 3.25/1.02  sim_eq_res_simp:                        4
% 3.25/1.02  sim_fw_demodulated:                     22
% 3.25/1.02  sim_bw_demodulated:                     67
% 3.25/1.02  sim_light_normalised:                   37
% 3.25/1.02  sim_joinable_taut:                      0
% 3.25/1.02  sim_joinable_simp:                      0
% 3.25/1.02  sim_ac_normalised:                      0
% 3.25/1.02  sim_smt_subsumption:                    0
% 3.25/1.02  
%------------------------------------------------------------------------------

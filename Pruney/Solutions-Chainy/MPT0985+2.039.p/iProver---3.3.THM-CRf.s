%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:27 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  194 (4037 expanded)
%              Number of clauses        :  127 (1418 expanded)
%              Number of leaves         :   18 ( 760 expanded)
%              Depth                    :   24
%              Number of atoms          :  609 (20549 expanded)
%              Number of equality atoms :  300 (4420 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
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

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

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
    inference(ennf_transformation,[],[f27])).

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

fof(f69,plain,
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

fof(f70,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f55,f69])).

fof(f118,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f70])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f106,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f24,axiom,(
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

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f51])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f117,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f99,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f116,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f115,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f120,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f70])).

fof(f98,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f94,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f89,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f114,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f121,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f70])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f129,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f110])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f130,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f108])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f62])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f125,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f90,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f91,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_48,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2135,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_35,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_33,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_584,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_35,c_33])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_35,c_33])).

cnf(c_589,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_588])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_728,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_589,c_41])).

cnf(c_2126,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_3544,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2135,c_2126])).

cnf(c_49,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_853,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_49])).

cnf(c_854,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_1075,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2609,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1075])).

cnf(c_2855,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2609])).

cnf(c_1074,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2856,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_3743,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3544,c_48,c_854,c_2855,c_2856])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2138,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5647,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2135,c_2138])).

cnf(c_5783,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3743,c_5647])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2140,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3654,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2135,c_2140])).

cnf(c_27,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_47,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_678,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_47])).

cnf(c_679,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_678])).

cnf(c_50,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_681,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_679,c_50])).

cnf(c_2128,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_3699,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3654,c_2128])).

cnf(c_42,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2136,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_6035,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3699,c_2136])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2137,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4459,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2135,c_2137])).

cnf(c_46,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_4471,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4459,c_46])).

cnf(c_28,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_664,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_47])).

cnf(c_665,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_667,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_50])).

cnf(c_2129,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_3698,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3654,c_2129])).

cnf(c_4759,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4471,c_3698])).

cnf(c_6072,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6035,c_4759])).

cnf(c_51,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_53,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2547,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2548,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2547])).

cnf(c_23,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2550,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2551,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2550])).

cnf(c_2564,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2565,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2564])).

cnf(c_6603,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6072,c_51,c_53,c_2548,c_2551,c_2565])).

cnf(c_6610,plain,
    ( v1_relat_1(k2_funct_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6603,c_2140])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2146,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6737,plain,
    ( k10_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3))) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_6610,c_2146])).

cnf(c_6739,plain,
    ( k10_relat_1(k2_funct_1(sK3),k1_relat_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_6737,c_3699,c_4759])).

cnf(c_6745,plain,
    ( k10_relat_1(k2_funct_1(sK3),sK1) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5783,c_6739])).

cnf(c_43,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_45,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_970,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k1_relat_1(X0) != sK2
    | k2_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_45])).

cnf(c_971,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(unflattening,[status(thm)],[c_970])).

cnf(c_983,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_971,c_29])).

cnf(c_2115,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_983])).

cnf(c_972,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_971])).

cnf(c_2733,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2115,c_51,c_53,c_972,c_2548,c_2551,c_2565])).

cnf(c_2734,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2733])).

cnf(c_3748,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3698,c_2734])).

cnf(c_4223,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3748,c_3699])).

cnf(c_4754,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4471,c_4223])).

cnf(c_4777,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4754])).

cnf(c_5881,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5783,c_4777])).

cnf(c_38,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_939,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_45])).

cnf(c_940,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1)
    | X3 != X0
    | X4 != X2
    | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_589,c_40])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_780,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_3])).

cnf(c_781,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_780])).

cnf(c_947,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | sK2 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_940,c_781])).

cnf(c_2117,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_2417,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2117,c_8])).

cnf(c_157,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1078,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2567,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_2568,plain,
    ( sK2 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2567])).

cnf(c_2570,plain,
    ( sK2 != k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2568])).

cnf(c_824,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_xboole_0(X1)
    | k2_funct_1(sK3) != X0
    | sK1 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_589,c_45])).

cnf(c_825,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(c_2122,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_826,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_2578,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2122,c_51,c_53,c_826,c_2548,c_2565])).

cnf(c_2910,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2417,c_157,c_2570,c_2578])).

cnf(c_5977,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5881,c_2910])).

cnf(c_6608,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5783,c_6603])).

cnf(c_9561,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6745,c_2910,c_5881,c_6608])).

cnf(c_9576,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9561,c_6603])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2144,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4110,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3698,c_2144])).

cnf(c_4111,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4110,c_3699])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2686,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4187,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4111,c_48,c_2564,c_2686])).

cnf(c_4188,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4187])).

cnf(c_4756,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4471,c_4188])).

cnf(c_9587,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9561,c_4756])).

cnf(c_9661,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9587])).

cnf(c_9697,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9576,c_9661])).

cnf(c_9699,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9697,c_8])).

cnf(c_9596,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9561,c_2910])).

cnf(c_9644,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9596])).

cnf(c_9646,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9644,c_8])).

cnf(c_9701,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_9699,c_9646])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n011.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 11:02:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.51/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.51/0.98  
% 3.51/0.98  ------  iProver source info
% 3.51/0.98  
% 3.51/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.51/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.51/0.98  git: non_committed_changes: false
% 3.51/0.98  git: last_make_outside_of_git: false
% 3.51/0.98  
% 3.51/0.98  ------ 
% 3.51/0.98  
% 3.51/0.98  ------ Input Options
% 3.51/0.98  
% 3.51/0.98  --out_options                           all
% 3.51/0.98  --tptp_safe_out                         true
% 3.51/0.98  --problem_path                          ""
% 3.51/0.98  --include_path                          ""
% 3.51/0.98  --clausifier                            res/vclausify_rel
% 3.51/0.98  --clausifier_options                    --mode clausify
% 3.51/0.98  --stdin                                 false
% 3.51/0.98  --stats_out                             all
% 3.51/0.98  
% 3.51/0.98  ------ General Options
% 3.51/0.98  
% 3.51/0.98  --fof                                   false
% 3.51/0.98  --time_out_real                         305.
% 3.51/0.98  --time_out_virtual                      -1.
% 3.51/0.98  --symbol_type_check                     false
% 3.51/0.98  --clausify_out                          false
% 3.51/0.98  --sig_cnt_out                           false
% 3.51/0.98  --trig_cnt_out                          false
% 3.51/0.98  --trig_cnt_out_tolerance                1.
% 3.51/0.98  --trig_cnt_out_sk_spl                   false
% 3.51/0.98  --abstr_cl_out                          false
% 3.51/0.98  
% 3.51/0.98  ------ Global Options
% 3.51/0.98  
% 3.51/0.98  --schedule                              default
% 3.51/0.98  --add_important_lit                     false
% 3.51/0.98  --prop_solver_per_cl                    1000
% 3.51/0.98  --min_unsat_core                        false
% 3.51/0.98  --soft_assumptions                      false
% 3.51/0.98  --soft_lemma_size                       3
% 3.51/0.98  --prop_impl_unit_size                   0
% 3.51/0.98  --prop_impl_unit                        []
% 3.51/0.98  --share_sel_clauses                     true
% 3.51/0.98  --reset_solvers                         false
% 3.51/0.98  --bc_imp_inh                            [conj_cone]
% 3.51/0.98  --conj_cone_tolerance                   3.
% 3.51/0.98  --extra_neg_conj                        none
% 3.51/0.98  --large_theory_mode                     true
% 3.51/0.98  --prolific_symb_bound                   200
% 3.51/0.98  --lt_threshold                          2000
% 3.51/0.98  --clause_weak_htbl                      true
% 3.51/0.98  --gc_record_bc_elim                     false
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing Options
% 3.51/0.99  
% 3.51/0.99  --preprocessing_flag                    true
% 3.51/0.99  --time_out_prep_mult                    0.1
% 3.51/0.99  --splitting_mode                        input
% 3.51/0.99  --splitting_grd                         true
% 3.51/0.99  --splitting_cvd                         false
% 3.51/0.99  --splitting_cvd_svl                     false
% 3.51/0.99  --splitting_nvd                         32
% 3.51/0.99  --sub_typing                            true
% 3.51/0.99  --prep_gs_sim                           true
% 3.51/0.99  --prep_unflatten                        true
% 3.51/0.99  --prep_res_sim                          true
% 3.51/0.99  --prep_upred                            true
% 3.51/0.99  --prep_sem_filter                       exhaustive
% 3.51/0.99  --prep_sem_filter_out                   false
% 3.51/0.99  --pred_elim                             true
% 3.51/0.99  --res_sim_input                         true
% 3.51/0.99  --eq_ax_congr_red                       true
% 3.51/0.99  --pure_diseq_elim                       true
% 3.51/0.99  --brand_transform                       false
% 3.51/0.99  --non_eq_to_eq                          false
% 3.51/0.99  --prep_def_merge                        true
% 3.51/0.99  --prep_def_merge_prop_impl              false
% 3.51/0.99  --prep_def_merge_mbd                    true
% 3.51/0.99  --prep_def_merge_tr_red                 false
% 3.51/0.99  --prep_def_merge_tr_cl                  false
% 3.51/0.99  --smt_preprocessing                     true
% 3.51/0.99  --smt_ac_axioms                         fast
% 3.51/0.99  --preprocessed_out                      false
% 3.51/0.99  --preprocessed_stats                    false
% 3.51/0.99  
% 3.51/0.99  ------ Abstraction refinement Options
% 3.51/0.99  
% 3.51/0.99  --abstr_ref                             []
% 3.51/0.99  --abstr_ref_prep                        false
% 3.51/0.99  --abstr_ref_until_sat                   false
% 3.51/0.99  --abstr_ref_sig_restrict                funpre
% 3.51/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.99  --abstr_ref_under                       []
% 3.51/0.99  
% 3.51/0.99  ------ SAT Options
% 3.51/0.99  
% 3.51/0.99  --sat_mode                              false
% 3.51/0.99  --sat_fm_restart_options                ""
% 3.51/0.99  --sat_gr_def                            false
% 3.51/0.99  --sat_epr_types                         true
% 3.51/0.99  --sat_non_cyclic_types                  false
% 3.51/0.99  --sat_finite_models                     false
% 3.51/0.99  --sat_fm_lemmas                         false
% 3.51/0.99  --sat_fm_prep                           false
% 3.51/0.99  --sat_fm_uc_incr                        true
% 3.51/0.99  --sat_out_model                         small
% 3.51/0.99  --sat_out_clauses                       false
% 3.51/0.99  
% 3.51/0.99  ------ QBF Options
% 3.51/0.99  
% 3.51/0.99  --qbf_mode                              false
% 3.51/0.99  --qbf_elim_univ                         false
% 3.51/0.99  --qbf_dom_inst                          none
% 3.51/0.99  --qbf_dom_pre_inst                      false
% 3.51/0.99  --qbf_sk_in                             false
% 3.51/0.99  --qbf_pred_elim                         true
% 3.51/0.99  --qbf_split                             512
% 3.51/0.99  
% 3.51/0.99  ------ BMC1 Options
% 3.51/0.99  
% 3.51/0.99  --bmc1_incremental                      false
% 3.51/0.99  --bmc1_axioms                           reachable_all
% 3.51/0.99  --bmc1_min_bound                        0
% 3.51/0.99  --bmc1_max_bound                        -1
% 3.51/0.99  --bmc1_max_bound_default                -1
% 3.51/0.99  --bmc1_symbol_reachability              true
% 3.51/0.99  --bmc1_property_lemmas                  false
% 3.51/0.99  --bmc1_k_induction                      false
% 3.51/0.99  --bmc1_non_equiv_states                 false
% 3.51/0.99  --bmc1_deadlock                         false
% 3.51/0.99  --bmc1_ucm                              false
% 3.51/0.99  --bmc1_add_unsat_core                   none
% 3.51/0.99  --bmc1_unsat_core_children              false
% 3.51/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.99  --bmc1_out_stat                         full
% 3.51/0.99  --bmc1_ground_init                      false
% 3.51/0.99  --bmc1_pre_inst_next_state              false
% 3.51/0.99  --bmc1_pre_inst_state                   false
% 3.51/0.99  --bmc1_pre_inst_reach_state             false
% 3.51/0.99  --bmc1_out_unsat_core                   false
% 3.51/0.99  --bmc1_aig_witness_out                  false
% 3.51/0.99  --bmc1_verbose                          false
% 3.51/0.99  --bmc1_dump_clauses_tptp                false
% 3.51/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.99  --bmc1_dump_file                        -
% 3.51/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.99  --bmc1_ucm_extend_mode                  1
% 3.51/0.99  --bmc1_ucm_init_mode                    2
% 3.51/0.99  --bmc1_ucm_cone_mode                    none
% 3.51/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.99  --bmc1_ucm_relax_model                  4
% 3.51/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.99  --bmc1_ucm_layered_model                none
% 3.51/0.99  --bmc1_ucm_max_lemma_size               10
% 3.51/0.99  
% 3.51/0.99  ------ AIG Options
% 3.51/0.99  
% 3.51/0.99  --aig_mode                              false
% 3.51/0.99  
% 3.51/0.99  ------ Instantiation Options
% 3.51/0.99  
% 3.51/0.99  --instantiation_flag                    true
% 3.51/0.99  --inst_sos_flag                         false
% 3.51/0.99  --inst_sos_phase                        true
% 3.51/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel_side                     num_symb
% 3.51/0.99  --inst_solver_per_active                1400
% 3.51/0.99  --inst_solver_calls_frac                1.
% 3.51/0.99  --inst_passive_queue_type               priority_queues
% 3.51/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.99  --inst_passive_queues_freq              [25;2]
% 3.51/0.99  --inst_dismatching                      true
% 3.51/0.99  --inst_eager_unprocessed_to_passive     true
% 3.51/0.99  --inst_prop_sim_given                   true
% 3.51/0.99  --inst_prop_sim_new                     false
% 3.51/0.99  --inst_subs_new                         false
% 3.51/0.99  --inst_eq_res_simp                      false
% 3.51/0.99  --inst_subs_given                       false
% 3.51/0.99  --inst_orphan_elimination               true
% 3.51/0.99  --inst_learning_loop_flag               true
% 3.51/0.99  --inst_learning_start                   3000
% 3.51/0.99  --inst_learning_factor                  2
% 3.51/0.99  --inst_start_prop_sim_after_learn       3
% 3.51/0.99  --inst_sel_renew                        solver
% 3.51/0.99  --inst_lit_activity_flag                true
% 3.51/0.99  --inst_restr_to_given                   false
% 3.51/0.99  --inst_activity_threshold               500
% 3.51/0.99  --inst_out_proof                        true
% 3.51/0.99  
% 3.51/0.99  ------ Resolution Options
% 3.51/0.99  
% 3.51/0.99  --resolution_flag                       true
% 3.51/0.99  --res_lit_sel                           adaptive
% 3.51/0.99  --res_lit_sel_side                      none
% 3.51/0.99  --res_ordering                          kbo
% 3.51/0.99  --res_to_prop_solver                    active
% 3.51/0.99  --res_prop_simpl_new                    false
% 3.51/0.99  --res_prop_simpl_given                  true
% 3.51/0.99  --res_passive_queue_type                priority_queues
% 3.51/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.99  --res_passive_queues_freq               [15;5]
% 3.51/0.99  --res_forward_subs                      full
% 3.51/0.99  --res_backward_subs                     full
% 3.51/0.99  --res_forward_subs_resolution           true
% 3.51/0.99  --res_backward_subs_resolution          true
% 3.51/0.99  --res_orphan_elimination                true
% 3.51/0.99  --res_time_limit                        2.
% 3.51/0.99  --res_out_proof                         true
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Options
% 3.51/0.99  
% 3.51/0.99  --superposition_flag                    true
% 3.51/0.99  --sup_passive_queue_type                priority_queues
% 3.51/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.99  --demod_completeness_check              fast
% 3.51/0.99  --demod_use_ground                      true
% 3.51/0.99  --sup_to_prop_solver                    passive
% 3.51/0.99  --sup_prop_simpl_new                    true
% 3.51/0.99  --sup_prop_simpl_given                  true
% 3.51/0.99  --sup_fun_splitting                     false
% 3.51/0.99  --sup_smt_interval                      50000
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Simplification Setup
% 3.51/0.99  
% 3.51/0.99  --sup_indices_passive                   []
% 3.51/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_full_bw                           [BwDemod]
% 3.51/0.99  --sup_immed_triv                        [TrivRules]
% 3.51/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_immed_bw_main                     []
% 3.51/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  
% 3.51/0.99  ------ Combination Options
% 3.51/0.99  
% 3.51/0.99  --comb_res_mult                         3
% 3.51/0.99  --comb_sup_mult                         2
% 3.51/0.99  --comb_inst_mult                        10
% 3.51/0.99  
% 3.51/0.99  ------ Debug Options
% 3.51/0.99  
% 3.51/0.99  --dbg_backtrace                         false
% 3.51/0.99  --dbg_dump_prop_clauses                 false
% 3.51/0.99  --dbg_dump_prop_clauses_file            -
% 3.51/0.99  --dbg_out_stat                          false
% 3.51/0.99  ------ Parsing...
% 3.51/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.51/0.99  ------ Proving...
% 3.51/0.99  ------ Problem Properties 
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  clauses                                 52
% 3.51/0.99  conjectures                             3
% 3.51/0.99  EPR                                     7
% 3.51/0.99  Horn                                    44
% 3.51/0.99  unary                                   10
% 3.51/0.99  binary                                  16
% 3.51/0.99  lits                                    136
% 3.51/0.99  lits eq                                 49
% 3.51/0.99  fd_pure                                 0
% 3.51/0.99  fd_pseudo                               0
% 3.51/0.99  fd_cond                                 3
% 3.51/0.99  fd_pseudo_cond                          1
% 3.51/0.99  AC symbols                              0
% 3.51/0.99  
% 3.51/0.99  ------ Schedule dynamic 5 is on 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  ------ 
% 3.51/0.99  Current options:
% 3.51/0.99  ------ 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options
% 3.51/0.99  
% 3.51/0.99  --out_options                           all
% 3.51/0.99  --tptp_safe_out                         true
% 3.51/0.99  --problem_path                          ""
% 3.51/0.99  --include_path                          ""
% 3.51/0.99  --clausifier                            res/vclausify_rel
% 3.51/0.99  --clausifier_options                    --mode clausify
% 3.51/0.99  --stdin                                 false
% 3.51/0.99  --stats_out                             all
% 3.51/0.99  
% 3.51/0.99  ------ General Options
% 3.51/0.99  
% 3.51/0.99  --fof                                   false
% 3.51/0.99  --time_out_real                         305.
% 3.51/0.99  --time_out_virtual                      -1.
% 3.51/0.99  --symbol_type_check                     false
% 3.51/0.99  --clausify_out                          false
% 3.51/0.99  --sig_cnt_out                           false
% 3.51/0.99  --trig_cnt_out                          false
% 3.51/0.99  --trig_cnt_out_tolerance                1.
% 3.51/0.99  --trig_cnt_out_sk_spl                   false
% 3.51/0.99  --abstr_cl_out                          false
% 3.51/0.99  
% 3.51/0.99  ------ Global Options
% 3.51/0.99  
% 3.51/0.99  --schedule                              default
% 3.51/0.99  --add_important_lit                     false
% 3.51/0.99  --prop_solver_per_cl                    1000
% 3.51/0.99  --min_unsat_core                        false
% 3.51/0.99  --soft_assumptions                      false
% 3.51/0.99  --soft_lemma_size                       3
% 3.51/0.99  --prop_impl_unit_size                   0
% 3.51/0.99  --prop_impl_unit                        []
% 3.51/0.99  --share_sel_clauses                     true
% 3.51/0.99  --reset_solvers                         false
% 3.51/0.99  --bc_imp_inh                            [conj_cone]
% 3.51/0.99  --conj_cone_tolerance                   3.
% 3.51/0.99  --extra_neg_conj                        none
% 3.51/0.99  --large_theory_mode                     true
% 3.51/0.99  --prolific_symb_bound                   200
% 3.51/0.99  --lt_threshold                          2000
% 3.51/0.99  --clause_weak_htbl                      true
% 3.51/0.99  --gc_record_bc_elim                     false
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing Options
% 3.51/0.99  
% 3.51/0.99  --preprocessing_flag                    true
% 3.51/0.99  --time_out_prep_mult                    0.1
% 3.51/0.99  --splitting_mode                        input
% 3.51/0.99  --splitting_grd                         true
% 3.51/0.99  --splitting_cvd                         false
% 3.51/0.99  --splitting_cvd_svl                     false
% 3.51/0.99  --splitting_nvd                         32
% 3.51/0.99  --sub_typing                            true
% 3.51/0.99  --prep_gs_sim                           true
% 3.51/0.99  --prep_unflatten                        true
% 3.51/0.99  --prep_res_sim                          true
% 3.51/0.99  --prep_upred                            true
% 3.51/0.99  --prep_sem_filter                       exhaustive
% 3.51/0.99  --prep_sem_filter_out                   false
% 3.51/0.99  --pred_elim                             true
% 3.51/0.99  --res_sim_input                         true
% 3.51/0.99  --eq_ax_congr_red                       true
% 3.51/0.99  --pure_diseq_elim                       true
% 3.51/0.99  --brand_transform                       false
% 3.51/0.99  --non_eq_to_eq                          false
% 3.51/0.99  --prep_def_merge                        true
% 3.51/0.99  --prep_def_merge_prop_impl              false
% 3.51/0.99  --prep_def_merge_mbd                    true
% 3.51/0.99  --prep_def_merge_tr_red                 false
% 3.51/0.99  --prep_def_merge_tr_cl                  false
% 3.51/0.99  --smt_preprocessing                     true
% 3.51/0.99  --smt_ac_axioms                         fast
% 3.51/0.99  --preprocessed_out                      false
% 3.51/0.99  --preprocessed_stats                    false
% 3.51/0.99  
% 3.51/0.99  ------ Abstraction refinement Options
% 3.51/0.99  
% 3.51/0.99  --abstr_ref                             []
% 3.51/0.99  --abstr_ref_prep                        false
% 3.51/0.99  --abstr_ref_until_sat                   false
% 3.51/0.99  --abstr_ref_sig_restrict                funpre
% 3.51/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.99  --abstr_ref_under                       []
% 3.51/0.99  
% 3.51/0.99  ------ SAT Options
% 3.51/0.99  
% 3.51/0.99  --sat_mode                              false
% 3.51/0.99  --sat_fm_restart_options                ""
% 3.51/0.99  --sat_gr_def                            false
% 3.51/0.99  --sat_epr_types                         true
% 3.51/0.99  --sat_non_cyclic_types                  false
% 3.51/0.99  --sat_finite_models                     false
% 3.51/0.99  --sat_fm_lemmas                         false
% 3.51/0.99  --sat_fm_prep                           false
% 3.51/0.99  --sat_fm_uc_incr                        true
% 3.51/0.99  --sat_out_model                         small
% 3.51/0.99  --sat_out_clauses                       false
% 3.51/0.99  
% 3.51/0.99  ------ QBF Options
% 3.51/0.99  
% 3.51/0.99  --qbf_mode                              false
% 3.51/0.99  --qbf_elim_univ                         false
% 3.51/0.99  --qbf_dom_inst                          none
% 3.51/0.99  --qbf_dom_pre_inst                      false
% 3.51/0.99  --qbf_sk_in                             false
% 3.51/0.99  --qbf_pred_elim                         true
% 3.51/0.99  --qbf_split                             512
% 3.51/0.99  
% 3.51/0.99  ------ BMC1 Options
% 3.51/0.99  
% 3.51/0.99  --bmc1_incremental                      false
% 3.51/0.99  --bmc1_axioms                           reachable_all
% 3.51/0.99  --bmc1_min_bound                        0
% 3.51/0.99  --bmc1_max_bound                        -1
% 3.51/0.99  --bmc1_max_bound_default                -1
% 3.51/0.99  --bmc1_symbol_reachability              true
% 3.51/0.99  --bmc1_property_lemmas                  false
% 3.51/0.99  --bmc1_k_induction                      false
% 3.51/0.99  --bmc1_non_equiv_states                 false
% 3.51/0.99  --bmc1_deadlock                         false
% 3.51/0.99  --bmc1_ucm                              false
% 3.51/0.99  --bmc1_add_unsat_core                   none
% 3.51/0.99  --bmc1_unsat_core_children              false
% 3.51/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.99  --bmc1_out_stat                         full
% 3.51/0.99  --bmc1_ground_init                      false
% 3.51/0.99  --bmc1_pre_inst_next_state              false
% 3.51/0.99  --bmc1_pre_inst_state                   false
% 3.51/0.99  --bmc1_pre_inst_reach_state             false
% 3.51/0.99  --bmc1_out_unsat_core                   false
% 3.51/0.99  --bmc1_aig_witness_out                  false
% 3.51/0.99  --bmc1_verbose                          false
% 3.51/0.99  --bmc1_dump_clauses_tptp                false
% 3.51/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.99  --bmc1_dump_file                        -
% 3.51/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.99  --bmc1_ucm_extend_mode                  1
% 3.51/0.99  --bmc1_ucm_init_mode                    2
% 3.51/0.99  --bmc1_ucm_cone_mode                    none
% 3.51/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.99  --bmc1_ucm_relax_model                  4
% 3.51/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.99  --bmc1_ucm_layered_model                none
% 3.51/0.99  --bmc1_ucm_max_lemma_size               10
% 3.51/0.99  
% 3.51/0.99  ------ AIG Options
% 3.51/0.99  
% 3.51/0.99  --aig_mode                              false
% 3.51/0.99  
% 3.51/0.99  ------ Instantiation Options
% 3.51/0.99  
% 3.51/0.99  --instantiation_flag                    true
% 3.51/0.99  --inst_sos_flag                         false
% 3.51/0.99  --inst_sos_phase                        true
% 3.51/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel_side                     none
% 3.51/0.99  --inst_solver_per_active                1400
% 3.51/0.99  --inst_solver_calls_frac                1.
% 3.51/0.99  --inst_passive_queue_type               priority_queues
% 3.51/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.99  --inst_passive_queues_freq              [25;2]
% 3.51/0.99  --inst_dismatching                      true
% 3.51/0.99  --inst_eager_unprocessed_to_passive     true
% 3.51/0.99  --inst_prop_sim_given                   true
% 3.51/0.99  --inst_prop_sim_new                     false
% 3.51/0.99  --inst_subs_new                         false
% 3.51/0.99  --inst_eq_res_simp                      false
% 3.51/0.99  --inst_subs_given                       false
% 3.51/0.99  --inst_orphan_elimination               true
% 3.51/0.99  --inst_learning_loop_flag               true
% 3.51/0.99  --inst_learning_start                   3000
% 3.51/0.99  --inst_learning_factor                  2
% 3.51/0.99  --inst_start_prop_sim_after_learn       3
% 3.51/0.99  --inst_sel_renew                        solver
% 3.51/0.99  --inst_lit_activity_flag                true
% 3.51/0.99  --inst_restr_to_given                   false
% 3.51/0.99  --inst_activity_threshold               500
% 3.51/0.99  --inst_out_proof                        true
% 3.51/0.99  
% 3.51/0.99  ------ Resolution Options
% 3.51/0.99  
% 3.51/0.99  --resolution_flag                       false
% 3.51/0.99  --res_lit_sel                           adaptive
% 3.51/0.99  --res_lit_sel_side                      none
% 3.51/0.99  --res_ordering                          kbo
% 3.51/0.99  --res_to_prop_solver                    active
% 3.51/0.99  --res_prop_simpl_new                    false
% 3.51/0.99  --res_prop_simpl_given                  true
% 3.51/0.99  --res_passive_queue_type                priority_queues
% 3.51/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.99  --res_passive_queues_freq               [15;5]
% 3.51/0.99  --res_forward_subs                      full
% 3.51/0.99  --res_backward_subs                     full
% 3.51/0.99  --res_forward_subs_resolution           true
% 3.51/0.99  --res_backward_subs_resolution          true
% 3.51/0.99  --res_orphan_elimination                true
% 3.51/0.99  --res_time_limit                        2.
% 3.51/0.99  --res_out_proof                         true
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Options
% 3.51/0.99  
% 3.51/0.99  --superposition_flag                    true
% 3.51/0.99  --sup_passive_queue_type                priority_queues
% 3.51/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.99  --demod_completeness_check              fast
% 3.51/0.99  --demod_use_ground                      true
% 3.51/0.99  --sup_to_prop_solver                    passive
% 3.51/0.99  --sup_prop_simpl_new                    true
% 3.51/0.99  --sup_prop_simpl_given                  true
% 3.51/0.99  --sup_fun_splitting                     false
% 3.51/0.99  --sup_smt_interval                      50000
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Simplification Setup
% 3.51/0.99  
% 3.51/0.99  --sup_indices_passive                   []
% 3.51/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_full_bw                           [BwDemod]
% 3.51/0.99  --sup_immed_triv                        [TrivRules]
% 3.51/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_immed_bw_main                     []
% 3.51/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  
% 3.51/0.99  ------ Combination Options
% 3.51/0.99  
% 3.51/0.99  --comb_res_mult                         3
% 3.51/0.99  --comb_sup_mult                         2
% 3.51/0.99  --comb_inst_mult                        10
% 3.51/0.99  
% 3.51/0.99  ------ Debug Options
% 3.51/0.99  
% 3.51/0.99  --dbg_backtrace                         false
% 3.51/0.99  --dbg_dump_prop_clauses                 false
% 3.51/0.99  --dbg_dump_prop_clauses_file            -
% 3.51/0.99  --dbg_out_stat                          false
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  ------ Proving...
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  % SZS status Theorem for theBenchmark.p
% 3.51/0.99  
% 3.51/0.99   Resolution empty clause
% 3.51/0.99  
% 3.51/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.51/0.99  
% 3.51/0.99  fof(f26,conjecture,(
% 3.51/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f27,negated_conjecture,(
% 3.51/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.51/0.99    inference(negated_conjecture,[],[f26])).
% 3.51/0.99  
% 3.51/0.99  fof(f54,plain,(
% 3.51/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.51/0.99    inference(ennf_transformation,[],[f27])).
% 3.51/0.99  
% 3.51/0.99  fof(f55,plain,(
% 3.51/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.51/0.99    inference(flattening,[],[f54])).
% 3.51/0.99  
% 3.51/0.99  fof(f69,plain,(
% 3.51/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f70,plain,(
% 3.51/0.99    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.51/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f55,f69])).
% 3.51/0.99  
% 3.51/0.99  fof(f118,plain,(
% 3.51/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.51/0.99    inference(cnf_transformation,[],[f70])).
% 3.51/0.99  
% 3.51/0.99  fof(f23,axiom,(
% 3.51/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f49,plain,(
% 3.51/0.99    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f23])).
% 3.51/0.99  
% 3.51/0.99  fof(f106,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f49])).
% 3.51/0.99  
% 3.51/0.99  fof(f22,axiom,(
% 3.51/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f47,plain,(
% 3.51/0.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/0.99    inference(ennf_transformation,[],[f22])).
% 3.51/0.99  
% 3.51/0.99  fof(f48,plain,(
% 3.51/0.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/0.99    inference(flattening,[],[f47])).
% 3.51/0.99  
% 3.51/0.99  fof(f105,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.51/0.99    inference(cnf_transformation,[],[f48])).
% 3.51/0.99  
% 3.51/0.99  fof(f24,axiom,(
% 3.51/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f50,plain,(
% 3.51/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/0.99    inference(ennf_transformation,[],[f24])).
% 3.51/0.99  
% 3.51/0.99  fof(f51,plain,(
% 3.51/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/0.99    inference(flattening,[],[f50])).
% 3.51/0.99  
% 3.51/0.99  fof(f68,plain,(
% 3.51/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/0.99    inference(nnf_transformation,[],[f51])).
% 3.51/0.99  
% 3.51/0.99  fof(f107,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.51/0.99    inference(cnf_transformation,[],[f68])).
% 3.51/0.99  
% 3.51/0.99  fof(f117,plain,(
% 3.51/0.99    v1_funct_2(sK3,sK1,sK2)),
% 3.51/0.99    inference(cnf_transformation,[],[f70])).
% 3.51/0.99  
% 3.51/0.99  fof(f20,axiom,(
% 3.51/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f45,plain,(
% 3.51/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/0.99    inference(ennf_transformation,[],[f20])).
% 3.51/0.99  
% 3.51/0.99  fof(f102,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.51/0.99    inference(cnf_transformation,[],[f45])).
% 3.51/0.99  
% 3.51/0.99  fof(f18,axiom,(
% 3.51/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f43,plain,(
% 3.51/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/0.99    inference(ennf_transformation,[],[f18])).
% 3.51/0.99  
% 3.51/0.99  fof(f100,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.51/0.99    inference(cnf_transformation,[],[f43])).
% 3.51/0.99  
% 3.51/0.99  fof(f17,axiom,(
% 3.51/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f41,plain,(
% 3.51/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f17])).
% 3.51/0.99  
% 3.51/0.99  fof(f42,plain,(
% 3.51/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.51/0.99    inference(flattening,[],[f41])).
% 3.51/0.99  
% 3.51/0.99  fof(f99,plain,(
% 3.51/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f42])).
% 3.51/0.99  
% 3.51/0.99  fof(f119,plain,(
% 3.51/0.99    v2_funct_1(sK3)),
% 3.51/0.99    inference(cnf_transformation,[],[f70])).
% 3.51/0.99  
% 3.51/0.99  fof(f116,plain,(
% 3.51/0.99    v1_funct_1(sK3)),
% 3.51/0.99    inference(cnf_transformation,[],[f70])).
% 3.51/0.99  
% 3.51/0.99  fof(f25,axiom,(
% 3.51/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f52,plain,(
% 3.51/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f25])).
% 3.51/0.99  
% 3.51/0.99  fof(f53,plain,(
% 3.51/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.51/0.99    inference(flattening,[],[f52])).
% 3.51/0.99  
% 3.51/0.99  fof(f115,plain,(
% 3.51/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f53])).
% 3.51/0.99  
% 3.51/0.99  fof(f21,axiom,(
% 3.51/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f46,plain,(
% 3.51/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.51/0.99    inference(ennf_transformation,[],[f21])).
% 3.51/0.99  
% 3.51/0.99  fof(f103,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.51/0.99    inference(cnf_transformation,[],[f46])).
% 3.51/0.99  
% 3.51/0.99  fof(f120,plain,(
% 3.51/0.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.51/0.99    inference(cnf_transformation,[],[f70])).
% 3.51/0.99  
% 3.51/0.99  fof(f98,plain,(
% 3.51/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f42])).
% 3.51/0.99  
% 3.51/0.99  fof(f14,axiom,(
% 3.51/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f37,plain,(
% 3.51/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f14])).
% 3.51/0.99  
% 3.51/0.99  fof(f38,plain,(
% 3.51/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.51/0.99    inference(flattening,[],[f37])).
% 3.51/0.99  
% 3.51/0.99  fof(f94,plain,(
% 3.51/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f38])).
% 3.51/0.99  
% 3.51/0.99  fof(f93,plain,(
% 3.51/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f38])).
% 3.51/0.99  
% 3.51/0.99  fof(f11,axiom,(
% 3.51/0.99    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f35,plain,(
% 3.51/0.99    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f11])).
% 3.51/0.99  
% 3.51/0.99  fof(f89,plain,(
% 3.51/0.99    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f35])).
% 3.51/0.99  
% 3.51/0.99  fof(f114,plain,(
% 3.51/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f53])).
% 3.51/0.99  
% 3.51/0.99  fof(f121,plain,(
% 3.51/0.99    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.51/0.99    inference(cnf_transformation,[],[f70])).
% 3.51/0.99  
% 3.51/0.99  fof(f110,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.51/0.99    inference(cnf_transformation,[],[f68])).
% 3.51/0.99  
% 3.51/0.99  fof(f129,plain,(
% 3.51/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.51/0.99    inference(equality_resolution,[],[f110])).
% 3.51/0.99  
% 3.51/0.99  fof(f108,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.51/0.99    inference(cnf_transformation,[],[f68])).
% 3.51/0.99  
% 3.51/0.99  fof(f130,plain,(
% 3.51/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.51/0.99    inference(equality_resolution,[],[f108])).
% 3.51/0.99  
% 3.51/0.99  fof(f2,axiom,(
% 3.51/0.99    v1_xboole_0(k1_xboole_0)),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f74,plain,(
% 3.51/0.99    v1_xboole_0(k1_xboole_0)),
% 3.51/0.99    inference(cnf_transformation,[],[f2])).
% 3.51/0.99  
% 3.51/0.99  fof(f4,axiom,(
% 3.51/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f62,plain,(
% 3.51/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.51/0.99    inference(nnf_transformation,[],[f4])).
% 3.51/0.99  
% 3.51/0.99  fof(f63,plain,(
% 3.51/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.51/0.99    inference(flattening,[],[f62])).
% 3.51/0.99  
% 3.51/0.99  fof(f79,plain,(
% 3.51/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.51/0.99    inference(cnf_transformation,[],[f63])).
% 3.51/0.99  
% 3.51/0.99  fof(f125,plain,(
% 3.51/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.51/0.99    inference(equality_resolution,[],[f79])).
% 3.51/0.99  
% 3.51/0.99  fof(f12,axiom,(
% 3.51/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f36,plain,(
% 3.51/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f12])).
% 3.51/0.99  
% 3.51/0.99  fof(f67,plain,(
% 3.51/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.51/0.99    inference(nnf_transformation,[],[f36])).
% 3.51/0.99  
% 3.51/0.99  fof(f90,plain,(
% 3.51/0.99    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f67])).
% 3.51/0.99  
% 3.51/0.99  fof(f91,plain,(
% 3.51/0.99    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f67])).
% 3.51/0.99  
% 3.51/0.99  cnf(c_48,negated_conjecture,
% 3.51/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.51/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2135,plain,
% 3.51/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_35,plain,
% 3.51/0.99      ( v1_partfun1(X0,X1)
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/0.99      | ~ v1_xboole_0(X1) ),
% 3.51/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_33,plain,
% 3.51/0.99      ( v1_funct_2(X0,X1,X2)
% 3.51/0.99      | ~ v1_partfun1(X0,X1)
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/0.99      | ~ v1_funct_1(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_584,plain,
% 3.51/0.99      ( v1_funct_2(X0,X1,X2)
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_xboole_0(X1) ),
% 3.51/0.99      inference(resolution,[status(thm)],[c_35,c_33]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_588,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/0.99      | v1_funct_2(X0,X1,X2)
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_xboole_0(X1) ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_584,c_35,c_33]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_589,plain,
% 3.51/0.99      ( v1_funct_2(X0,X1,X2)
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_xboole_0(X1) ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_588]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_41,plain,
% 3.51/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.51/0.99      | k1_xboole_0 = X2 ),
% 3.51/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_728,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_xboole_0(X1)
% 3.51/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.51/0.99      | k1_xboole_0 = X2 ),
% 3.51/0.99      inference(resolution,[status(thm)],[c_589,c_41]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2126,plain,
% 3.51/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.51/0.99      | k1_xboole_0 = X1
% 3.51/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.51/0.99      | v1_funct_1(X2) != iProver_top
% 3.51/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3544,plain,
% 3.51/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1
% 3.51/0.99      | sK2 = k1_xboole_0
% 3.51/0.99      | v1_funct_1(sK3) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK1) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_2135,c_2126]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_49,negated_conjecture,
% 3.51/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.51/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_853,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.51/0.99      | sK1 != X1
% 3.51/0.99      | sK2 != X2
% 3.51/0.99      | sK3 != X0
% 3.51/0.99      | k1_xboole_0 = X2 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_41,c_49]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_854,plain,
% 3.51/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.51/0.99      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.51/0.99      | k1_xboole_0 = sK2 ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_853]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1075,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2609,plain,
% 3.51/0.99      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_1075]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2855,plain,
% 3.51/0.99      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_2609]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1074,plain,( X0 = X0 ),theory(equality) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2856,plain,
% 3.51/0.99      ( sK2 = sK2 ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_1074]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3743,plain,
% 3.51/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_3544,c_48,c_854,c_2855,c_2856]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_31,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2138,plain,
% 3.51/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.51/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5647,plain,
% 3.51/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_2135,c_2138]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5783,plain,
% 3.51/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3743,c_5647]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_29,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2140,plain,
% 3.51/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.51/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3654,plain,
% 3.51/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_2135,c_2140]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_27,plain,
% 3.51/0.99      ( ~ v2_funct_1(X0)
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_relat_1(X0)
% 3.51/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_47,negated_conjecture,
% 3.51/0.99      ( v2_funct_1(sK3) ),
% 3.51/0.99      inference(cnf_transformation,[],[f119]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_678,plain,
% 3.51/0.99      ( ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_relat_1(X0)
% 3.51/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.51/0.99      | sK3 != X0 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_47]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_679,plain,
% 3.51/0.99      ( ~ v1_funct_1(sK3)
% 3.51/0.99      | ~ v1_relat_1(sK3)
% 3.51/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_678]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_50,negated_conjecture,
% 3.51/0.99      ( v1_funct_1(sK3) ),
% 3.51/0.99      inference(cnf_transformation,[],[f116]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_681,plain,
% 3.51/0.99      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.51/0.99      inference(global_propositional_subsumption,[status(thm)],[c_679,c_50]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2128,plain,
% 3.51/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.51/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3699,plain,
% 3.51/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3654,c_2128]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_42,plain,
% 3.51/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_relat_1(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f115]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2136,plain,
% 3.51/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.51/0.99      | v1_funct_1(X0) != iProver_top
% 3.51/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_6035,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.51/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.51/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3699,c_2136]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_32,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2137,plain,
% 3.51/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.51/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4459,plain,
% 3.51/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_2135,c_2137]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_46,negated_conjecture,
% 3.51/0.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.51/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4471,plain,
% 3.51/0.99      ( k2_relat_1(sK3) = sK2 ),
% 3.51/0.99      inference(light_normalisation,[status(thm)],[c_4459,c_46]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_28,plain,
% 3.51/0.99      ( ~ v2_funct_1(X0)
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_relat_1(X0)
% 3.51/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_664,plain,
% 3.51/0.99      ( ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_relat_1(X0)
% 3.51/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.51/0.99      | sK3 != X0 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_47]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_665,plain,
% 3.51/0.99      ( ~ v1_funct_1(sK3)
% 3.51/0.99      | ~ v1_relat_1(sK3)
% 3.51/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_664]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_667,plain,
% 3.51/0.99      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.51/0.99      inference(global_propositional_subsumption,[status(thm)],[c_665,c_50]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2129,plain,
% 3.51/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.51/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3698,plain,
% 3.51/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3654,c_2129]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4759,plain,
% 3.51/0.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.51/0.99      inference(demodulation,[status(thm)],[c_4471,c_3698]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_6072,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.51/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.51/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.51/0.99      inference(light_normalisation,[status(thm)],[c_6035,c_4759]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_51,plain,
% 3.51/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_53,plain,
% 3.51/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_22,plain,
% 3.51/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2547,plain,
% 3.51/0.99      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2548,plain,
% 3.51/0.99      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.51/0.99      | v1_funct_1(sK3) != iProver_top
% 3.51/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2547]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_23,plain,
% 3.51/0.99      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.51/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2550,plain,
% 3.51/0.99      ( ~ v1_funct_1(sK3) | v1_relat_1(k2_funct_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2551,plain,
% 3.51/0.99      ( v1_funct_1(sK3) != iProver_top
% 3.51/0.99      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 3.51/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2550]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2564,plain,
% 3.51/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.51/0.99      | v1_relat_1(sK3) ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2565,plain,
% 3.51/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.51/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2564]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_6603,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_6072,c_51,c_53,c_2548,c_2551,c_2565]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_6610,plain,
% 3.51/0.99      ( v1_relat_1(k2_funct_1(sK3)) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_6603,c_2140]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_18,plain,
% 3.51/0.99      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2146,plain,
% 3.51/0.99      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.51/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_6737,plain,
% 3.51/0.99      ( k10_relat_1(k2_funct_1(sK3),k2_relat_1(k2_funct_1(sK3))) = k1_relat_1(k2_funct_1(sK3)) ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_6610,c_2146]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_6739,plain,
% 3.51/0.99      ( k10_relat_1(k2_funct_1(sK3),k1_relat_1(sK3)) = sK2 ),
% 3.51/0.99      inference(light_normalisation,[status(thm)],[c_6737,c_3699,c_4759]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_6745,plain,
% 3.51/0.99      ( k10_relat_1(k2_funct_1(sK3),sK1) = sK2 | sK2 = k1_xboole_0 ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_5783,c_6739]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_43,plain,
% 3.51/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_relat_1(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_45,negated_conjecture,
% 3.51/0.99      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.51/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.51/0.99      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.51/0.99      inference(cnf_transformation,[],[f121]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_970,plain,
% 3.51/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.51/0.99      | ~ v1_relat_1(X0)
% 3.51/0.99      | k2_funct_1(sK3) != X0
% 3.51/0.99      | k1_relat_1(X0) != sK2
% 3.51/0.99      | k2_relat_1(X0) != sK1 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_43,c_45]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_971,plain,
% 3.51/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.51/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.51/0.99      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.51/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.51/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_970]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_983,plain,
% 3.51/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.51/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.51/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.51/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.51/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_971,c_29]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2115,plain,
% 3.51/0.99      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.51/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.51/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_983]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_972,plain,
% 3.51/0.99      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.51/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.51/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.51/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_971]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2733,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.51/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.51/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_2115,c_51,c_53,c_972,c_2548,c_2551,c_2565]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2734,plain,
% 3.51/0.99      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.51/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_2733]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3748,plain,
% 3.51/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.51/0.99      | k2_relat_1(sK3) != sK2
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.51/0.99      inference(demodulation,[status(thm)],[c_3698,c_2734]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4223,plain,
% 3.51/0.99      ( k1_relat_1(sK3) != sK1
% 3.51/0.99      | k2_relat_1(sK3) != sK2
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.51/0.99      inference(light_normalisation,[status(thm)],[c_3748,c_3699]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4754,plain,
% 3.51/0.99      ( k1_relat_1(sK3) != sK1
% 3.51/0.99      | sK2 != sK2
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.51/0.99      inference(demodulation,[status(thm)],[c_4471,c_4223]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4777,plain,
% 3.51/0.99      ( k1_relat_1(sK3) != sK1
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.51/0.99      inference(equality_resolution_simp,[status(thm)],[c_4754]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5881,plain,
% 3.51/0.99      ( sK2 = k1_xboole_0
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_5783,c_4777]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_38,plain,
% 3.51/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.51/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.51/0.99      inference(cnf_transformation,[],[f129]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_939,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.51/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.51/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.51/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.51/0.99      | k2_funct_1(sK3) != X0
% 3.51/0.99      | sK1 != X1
% 3.51/0.99      | sK2 != k1_xboole_0 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_38,c_45]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_940,plain,
% 3.51/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.51/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.51/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.51/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.51/0.99      | sK2 != k1_xboole_0 ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_939]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_40,plain,
% 3.51/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.51/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.51/0.99      inference(cnf_transformation,[],[f130]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_775,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_xboole_0(X1)
% 3.51/0.99      | X3 != X0
% 3.51/0.99      | X4 != X2
% 3.51/0.99      | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
% 3.51/0.99      | k1_xboole_0 != X1 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_589,c_40]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_776,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.51/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_775]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3,plain,
% 3.51/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_780,plain,
% 3.51/0.99      ( ~ v1_funct_1(X0)
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.51/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.51/0.99      inference(global_propositional_subsumption,[status(thm)],[c_776,c_3]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_781,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_780]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_947,plain,
% 3.51/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.51/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.51/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.51/0.99      | sK2 != k1_xboole_0 ),
% 3.51/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_940,c_781]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2117,plain,
% 3.51/0.99      ( sK2 != k1_xboole_0
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.51/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8,plain,
% 3.51/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.51/0.99      inference(cnf_transformation,[],[f125]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2417,plain,
% 3.51/0.99      ( sK2 != k1_xboole_0
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.51/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.51/0.99      inference(demodulation,[status(thm)],[c_2117,c_8]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_157,plain,
% 3.51/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1078,plain,
% 3.51/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.51/0.99      theory(equality) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2567,plain,
% 3.51/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_1078]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2568,plain,
% 3.51/0.99      ( sK2 != X0
% 3.51/0.99      | v1_xboole_0(X0) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2567]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2570,plain,
% 3.51/0.99      ( sK2 != k1_xboole_0
% 3.51/0.99      | v1_xboole_0(sK2) = iProver_top
% 3.51/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_2568]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_824,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.51/0.99      | ~ v1_funct_1(X0)
% 3.51/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.51/0.99      | ~ v1_xboole_0(X1)
% 3.51/0.99      | k2_funct_1(sK3) != X0
% 3.51/0.99      | sK1 != X2
% 3.51/0.99      | sK2 != X1 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_589,c_45]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_825,plain,
% 3.51/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.51/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.51/0.99      | ~ v1_xboole_0(sK2) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_824]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2122,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.51/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_825]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_826,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.51/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_825]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2578,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_2122,c_51,c_53,c_826,c_2548,c_2565]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2910,plain,
% 3.51/0.99      ( sK2 != k1_xboole_0
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_2417,c_157,c_2570,c_2578]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5977,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5881,c_2910]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_6608,plain,
% 3.51/0.99      ( sK2 = k1_xboole_0
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_5783,c_6603]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9561,plain,
% 3.51/0.99      ( sK2 = k1_xboole_0 ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_6745,c_2910,c_5881,c_6608]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9576,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 3.51/0.99      inference(demodulation,[status(thm)],[c_9561,c_6603]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_20,plain,
% 3.51/0.99      ( ~ v1_relat_1(X0)
% 3.51/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.51/0.99      | k2_relat_1(X0) = k1_xboole_0 ),
% 3.51/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2144,plain,
% 3.51/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 3.51/0.99      | k2_relat_1(X0) = k1_xboole_0
% 3.51/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4110,plain,
% 3.51/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_xboole_0
% 3.51/0.99      | k2_relat_1(sK3) != k1_xboole_0
% 3.51/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3698,c_2144]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4111,plain,
% 3.51/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.51/0.99      | k2_relat_1(sK3) != k1_xboole_0
% 3.51/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.51/0.99      inference(demodulation,[status(thm)],[c_4110,c_3699]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_19,plain,
% 3.51/0.99      ( ~ v1_relat_1(X0)
% 3.51/0.99      | k1_relat_1(X0) = k1_xboole_0
% 3.51/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.51/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2686,plain,
% 3.51/0.99      ( ~ v1_relat_1(sK3)
% 3.51/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.51/0.99      | k2_relat_1(sK3) != k1_xboole_0 ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4187,plain,
% 3.51/0.99      ( k2_relat_1(sK3) != k1_xboole_0 | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_4111,c_48,c_2564,c_2686]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4188,plain,
% 3.51/0.99      ( k1_relat_1(sK3) = k1_xboole_0 | k2_relat_1(sK3) != k1_xboole_0 ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_4187]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4756,plain,
% 3.51/0.99      ( k1_relat_1(sK3) = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.51/0.99      inference(demodulation,[status(thm)],[c_4471,c_4188]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9587,plain,
% 3.51/0.99      ( k1_relat_1(sK3) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.51/0.99      inference(demodulation,[status(thm)],[c_9561,c_4756]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9661,plain,
% 3.51/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.51/0.99      inference(equality_resolution_simp,[status(thm)],[c_9587]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9697,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.51/0.99      inference(light_normalisation,[status(thm)],[c_9576,c_9661]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9699,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.51/0.99      inference(demodulation,[status(thm)],[c_9697,c_8]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9596,plain,
% 3.51/0.99      ( k1_xboole_0 != k1_xboole_0
% 3.51/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.51/0.99      inference(demodulation,[status(thm)],[c_9561,c_2910]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9644,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.51/0.99      inference(equality_resolution_simp,[status(thm)],[c_9596]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9646,plain,
% 3.51/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.51/0.99      inference(demodulation,[status(thm)],[c_9644,c_8]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9701,plain,
% 3.51/0.99      ( $false ),
% 3.51/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_9699,c_9646]) ).
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.51/0.99  
% 3.51/0.99  ------                               Statistics
% 3.51/0.99  
% 3.51/0.99  ------ General
% 3.51/0.99  
% 3.51/0.99  abstr_ref_over_cycles:                  0
% 3.51/0.99  abstr_ref_under_cycles:                 0
% 3.51/0.99  gc_basic_clause_elim:                   0
% 3.51/0.99  forced_gc_time:                         0
% 3.51/0.99  parsing_time:                           0.01
% 3.51/0.99  unif_index_cands_time:                  0.
% 3.51/0.99  unif_index_add_time:                    0.
% 3.51/0.99  orderings_time:                         0.
% 3.51/0.99  out_proof_time:                         0.011
% 3.51/0.99  total_time:                             0.283
% 3.51/0.99  num_of_symbols:                         56
% 3.51/0.99  num_of_terms:                           9041
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing
% 3.51/0.99  
% 3.51/0.99  num_of_splits:                          0
% 3.51/0.99  num_of_split_atoms:                     0
% 3.51/0.99  num_of_reused_defs:                     0
% 3.51/0.99  num_eq_ax_congr_red:                    15
% 3.51/0.99  num_of_sem_filtered_clauses:            1
% 3.51/0.99  num_of_subtypes:                        0
% 3.51/0.99  monotx_restored_types:                  0
% 3.51/0.99  sat_num_of_epr_types:                   0
% 3.51/0.99  sat_num_of_non_cyclic_types:            0
% 3.51/0.99  sat_guarded_non_collapsed_types:        0
% 3.51/0.99  num_pure_diseq_elim:                    0
% 3.51/0.99  simp_replaced_by:                       0
% 3.51/0.99  res_preprocessed:                       191
% 3.51/0.99  prep_upred:                             0
% 3.51/0.99  prep_unflattend:                        56
% 3.51/0.99  smt_new_axioms:                         0
% 3.51/0.99  pred_elim_cands:                        10
% 3.51/0.99  pred_elim:                              3
% 3.51/0.99  pred_elim_cl:                           -4
% 3.51/0.99  pred_elim_cycles:                       4
% 3.51/0.99  merged_defs:                            6
% 3.51/0.99  merged_defs_ncl:                        0
% 3.51/0.99  bin_hyper_res:                          7
% 3.51/0.99  prep_cycles:                            3
% 3.51/0.99  pred_elim_time:                         0.014
% 3.51/0.99  splitting_time:                         0.
% 3.51/0.99  sem_filter_time:                        0.
% 3.51/0.99  monotx_time:                            0.001
% 3.51/0.99  subtype_inf_time:                       0.
% 3.51/0.99  
% 3.51/0.99  ------ Problem properties
% 3.51/0.99  
% 3.51/0.99  clauses:                                52
% 3.51/0.99  conjectures:                            3
% 3.51/0.99  epr:                                    7
% 3.51/0.99  horn:                                   44
% 3.51/0.99  ground:                                 16
% 3.51/0.99  unary:                                  10
% 3.51/0.99  binary:                                 16
% 3.51/0.99  lits:                                   136
% 3.51/0.99  lits_eq:                                49
% 3.51/0.99  fd_pure:                                0
% 3.51/0.99  fd_pseudo:                              0
% 3.51/0.99  fd_cond:                                3
% 3.51/0.99  fd_pseudo_cond:                         1
% 3.51/0.99  ac_symbols:                             0
% 3.51/0.99  
% 3.51/0.99  ------ Propositional Solver
% 3.51/0.99  
% 3.51/0.99  prop_solver_calls:                      24
% 3.51/0.99  prop_fast_solver_calls:                 1427
% 3.51/0.99  smt_solver_calls:                       0
% 3.51/0.99  smt_fast_solver_calls:                  0
% 3.51/0.99  prop_num_of_clauses:                    3554
% 3.51/0.99  prop_preprocess_simplified:             11738
% 3.51/0.99  prop_fo_subsumed:                       41
% 3.51/0.99  prop_solver_time:                       0.
% 3.51/0.99  smt_solver_time:                        0.
% 3.51/0.99  smt_fast_solver_time:                   0.
% 3.51/0.99  prop_fast_solver_time:                  0.
% 3.51/0.99  prop_unsat_core_time:                   0.
% 3.51/0.99  
% 3.51/0.99  ------ QBF
% 3.51/0.99  
% 3.51/0.99  qbf_q_res:                              0
% 3.51/0.99  qbf_num_tautologies:                    0
% 3.51/0.99  qbf_prep_cycles:                        0
% 3.51/0.99  
% 3.51/0.99  ------ BMC1
% 3.51/0.99  
% 3.51/0.99  bmc1_current_bound:                     -1
% 3.51/0.99  bmc1_last_solved_bound:                 -1
% 3.51/0.99  bmc1_unsat_core_size:                   -1
% 3.51/0.99  bmc1_unsat_core_parents_size:           -1
% 3.51/0.99  bmc1_merge_next_fun:                    0
% 3.51/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.51/0.99  
% 3.51/0.99  ------ Instantiation
% 3.51/0.99  
% 3.51/0.99  inst_num_of_clauses:                    1193
% 3.51/0.99  inst_num_in_passive:                    659
% 3.51/0.99  inst_num_in_active:                     533
% 3.51/0.99  inst_num_in_unprocessed:                1
% 3.51/0.99  inst_num_of_loops:                      620
% 3.51/0.99  inst_num_of_learning_restarts:          0
% 3.51/0.99  inst_num_moves_active_passive:          84
% 3.51/0.99  inst_lit_activity:                      0
% 3.51/0.99  inst_lit_activity_moves:                0
% 3.51/0.99  inst_num_tautologies:                   0
% 3.51/0.99  inst_num_prop_implied:                  0
% 3.51/0.99  inst_num_existing_simplified:           0
% 3.51/0.99  inst_num_eq_res_simplified:             0
% 3.51/0.99  inst_num_child_elim:                    0
% 3.51/0.99  inst_num_of_dismatching_blockings:      301
% 3.51/0.99  inst_num_of_non_proper_insts:           957
% 3.51/0.99  inst_num_of_duplicates:                 0
% 3.51/0.99  inst_inst_num_from_inst_to_res:         0
% 3.51/0.99  inst_dismatching_checking_time:         0.
% 3.51/0.99  
% 3.51/0.99  ------ Resolution
% 3.51/0.99  
% 3.51/0.99  res_num_of_clauses:                     0
% 3.51/0.99  res_num_in_passive:                     0
% 3.51/0.99  res_num_in_active:                      0
% 3.51/0.99  res_num_of_loops:                       194
% 3.51/0.99  res_forward_subset_subsumed:            46
% 3.51/0.99  res_backward_subset_subsumed:           2
% 3.51/0.99  res_forward_subsumed:                   1
% 3.51/0.99  res_backward_subsumed:                  0
% 3.51/0.99  res_forward_subsumption_resolution:     3
% 3.51/0.99  res_backward_subsumption_resolution:    0
% 3.51/0.99  res_clause_to_clause_subsumption:       322
% 3.51/0.99  res_orphan_elimination:                 0
% 3.51/0.99  res_tautology_del:                      90
% 3.51/0.99  res_num_eq_res_simplified:              0
% 3.51/0.99  res_num_sel_changes:                    0
% 3.51/0.99  res_moves_from_active_to_pass:          0
% 3.51/0.99  
% 3.51/0.99  ------ Superposition
% 3.51/0.99  
% 3.51/0.99  sup_time_total:                         0.
% 3.51/0.99  sup_time_generating:                    0.
% 3.51/0.99  sup_time_sim_full:                      0.
% 3.51/0.99  sup_time_sim_immed:                     0.
% 3.51/0.99  
% 3.51/0.99  sup_num_of_clauses:                     103
% 3.51/0.99  sup_num_in_active:                      69
% 3.51/0.99  sup_num_in_passive:                     34
% 3.51/0.99  sup_num_of_loops:                       122
% 3.51/0.99  sup_fw_superposition:                   105
% 3.51/0.99  sup_bw_superposition:                   49
% 3.51/0.99  sup_immediate_simplified:               37
% 3.51/0.99  sup_given_eliminated:                   0
% 3.51/0.99  comparisons_done:                       0
% 3.51/0.99  comparisons_avoided:                    10
% 3.51/0.99  
% 3.51/0.99  ------ Simplifications
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  sim_fw_subset_subsumed:                 12
% 3.51/0.99  sim_bw_subset_subsumed:                 10
% 3.51/0.99  sim_fw_subsumed:                        3
% 3.51/0.99  sim_bw_subsumed:                        5
% 3.51/0.99  sim_fw_subsumption_res:                 5
% 3.51/0.99  sim_bw_subsumption_res:                 1
% 3.51/0.99  sim_tautology_del:                      3
% 3.51/0.99  sim_eq_tautology_del:                   14
% 3.51/0.99  sim_eq_res_simp:                        4
% 3.51/0.99  sim_fw_demodulated:                     21
% 3.51/0.99  sim_bw_demodulated:                     52
% 3.51/0.99  sim_light_normalised:                   27
% 3.51/0.99  sim_joinable_taut:                      0
% 3.51/0.99  sim_joinable_simp:                      0
% 3.51/0.99  sim_ac_normalised:                      0
% 3.51/0.99  sim_smt_subsumption:                    0
% 3.51/0.99  
%------------------------------------------------------------------------------

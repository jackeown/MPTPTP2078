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

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  206 (6192 expanded)
%              Number of clauses        :  126 (2097 expanded)
%              Number of leaves         :   20 (1167 expanded)
%              Depth                    :   26
%              Number of atoms          :  586 (31985 expanded)
%              Number of equality atoms :  281 (6348 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f57,plain,(
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

fof(f58,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f57])).

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
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & k2_relset_1(sK1,sK2,sK3) = sK2
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f58,f68])).

fof(f114,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f69])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f92,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f115,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f112,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
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

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f54])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f125,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f106])).

fof(f117,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f69])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f65])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f121,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f94,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f113,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f98,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f111,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f116,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f69])).

fof(f97,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f110,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f60,f61])).

fof(f71,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f120,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1699,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1703,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3817,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1699,c_1703])).

cnf(c_22,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_44,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_590,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_44])).

cnf(c_591,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_593,plain,
    ( ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_47])).

cnf(c_1691,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_4015,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3817,c_1691])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_42,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_754,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_42])).

cnf(c_755,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_754])).

cnf(c_1685,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1959,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1685,c_8])).

cnf(c_48,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_23,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2071,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2072,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2071])).

cnf(c_2080,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2295,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2080])).

cnf(c_2296,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2295])).

cnf(c_2470,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1959,c_48,c_50,c_2072,c_2296])).

cnf(c_2471,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2470])).

cnf(c_4304,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4015,c_2471])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_826,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_46])).

cnf(c_827,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_826])).

cnf(c_829,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_827,c_45])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1702,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4743,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1699,c_1702])).

cnf(c_4794,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_829,c_4743])).

cnf(c_27,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_576,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_44])).

cnf(c_577,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_579,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_577,c_47])).

cnf(c_1692,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_4014,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3817,c_1692])).

cnf(c_4018,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_4014,c_4015])).

cnf(c_39,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1700,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5534,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4018,c_1700])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1701,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3868,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1699,c_1701])).

cnf(c_43,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3880,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3868,c_43])).

cnf(c_28,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_562,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_44])).

cnf(c_563,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_565,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_563,c_47])).

cnf(c_1693,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_3889,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3880,c_1693])).

cnf(c_4293,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3889,c_50,c_2296])).

cnf(c_4303,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4015,c_4293])).

cnf(c_5535,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5534,c_4303])).

cnf(c_24,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1706,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5168,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4015,c_1706])).

cnf(c_1707,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5211,plain,
    ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4015,c_1707])).

cnf(c_7680,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5535,c_48,c_50,c_2296,c_5168,c_5211])).

cnf(c_7685,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4794,c_7680])).

cnf(c_40,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_837,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k2_relat_1(X0) != sK1
    | k1_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_42])).

cnf(c_838,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_837])).

cnf(c_850,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_838,c_30])).

cnf(c_1681,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_855,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_2369,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1681,c_48,c_50,c_855,c_2072,c_2296])).

cnf(c_2370,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2369])).

cnf(c_4296,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4293,c_2370])).

cnf(c_4855,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4296])).

cnf(c_4857,plain,
    ( k2_relat_1(k4_relat_1(sK3)) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4855,c_4015])).

cnf(c_5532,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4018,c_4857])).

cnf(c_7716,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7685,c_4794,c_5532])).

cnf(c_7719,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7716,c_7680])).

cnf(c_7858,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7719,c_8])).

cnf(c_9849,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4304,c_4794,c_5532,c_7685,c_7858])).

cnf(c_9850,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9849])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1722,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1717,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_29,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1704,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3215,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_1704])).

cnf(c_3264,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1722,c_3215])).

cnf(c_15,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1711,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1720,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2932,plain,
    ( k4_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1711,c_1720])).

cnf(c_3375,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3264,c_2932])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1714,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5775,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1699,c_1714])).

cnf(c_7733,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7716,c_5775])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_7811,plain,
    ( m1_subset_1(X0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7733,c_7])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1716,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5830,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1699,c_1716])).

cnf(c_7732,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7716,c_5830])).

cnf(c_7816,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7732,c_7])).

cnf(c_8643,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7811,c_3215,c_7816])).

cnf(c_8648,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1722,c_8643])).

cnf(c_9366,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8648,c_1720])).

cnf(c_9853,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9850,c_3375,c_7716,c_9366])).

cnf(c_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1715,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4742,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1715,c_1702])).

cnf(c_9854,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9853,c_8,c_4742])).

cnf(c_9857,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9854,c_1715])).

cnf(c_7743,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7716,c_4303])).

cnf(c_9375,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9366,c_7743])).

cnf(c_9434,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9375,c_3375])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9857,c_9434])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.82/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.00  
% 3.82/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.82/1.00  
% 3.82/1.00  ------  iProver source info
% 3.82/1.00  
% 3.82/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.82/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.82/1.00  git: non_committed_changes: false
% 3.82/1.00  git: last_make_outside_of_git: false
% 3.82/1.00  
% 3.82/1.00  ------ 
% 3.82/1.00  
% 3.82/1.00  ------ Input Options
% 3.82/1.00  
% 3.82/1.00  --out_options                           all
% 3.82/1.00  --tptp_safe_out                         true
% 3.82/1.00  --problem_path                          ""
% 3.82/1.00  --include_path                          ""
% 3.82/1.00  --clausifier                            res/vclausify_rel
% 3.82/1.00  --clausifier_options                    --mode clausify
% 3.82/1.00  --stdin                                 false
% 3.82/1.00  --stats_out                             all
% 3.82/1.00  
% 3.82/1.00  ------ General Options
% 3.82/1.00  
% 3.82/1.00  --fof                                   false
% 3.82/1.00  --time_out_real                         305.
% 3.82/1.00  --time_out_virtual                      -1.
% 3.82/1.00  --symbol_type_check                     false
% 3.82/1.00  --clausify_out                          false
% 3.82/1.00  --sig_cnt_out                           false
% 3.82/1.00  --trig_cnt_out                          false
% 3.82/1.00  --trig_cnt_out_tolerance                1.
% 3.82/1.00  --trig_cnt_out_sk_spl                   false
% 3.82/1.00  --abstr_cl_out                          false
% 3.82/1.00  
% 3.82/1.00  ------ Global Options
% 3.82/1.00  
% 3.82/1.00  --schedule                              default
% 3.82/1.00  --add_important_lit                     false
% 3.82/1.00  --prop_solver_per_cl                    1000
% 3.82/1.00  --min_unsat_core                        false
% 3.82/1.00  --soft_assumptions                      false
% 3.82/1.00  --soft_lemma_size                       3
% 3.82/1.00  --prop_impl_unit_size                   0
% 3.82/1.00  --prop_impl_unit                        []
% 3.82/1.00  --share_sel_clauses                     true
% 3.82/1.00  --reset_solvers                         false
% 3.82/1.00  --bc_imp_inh                            [conj_cone]
% 3.82/1.00  --conj_cone_tolerance                   3.
% 3.82/1.00  --extra_neg_conj                        none
% 3.82/1.00  --large_theory_mode                     true
% 3.82/1.00  --prolific_symb_bound                   200
% 3.82/1.00  --lt_threshold                          2000
% 3.82/1.00  --clause_weak_htbl                      true
% 3.82/1.00  --gc_record_bc_elim                     false
% 3.82/1.00  
% 3.82/1.00  ------ Preprocessing Options
% 3.82/1.00  
% 3.82/1.00  --preprocessing_flag                    true
% 3.82/1.00  --time_out_prep_mult                    0.1
% 3.82/1.00  --splitting_mode                        input
% 3.82/1.00  --splitting_grd                         true
% 3.82/1.00  --splitting_cvd                         false
% 3.82/1.00  --splitting_cvd_svl                     false
% 3.82/1.00  --splitting_nvd                         32
% 3.82/1.00  --sub_typing                            true
% 3.82/1.00  --prep_gs_sim                           true
% 3.82/1.00  --prep_unflatten                        true
% 3.82/1.00  --prep_res_sim                          true
% 3.82/1.00  --prep_upred                            true
% 3.82/1.00  --prep_sem_filter                       exhaustive
% 3.82/1.00  --prep_sem_filter_out                   false
% 3.82/1.00  --pred_elim                             true
% 3.82/1.00  --res_sim_input                         true
% 3.82/1.00  --eq_ax_congr_red                       true
% 3.82/1.00  --pure_diseq_elim                       true
% 3.82/1.00  --brand_transform                       false
% 3.82/1.00  --non_eq_to_eq                          false
% 3.82/1.00  --prep_def_merge                        true
% 3.82/1.00  --prep_def_merge_prop_impl              false
% 3.82/1.00  --prep_def_merge_mbd                    true
% 3.82/1.00  --prep_def_merge_tr_red                 false
% 3.82/1.00  --prep_def_merge_tr_cl                  false
% 3.82/1.00  --smt_preprocessing                     true
% 3.82/1.00  --smt_ac_axioms                         fast
% 3.82/1.00  --preprocessed_out                      false
% 3.82/1.00  --preprocessed_stats                    false
% 3.82/1.00  
% 3.82/1.00  ------ Abstraction refinement Options
% 3.82/1.00  
% 3.82/1.00  --abstr_ref                             []
% 3.82/1.00  --abstr_ref_prep                        false
% 3.82/1.00  --abstr_ref_until_sat                   false
% 3.82/1.00  --abstr_ref_sig_restrict                funpre
% 3.82/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.82/1.00  --abstr_ref_under                       []
% 3.82/1.00  
% 3.82/1.00  ------ SAT Options
% 3.82/1.00  
% 3.82/1.00  --sat_mode                              false
% 3.82/1.00  --sat_fm_restart_options                ""
% 3.82/1.00  --sat_gr_def                            false
% 3.82/1.00  --sat_epr_types                         true
% 3.82/1.00  --sat_non_cyclic_types                  false
% 3.82/1.00  --sat_finite_models                     false
% 3.82/1.00  --sat_fm_lemmas                         false
% 3.82/1.00  --sat_fm_prep                           false
% 3.82/1.00  --sat_fm_uc_incr                        true
% 3.82/1.00  --sat_out_model                         small
% 3.82/1.00  --sat_out_clauses                       false
% 3.82/1.00  
% 3.82/1.00  ------ QBF Options
% 3.82/1.00  
% 3.82/1.00  --qbf_mode                              false
% 3.82/1.00  --qbf_elim_univ                         false
% 3.82/1.00  --qbf_dom_inst                          none
% 3.82/1.00  --qbf_dom_pre_inst                      false
% 3.82/1.00  --qbf_sk_in                             false
% 3.82/1.00  --qbf_pred_elim                         true
% 3.82/1.00  --qbf_split                             512
% 3.82/1.00  
% 3.82/1.00  ------ BMC1 Options
% 3.82/1.00  
% 3.82/1.00  --bmc1_incremental                      false
% 3.82/1.00  --bmc1_axioms                           reachable_all
% 3.82/1.00  --bmc1_min_bound                        0
% 3.82/1.00  --bmc1_max_bound                        -1
% 3.82/1.00  --bmc1_max_bound_default                -1
% 3.82/1.00  --bmc1_symbol_reachability              true
% 3.82/1.00  --bmc1_property_lemmas                  false
% 3.82/1.00  --bmc1_k_induction                      false
% 3.82/1.00  --bmc1_non_equiv_states                 false
% 3.82/1.00  --bmc1_deadlock                         false
% 3.82/1.00  --bmc1_ucm                              false
% 3.82/1.00  --bmc1_add_unsat_core                   none
% 3.82/1.00  --bmc1_unsat_core_children              false
% 3.82/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.82/1.00  --bmc1_out_stat                         full
% 3.82/1.00  --bmc1_ground_init                      false
% 3.82/1.00  --bmc1_pre_inst_next_state              false
% 3.82/1.00  --bmc1_pre_inst_state                   false
% 3.82/1.00  --bmc1_pre_inst_reach_state             false
% 3.82/1.00  --bmc1_out_unsat_core                   false
% 3.82/1.00  --bmc1_aig_witness_out                  false
% 3.82/1.00  --bmc1_verbose                          false
% 3.82/1.00  --bmc1_dump_clauses_tptp                false
% 3.82/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.82/1.00  --bmc1_dump_file                        -
% 3.82/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.82/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.82/1.00  --bmc1_ucm_extend_mode                  1
% 3.82/1.00  --bmc1_ucm_init_mode                    2
% 3.82/1.00  --bmc1_ucm_cone_mode                    none
% 3.82/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.82/1.00  --bmc1_ucm_relax_model                  4
% 3.82/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.82/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.82/1.00  --bmc1_ucm_layered_model                none
% 3.82/1.00  --bmc1_ucm_max_lemma_size               10
% 3.82/1.00  
% 3.82/1.00  ------ AIG Options
% 3.82/1.00  
% 3.82/1.00  --aig_mode                              false
% 3.82/1.00  
% 3.82/1.00  ------ Instantiation Options
% 3.82/1.00  
% 3.82/1.00  --instantiation_flag                    true
% 3.82/1.00  --inst_sos_flag                         false
% 3.82/1.00  --inst_sos_phase                        true
% 3.82/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.82/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.82/1.00  --inst_lit_sel_side                     num_symb
% 3.82/1.00  --inst_solver_per_active                1400
% 3.82/1.00  --inst_solver_calls_frac                1.
% 3.82/1.00  --inst_passive_queue_type               priority_queues
% 3.82/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.82/1.00  --inst_passive_queues_freq              [25;2]
% 3.82/1.00  --inst_dismatching                      true
% 3.82/1.00  --inst_eager_unprocessed_to_passive     true
% 3.82/1.00  --inst_prop_sim_given                   true
% 3.82/1.00  --inst_prop_sim_new                     false
% 3.82/1.00  --inst_subs_new                         false
% 3.82/1.00  --inst_eq_res_simp                      false
% 3.82/1.00  --inst_subs_given                       false
% 3.82/1.00  --inst_orphan_elimination               true
% 3.82/1.00  --inst_learning_loop_flag               true
% 3.82/1.00  --inst_learning_start                   3000
% 3.82/1.00  --inst_learning_factor                  2
% 3.82/1.00  --inst_start_prop_sim_after_learn       3
% 3.82/1.00  --inst_sel_renew                        solver
% 3.82/1.00  --inst_lit_activity_flag                true
% 3.82/1.00  --inst_restr_to_given                   false
% 3.82/1.00  --inst_activity_threshold               500
% 3.82/1.00  --inst_out_proof                        true
% 3.82/1.00  
% 3.82/1.00  ------ Resolution Options
% 3.82/1.00  
% 3.82/1.00  --resolution_flag                       true
% 3.82/1.00  --res_lit_sel                           adaptive
% 3.82/1.00  --res_lit_sel_side                      none
% 3.82/1.00  --res_ordering                          kbo
% 3.82/1.00  --res_to_prop_solver                    active
% 3.82/1.00  --res_prop_simpl_new                    false
% 3.82/1.00  --res_prop_simpl_given                  true
% 3.82/1.00  --res_passive_queue_type                priority_queues
% 3.82/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.82/1.00  --res_passive_queues_freq               [15;5]
% 3.82/1.00  --res_forward_subs                      full
% 3.82/1.00  --res_backward_subs                     full
% 3.82/1.00  --res_forward_subs_resolution           true
% 3.82/1.00  --res_backward_subs_resolution          true
% 3.82/1.00  --res_orphan_elimination                true
% 3.82/1.00  --res_time_limit                        2.
% 3.82/1.00  --res_out_proof                         true
% 3.82/1.00  
% 3.82/1.00  ------ Superposition Options
% 3.82/1.00  
% 3.82/1.00  --superposition_flag                    true
% 3.82/1.00  --sup_passive_queue_type                priority_queues
% 3.82/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.82/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.82/1.00  --demod_completeness_check              fast
% 3.82/1.00  --demod_use_ground                      true
% 3.82/1.00  --sup_to_prop_solver                    passive
% 3.82/1.00  --sup_prop_simpl_new                    true
% 3.82/1.00  --sup_prop_simpl_given                  true
% 3.82/1.00  --sup_fun_splitting                     false
% 3.82/1.00  --sup_smt_interval                      50000
% 3.82/1.00  
% 3.82/1.00  ------ Superposition Simplification Setup
% 3.82/1.00  
% 3.82/1.00  --sup_indices_passive                   []
% 3.82/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.82/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.82/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.82/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.82/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.82/1.00  --sup_full_bw                           [BwDemod]
% 3.82/1.00  --sup_immed_triv                        [TrivRules]
% 3.82/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.82/1.00  --sup_immed_bw_main                     []
% 3.82/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.82/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.82/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.82/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.82/1.00  
% 3.82/1.00  ------ Combination Options
% 3.82/1.00  
% 3.82/1.00  --comb_res_mult                         3
% 3.82/1.00  --comb_sup_mult                         2
% 3.82/1.00  --comb_inst_mult                        10
% 3.82/1.00  
% 3.82/1.00  ------ Debug Options
% 3.82/1.00  
% 3.82/1.00  --dbg_backtrace                         false
% 3.82/1.00  --dbg_dump_prop_clauses                 false
% 3.82/1.00  --dbg_dump_prop_clauses_file            -
% 3.82/1.00  --dbg_out_stat                          false
% 3.82/1.00  ------ Parsing...
% 3.82/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.82/1.00  
% 3.82/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.82/1.00  
% 3.82/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.82/1.00  
% 3.82/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/1.00  ------ Proving...
% 3.82/1.00  ------ Problem Properties 
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  clauses                                 48
% 3.82/1.00  conjectures                             3
% 3.82/1.00  EPR                                     9
% 3.82/1.00  Horn                                    42
% 3.82/1.00  unary                                   8
% 3.82/1.00  binary                                  20
% 3.82/1.00  lits                                    121
% 3.82/1.00  lits eq                                 46
% 3.82/1.00  fd_pure                                 0
% 3.82/1.00  fd_pseudo                               0
% 3.82/1.00  fd_cond                                 3
% 3.82/1.00  fd_pseudo_cond                          1
% 3.82/1.00  AC symbols                              0
% 3.82/1.00  
% 3.82/1.00  ------ Schedule dynamic 5 is on 
% 3.82/1.00  
% 3.82/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  ------ 
% 3.82/1.00  Current options:
% 3.82/1.00  ------ 
% 3.82/1.00  
% 3.82/1.00  ------ Input Options
% 3.82/1.00  
% 3.82/1.00  --out_options                           all
% 3.82/1.00  --tptp_safe_out                         true
% 3.82/1.00  --problem_path                          ""
% 3.82/1.00  --include_path                          ""
% 3.82/1.00  --clausifier                            res/vclausify_rel
% 3.82/1.00  --clausifier_options                    --mode clausify
% 3.82/1.00  --stdin                                 false
% 3.82/1.00  --stats_out                             all
% 3.82/1.00  
% 3.82/1.00  ------ General Options
% 3.82/1.00  
% 3.82/1.00  --fof                                   false
% 3.82/1.00  --time_out_real                         305.
% 3.82/1.00  --time_out_virtual                      -1.
% 3.82/1.00  --symbol_type_check                     false
% 3.82/1.00  --clausify_out                          false
% 3.82/1.00  --sig_cnt_out                           false
% 3.82/1.00  --trig_cnt_out                          false
% 3.82/1.00  --trig_cnt_out_tolerance                1.
% 3.82/1.00  --trig_cnt_out_sk_spl                   false
% 3.82/1.00  --abstr_cl_out                          false
% 3.82/1.00  
% 3.82/1.00  ------ Global Options
% 3.82/1.00  
% 3.82/1.00  --schedule                              default
% 3.82/1.00  --add_important_lit                     false
% 3.82/1.00  --prop_solver_per_cl                    1000
% 3.82/1.00  --min_unsat_core                        false
% 3.82/1.00  --soft_assumptions                      false
% 3.82/1.00  --soft_lemma_size                       3
% 3.82/1.00  --prop_impl_unit_size                   0
% 3.82/1.00  --prop_impl_unit                        []
% 3.82/1.00  --share_sel_clauses                     true
% 3.82/1.00  --reset_solvers                         false
% 3.82/1.00  --bc_imp_inh                            [conj_cone]
% 3.82/1.00  --conj_cone_tolerance                   3.
% 3.82/1.00  --extra_neg_conj                        none
% 3.82/1.00  --large_theory_mode                     true
% 3.82/1.00  --prolific_symb_bound                   200
% 3.82/1.00  --lt_threshold                          2000
% 3.82/1.00  --clause_weak_htbl                      true
% 3.82/1.00  --gc_record_bc_elim                     false
% 3.82/1.00  
% 3.82/1.00  ------ Preprocessing Options
% 3.82/1.00  
% 3.82/1.00  --preprocessing_flag                    true
% 3.82/1.00  --time_out_prep_mult                    0.1
% 3.82/1.00  --splitting_mode                        input
% 3.82/1.00  --splitting_grd                         true
% 3.82/1.00  --splitting_cvd                         false
% 3.82/1.00  --splitting_cvd_svl                     false
% 3.82/1.00  --splitting_nvd                         32
% 3.82/1.00  --sub_typing                            true
% 3.82/1.00  --prep_gs_sim                           true
% 3.82/1.00  --prep_unflatten                        true
% 3.82/1.00  --prep_res_sim                          true
% 3.82/1.00  --prep_upred                            true
% 3.82/1.00  --prep_sem_filter                       exhaustive
% 3.82/1.00  --prep_sem_filter_out                   false
% 3.82/1.00  --pred_elim                             true
% 3.82/1.00  --res_sim_input                         true
% 3.82/1.00  --eq_ax_congr_red                       true
% 3.82/1.00  --pure_diseq_elim                       true
% 3.82/1.00  --brand_transform                       false
% 3.82/1.00  --non_eq_to_eq                          false
% 3.82/1.00  --prep_def_merge                        true
% 3.82/1.00  --prep_def_merge_prop_impl              false
% 3.82/1.00  --prep_def_merge_mbd                    true
% 3.82/1.00  --prep_def_merge_tr_red                 false
% 3.82/1.00  --prep_def_merge_tr_cl                  false
% 3.82/1.00  --smt_preprocessing                     true
% 3.82/1.00  --smt_ac_axioms                         fast
% 3.82/1.00  --preprocessed_out                      false
% 3.82/1.00  --preprocessed_stats                    false
% 3.82/1.00  
% 3.82/1.00  ------ Abstraction refinement Options
% 3.82/1.00  
% 3.82/1.00  --abstr_ref                             []
% 3.82/1.00  --abstr_ref_prep                        false
% 3.82/1.00  --abstr_ref_until_sat                   false
% 3.82/1.00  --abstr_ref_sig_restrict                funpre
% 3.82/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.82/1.00  --abstr_ref_under                       []
% 3.82/1.00  
% 3.82/1.00  ------ SAT Options
% 3.82/1.00  
% 3.82/1.00  --sat_mode                              false
% 3.82/1.00  --sat_fm_restart_options                ""
% 3.82/1.00  --sat_gr_def                            false
% 3.82/1.00  --sat_epr_types                         true
% 3.82/1.00  --sat_non_cyclic_types                  false
% 3.82/1.00  --sat_finite_models                     false
% 3.82/1.00  --sat_fm_lemmas                         false
% 3.82/1.00  --sat_fm_prep                           false
% 3.82/1.00  --sat_fm_uc_incr                        true
% 3.82/1.00  --sat_out_model                         small
% 3.82/1.00  --sat_out_clauses                       false
% 3.82/1.00  
% 3.82/1.00  ------ QBF Options
% 3.82/1.00  
% 3.82/1.00  --qbf_mode                              false
% 3.82/1.00  --qbf_elim_univ                         false
% 3.82/1.00  --qbf_dom_inst                          none
% 3.82/1.00  --qbf_dom_pre_inst                      false
% 3.82/1.00  --qbf_sk_in                             false
% 3.82/1.00  --qbf_pred_elim                         true
% 3.82/1.00  --qbf_split                             512
% 3.82/1.00  
% 3.82/1.00  ------ BMC1 Options
% 3.82/1.00  
% 3.82/1.00  --bmc1_incremental                      false
% 3.82/1.00  --bmc1_axioms                           reachable_all
% 3.82/1.00  --bmc1_min_bound                        0
% 3.82/1.00  --bmc1_max_bound                        -1
% 3.82/1.00  --bmc1_max_bound_default                -1
% 3.82/1.00  --bmc1_symbol_reachability              true
% 3.82/1.00  --bmc1_property_lemmas                  false
% 3.82/1.00  --bmc1_k_induction                      false
% 3.82/1.00  --bmc1_non_equiv_states                 false
% 3.82/1.00  --bmc1_deadlock                         false
% 3.82/1.00  --bmc1_ucm                              false
% 3.82/1.00  --bmc1_add_unsat_core                   none
% 3.82/1.00  --bmc1_unsat_core_children              false
% 3.82/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.82/1.00  --bmc1_out_stat                         full
% 3.82/1.00  --bmc1_ground_init                      false
% 3.82/1.00  --bmc1_pre_inst_next_state              false
% 3.82/1.00  --bmc1_pre_inst_state                   false
% 3.82/1.00  --bmc1_pre_inst_reach_state             false
% 3.82/1.00  --bmc1_out_unsat_core                   false
% 3.82/1.00  --bmc1_aig_witness_out                  false
% 3.82/1.00  --bmc1_verbose                          false
% 3.82/1.00  --bmc1_dump_clauses_tptp                false
% 3.82/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.82/1.00  --bmc1_dump_file                        -
% 3.82/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.82/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.82/1.00  --bmc1_ucm_extend_mode                  1
% 3.82/1.00  --bmc1_ucm_init_mode                    2
% 3.82/1.00  --bmc1_ucm_cone_mode                    none
% 3.82/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.82/1.00  --bmc1_ucm_relax_model                  4
% 3.82/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.82/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.82/1.00  --bmc1_ucm_layered_model                none
% 3.82/1.00  --bmc1_ucm_max_lemma_size               10
% 3.82/1.00  
% 3.82/1.00  ------ AIG Options
% 3.82/1.00  
% 3.82/1.00  --aig_mode                              false
% 3.82/1.00  
% 3.82/1.00  ------ Instantiation Options
% 3.82/1.00  
% 3.82/1.00  --instantiation_flag                    true
% 3.82/1.00  --inst_sos_flag                         false
% 3.82/1.00  --inst_sos_phase                        true
% 3.82/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.82/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.82/1.00  --inst_lit_sel_side                     none
% 3.82/1.00  --inst_solver_per_active                1400
% 3.82/1.00  --inst_solver_calls_frac                1.
% 3.82/1.00  --inst_passive_queue_type               priority_queues
% 3.82/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.82/1.00  --inst_passive_queues_freq              [25;2]
% 3.82/1.00  --inst_dismatching                      true
% 3.82/1.00  --inst_eager_unprocessed_to_passive     true
% 3.82/1.00  --inst_prop_sim_given                   true
% 3.82/1.00  --inst_prop_sim_new                     false
% 3.82/1.00  --inst_subs_new                         false
% 3.82/1.00  --inst_eq_res_simp                      false
% 3.82/1.00  --inst_subs_given                       false
% 3.82/1.00  --inst_orphan_elimination               true
% 3.82/1.00  --inst_learning_loop_flag               true
% 3.82/1.00  --inst_learning_start                   3000
% 3.82/1.00  --inst_learning_factor                  2
% 3.82/1.00  --inst_start_prop_sim_after_learn       3
% 3.82/1.00  --inst_sel_renew                        solver
% 3.82/1.00  --inst_lit_activity_flag                true
% 3.82/1.00  --inst_restr_to_given                   false
% 3.82/1.00  --inst_activity_threshold               500
% 3.82/1.00  --inst_out_proof                        true
% 3.82/1.00  
% 3.82/1.00  ------ Resolution Options
% 3.82/1.00  
% 3.82/1.00  --resolution_flag                       false
% 3.82/1.00  --res_lit_sel                           adaptive
% 3.82/1.00  --res_lit_sel_side                      none
% 3.82/1.00  --res_ordering                          kbo
% 3.82/1.00  --res_to_prop_solver                    active
% 3.82/1.00  --res_prop_simpl_new                    false
% 3.82/1.00  --res_prop_simpl_given                  true
% 3.82/1.00  --res_passive_queue_type                priority_queues
% 3.82/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.82/1.00  --res_passive_queues_freq               [15;5]
% 3.82/1.00  --res_forward_subs                      full
% 3.82/1.00  --res_backward_subs                     full
% 3.82/1.00  --res_forward_subs_resolution           true
% 3.82/1.00  --res_backward_subs_resolution          true
% 3.82/1.00  --res_orphan_elimination                true
% 3.82/1.00  --res_time_limit                        2.
% 3.82/1.00  --res_out_proof                         true
% 3.82/1.00  
% 3.82/1.00  ------ Superposition Options
% 3.82/1.00  
% 3.82/1.00  --superposition_flag                    true
% 3.82/1.00  --sup_passive_queue_type                priority_queues
% 3.82/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.82/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.82/1.00  --demod_completeness_check              fast
% 3.82/1.00  --demod_use_ground                      true
% 3.82/1.00  --sup_to_prop_solver                    passive
% 3.82/1.00  --sup_prop_simpl_new                    true
% 3.82/1.00  --sup_prop_simpl_given                  true
% 3.82/1.00  --sup_fun_splitting                     false
% 3.82/1.00  --sup_smt_interval                      50000
% 3.82/1.00  
% 3.82/1.00  ------ Superposition Simplification Setup
% 3.82/1.00  
% 3.82/1.00  --sup_indices_passive                   []
% 3.82/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.82/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.82/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.82/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.82/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.82/1.00  --sup_full_bw                           [BwDemod]
% 3.82/1.00  --sup_immed_triv                        [TrivRules]
% 3.82/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.82/1.00  --sup_immed_bw_main                     []
% 3.82/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.82/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.82/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.82/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.82/1.00  
% 3.82/1.00  ------ Combination Options
% 3.82/1.00  
% 3.82/1.00  --comb_res_mult                         3
% 3.82/1.00  --comb_sup_mult                         2
% 3.82/1.00  --comb_inst_mult                        10
% 3.82/1.00  
% 3.82/1.00  ------ Debug Options
% 3.82/1.00  
% 3.82/1.00  --dbg_backtrace                         false
% 3.82/1.00  --dbg_dump_prop_clauses                 false
% 3.82/1.00  --dbg_dump_prop_clauses_file            -
% 3.82/1.00  --dbg_out_stat                          false
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  ------ Proving...
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  % SZS status Theorem for theBenchmark.p
% 3.82/1.00  
% 3.82/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.82/1.00  
% 3.82/1.00  fof(f26,conjecture,(
% 3.82/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f27,negated_conjecture,(
% 3.82/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.82/1.00    inference(negated_conjecture,[],[f26])).
% 3.82/1.00  
% 3.82/1.00  fof(f57,plain,(
% 3.82/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.82/1.00    inference(ennf_transformation,[],[f27])).
% 3.82/1.00  
% 3.82/1.00  fof(f58,plain,(
% 3.82/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.82/1.00    inference(flattening,[],[f57])).
% 3.82/1.00  
% 3.82/1.00  fof(f68,plain,(
% 3.82/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.82/1.00    introduced(choice_axiom,[])).
% 3.82/1.00  
% 3.82/1.00  fof(f69,plain,(
% 3.82/1.00    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.82/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f58,f68])).
% 3.82/1.00  
% 3.82/1.00  fof(f114,plain,(
% 3.82/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.82/1.00    inference(cnf_transformation,[],[f69])).
% 3.82/1.00  
% 3.82/1.00  fof(f21,axiom,(
% 3.82/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f50,plain,(
% 3.82/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.82/1.00    inference(ennf_transformation,[],[f21])).
% 3.82/1.00  
% 3.82/1.00  fof(f100,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.82/1.00    inference(cnf_transformation,[],[f50])).
% 3.82/1.00  
% 3.82/1.00  fof(f15,axiom,(
% 3.82/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f39,plain,(
% 3.82/1.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.82/1.00    inference(ennf_transformation,[],[f15])).
% 3.82/1.00  
% 3.82/1.00  fof(f40,plain,(
% 3.82/1.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.82/1.00    inference(flattening,[],[f39])).
% 3.82/1.00  
% 3.82/1.00  fof(f92,plain,(
% 3.82/1.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f40])).
% 3.82/1.00  
% 3.82/1.00  fof(f115,plain,(
% 3.82/1.00    v2_funct_1(sK3)),
% 3.82/1.00    inference(cnf_transformation,[],[f69])).
% 3.82/1.00  
% 3.82/1.00  fof(f112,plain,(
% 3.82/1.00    v1_funct_1(sK3)),
% 3.82/1.00    inference(cnf_transformation,[],[f69])).
% 3.82/1.00  
% 3.82/1.00  fof(f24,axiom,(
% 3.82/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f53,plain,(
% 3.82/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.82/1.00    inference(ennf_transformation,[],[f24])).
% 3.82/1.00  
% 3.82/1.00  fof(f54,plain,(
% 3.82/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.82/1.00    inference(flattening,[],[f53])).
% 3.82/1.00  
% 3.82/1.00  fof(f67,plain,(
% 3.82/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.82/1.00    inference(nnf_transformation,[],[f54])).
% 3.82/1.00  
% 3.82/1.00  fof(f106,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.82/1.00    inference(cnf_transformation,[],[f67])).
% 3.82/1.00  
% 3.82/1.00  fof(f125,plain,(
% 3.82/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.82/1.00    inference(equality_resolution,[],[f106])).
% 3.82/1.00  
% 3.82/1.00  fof(f117,plain,(
% 3.82/1.00    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.82/1.00    inference(cnf_transformation,[],[f69])).
% 3.82/1.00  
% 3.82/1.00  fof(f5,axiom,(
% 3.82/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f65,plain,(
% 3.82/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.82/1.00    inference(nnf_transformation,[],[f5])).
% 3.82/1.00  
% 3.82/1.00  fof(f66,plain,(
% 3.82/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.82/1.00    inference(flattening,[],[f65])).
% 3.82/1.00  
% 3.82/1.00  fof(f78,plain,(
% 3.82/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.82/1.00    inference(cnf_transformation,[],[f66])).
% 3.82/1.00  
% 3.82/1.00  fof(f121,plain,(
% 3.82/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.82/1.00    inference(equality_resolution,[],[f78])).
% 3.82/1.00  
% 3.82/1.00  fof(f16,axiom,(
% 3.82/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f41,plain,(
% 3.82/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.82/1.00    inference(ennf_transformation,[],[f16])).
% 3.82/1.00  
% 3.82/1.00  fof(f42,plain,(
% 3.82/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.82/1.00    inference(flattening,[],[f41])).
% 3.82/1.00  
% 3.82/1.00  fof(f94,plain,(
% 3.82/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f42])).
% 3.82/1.00  
% 3.82/1.00  fof(f103,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.82/1.00    inference(cnf_transformation,[],[f67])).
% 3.82/1.00  
% 3.82/1.00  fof(f113,plain,(
% 3.82/1.00    v1_funct_2(sK3,sK1,sK2)),
% 3.82/1.00    inference(cnf_transformation,[],[f69])).
% 3.82/1.00  
% 3.82/1.00  fof(f22,axiom,(
% 3.82/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f51,plain,(
% 3.82/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.82/1.00    inference(ennf_transformation,[],[f22])).
% 3.82/1.00  
% 3.82/1.00  fof(f101,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.82/1.00    inference(cnf_transformation,[],[f51])).
% 3.82/1.00  
% 3.82/1.00  fof(f19,axiom,(
% 3.82/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f47,plain,(
% 3.82/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.82/1.00    inference(ennf_transformation,[],[f19])).
% 3.82/1.00  
% 3.82/1.00  fof(f48,plain,(
% 3.82/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.82/1.00    inference(flattening,[],[f47])).
% 3.82/1.00  
% 3.82/1.00  fof(f98,plain,(
% 3.82/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f48])).
% 3.82/1.00  
% 3.82/1.00  fof(f25,axiom,(
% 3.82/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f55,plain,(
% 3.82/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.82/1.00    inference(ennf_transformation,[],[f25])).
% 3.82/1.00  
% 3.82/1.00  fof(f56,plain,(
% 3.82/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.82/1.00    inference(flattening,[],[f55])).
% 3.82/1.00  
% 3.82/1.00  fof(f111,plain,(
% 3.82/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f56])).
% 3.82/1.00  
% 3.82/1.00  fof(f23,axiom,(
% 3.82/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f52,plain,(
% 3.82/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.82/1.00    inference(ennf_transformation,[],[f23])).
% 3.82/1.00  
% 3.82/1.00  fof(f102,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.82/1.00    inference(cnf_transformation,[],[f52])).
% 3.82/1.00  
% 3.82/1.00  fof(f116,plain,(
% 3.82/1.00    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.82/1.00    inference(cnf_transformation,[],[f69])).
% 3.82/1.00  
% 3.82/1.00  fof(f97,plain,(
% 3.82/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f48])).
% 3.82/1.00  
% 3.82/1.00  fof(f93,plain,(
% 3.82/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f42])).
% 3.82/1.00  
% 3.82/1.00  fof(f110,plain,(
% 3.82/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f56])).
% 3.82/1.00  
% 3.82/1.00  fof(f1,axiom,(
% 3.82/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f59,plain,(
% 3.82/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.82/1.00    inference(nnf_transformation,[],[f1])).
% 3.82/1.00  
% 3.82/1.00  fof(f60,plain,(
% 3.82/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.82/1.00    inference(rectify,[],[f59])).
% 3.82/1.00  
% 3.82/1.00  fof(f61,plain,(
% 3.82/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.82/1.00    introduced(choice_axiom,[])).
% 3.82/1.00  
% 3.82/1.00  fof(f62,plain,(
% 3.82/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.82/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f60,f61])).
% 3.82/1.00  
% 3.82/1.00  fof(f71,plain,(
% 3.82/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f62])).
% 3.82/1.00  
% 3.82/1.00  fof(f4,axiom,(
% 3.82/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f76,plain,(
% 3.82/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f4])).
% 3.82/1.00  
% 3.82/1.00  fof(f20,axiom,(
% 3.82/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f49,plain,(
% 3.82/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.82/1.00    inference(ennf_transformation,[],[f20])).
% 3.82/1.00  
% 3.82/1.00  fof(f99,plain,(
% 3.82/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f49])).
% 3.82/1.00  
% 3.82/1.00  fof(f10,axiom,(
% 3.82/1.00    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f33,plain,(
% 3.82/1.00    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 3.82/1.00    inference(ennf_transformation,[],[f10])).
% 3.82/1.00  
% 3.82/1.00  fof(f84,plain,(
% 3.82/1.00    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f33])).
% 3.82/1.00  
% 3.82/1.00  fof(f2,axiom,(
% 3.82/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f28,plain,(
% 3.82/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.82/1.00    inference(ennf_transformation,[],[f2])).
% 3.82/1.00  
% 3.82/1.00  fof(f72,plain,(
% 3.82/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f28])).
% 3.82/1.00  
% 3.82/1.00  fof(f8,axiom,(
% 3.82/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f30,plain,(
% 3.82/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.82/1.00    inference(ennf_transformation,[],[f8])).
% 3.82/1.00  
% 3.82/1.00  fof(f31,plain,(
% 3.82/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.82/1.00    inference(flattening,[],[f30])).
% 3.82/1.00  
% 3.82/1.00  fof(f82,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.82/1.00    inference(cnf_transformation,[],[f31])).
% 3.82/1.00  
% 3.82/1.00  fof(f79,plain,(
% 3.82/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.82/1.00    inference(cnf_transformation,[],[f66])).
% 3.82/1.00  
% 3.82/1.00  fof(f120,plain,(
% 3.82/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.82/1.00    inference(equality_resolution,[],[f79])).
% 3.82/1.00  
% 3.82/1.00  fof(f6,axiom,(
% 3.82/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f29,plain,(
% 3.82/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.82/1.00    inference(ennf_transformation,[],[f6])).
% 3.82/1.00  
% 3.82/1.00  fof(f80,plain,(
% 3.82/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.82/1.00    inference(cnf_transformation,[],[f29])).
% 3.82/1.00  
% 3.82/1.00  fof(f7,axiom,(
% 3.82/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.00  
% 3.82/1.00  fof(f81,plain,(
% 3.82/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.82/1.00    inference(cnf_transformation,[],[f7])).
% 3.82/1.00  
% 3.82/1.00  cnf(c_45,negated_conjecture,
% 3.82/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.82/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1699,plain,
% 3.82/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_30,plain,
% 3.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.82/1.00      | v1_relat_1(X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1703,plain,
% 3.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.82/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3817,plain,
% 3.82/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_1699,c_1703]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_22,plain,
% 3.82/1.00      ( ~ v2_funct_1(X0)
% 3.82/1.00      | ~ v1_funct_1(X0)
% 3.82/1.00      | ~ v1_relat_1(X0)
% 3.82/1.00      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_44,negated_conjecture,
% 3.82/1.00      ( v2_funct_1(sK3) ),
% 3.82/1.00      inference(cnf_transformation,[],[f115]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_590,plain,
% 3.82/1.00      ( ~ v1_funct_1(X0)
% 3.82/1.00      | ~ v1_relat_1(X0)
% 3.82/1.00      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.82/1.00      | sK3 != X0 ),
% 3.82/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_44]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_591,plain,
% 3.82/1.00      ( ~ v1_funct_1(sK3)
% 3.82/1.00      | ~ v1_relat_1(sK3)
% 3.82/1.00      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.82/1.00      inference(unflattening,[status(thm)],[c_590]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_47,negated_conjecture,
% 3.82/1.00      ( v1_funct_1(sK3) ),
% 3.82/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_593,plain,
% 3.82/1.00      ( ~ v1_relat_1(sK3) | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_591,c_47]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1691,plain,
% 3.82/1.00      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 3.82/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4015,plain,
% 3.82/1.00      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_3817,c_1691]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_35,plain,
% 3.82/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.82/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.82/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.82/1.00      inference(cnf_transformation,[],[f125]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_42,negated_conjecture,
% 3.82/1.00      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.82/1.00      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.82/1.00      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.82/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_754,plain,
% 3.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.82/1.00      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.82/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.82/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.82/1.00      | k2_funct_1(sK3) != X0
% 3.82/1.00      | sK1 != X1
% 3.82/1.00      | sK2 != k1_xboole_0 ),
% 3.82/1.00      inference(resolution_lifted,[status(thm)],[c_35,c_42]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_755,plain,
% 3.82/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.82/1.00      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.82/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.82/1.00      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.82/1.00      | sK2 != k1_xboole_0 ),
% 3.82/1.00      inference(unflattening,[status(thm)],[c_754]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1685,plain,
% 3.82/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.82/1.00      | sK2 != k1_xboole_0
% 3.82/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.82/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.82/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_8,plain,
% 3.82/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.82/1.00      inference(cnf_transformation,[],[f121]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1959,plain,
% 3.82/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.82/1.00      | sK2 != k1_xboole_0
% 3.82/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.82/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.82/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_1685,c_8]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_48,plain,
% 3.82/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_50,plain,
% 3.82/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_23,plain,
% 3.82/1.00      ( ~ v1_funct_1(X0)
% 3.82/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.82/1.00      | ~ v1_relat_1(X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2071,plain,
% 3.82/1.00      ( v1_funct_1(k2_funct_1(sK3))
% 3.82/1.00      | ~ v1_funct_1(sK3)
% 3.82/1.00      | ~ v1_relat_1(sK3) ),
% 3.82/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2072,plain,
% 3.82/1.00      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.82/1.00      | v1_funct_1(sK3) != iProver_top
% 3.82/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_2071]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2080,plain,
% 3.82/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.82/1.00      | v1_relat_1(sK3) ),
% 3.82/1.00      inference(instantiation,[status(thm)],[c_30]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2295,plain,
% 3.82/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.82/1.00      | v1_relat_1(sK3) ),
% 3.82/1.00      inference(instantiation,[status(thm)],[c_2080]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2296,plain,
% 3.82/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.82/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_2295]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2470,plain,
% 3.82/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.82/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.82/1.00      | sK2 != k1_xboole_0
% 3.82/1.00      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_1959,c_48,c_50,c_2072,c_2296]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2471,plain,
% 3.82/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.82/1.00      | sK2 != k1_xboole_0
% 3.82/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.82/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.82/1.00      inference(renaming,[status(thm)],[c_2470]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4304,plain,
% 3.82/1.00      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 3.82/1.00      | sK2 != k1_xboole_0
% 3.82/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.82/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_4015,c_2471]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_38,plain,
% 3.82/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.82/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.82/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.82/1.00      | k1_xboole_0 = X2 ),
% 3.82/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_46,negated_conjecture,
% 3.82/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.82/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_826,plain,
% 3.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.82/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.82/1.00      | sK1 != X1
% 3.82/1.00      | sK2 != X2
% 3.82/1.00      | sK3 != X0
% 3.82/1.00      | k1_xboole_0 = X2 ),
% 3.82/1.00      inference(resolution_lifted,[status(thm)],[c_38,c_46]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_827,plain,
% 3.82/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.82/1.00      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.82/1.00      | k1_xboole_0 = sK2 ),
% 3.82/1.00      inference(unflattening,[status(thm)],[c_826]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_829,plain,
% 3.82/1.00      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_827,c_45]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_31,plain,
% 3.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.82/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1702,plain,
% 3.82/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.82/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4743,plain,
% 3.82/1.00      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_1699,c_1702]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4794,plain,
% 3.82/1.00      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_829,c_4743]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_27,plain,
% 3.82/1.00      ( ~ v2_funct_1(X0)
% 3.82/1.00      | ~ v1_funct_1(X0)
% 3.82/1.00      | ~ v1_relat_1(X0)
% 3.82/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_576,plain,
% 3.82/1.00      ( ~ v1_funct_1(X0)
% 3.82/1.00      | ~ v1_relat_1(X0)
% 3.82/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.82/1.00      | sK3 != X0 ),
% 3.82/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_44]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_577,plain,
% 3.82/1.00      ( ~ v1_funct_1(sK3)
% 3.82/1.00      | ~ v1_relat_1(sK3)
% 3.82/1.00      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.82/1.00      inference(unflattening,[status(thm)],[c_576]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_579,plain,
% 3.82/1.00      ( ~ v1_relat_1(sK3)
% 3.82/1.00      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_577,c_47]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1692,plain,
% 3.82/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.82/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4014,plain,
% 3.82/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_3817,c_1692]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4018,plain,
% 3.82/1.00      ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
% 3.82/1.00      inference(light_normalisation,[status(thm)],[c_4014,c_4015]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_39,plain,
% 3.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.82/1.00      | ~ v1_funct_1(X0)
% 3.82/1.00      | ~ v1_relat_1(X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1700,plain,
% 3.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.82/1.00      | v1_funct_1(X0) != iProver_top
% 3.82/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_5534,plain,
% 3.82/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.82/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.82/1.00      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_4018,c_1700]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_32,plain,
% 3.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.82/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1701,plain,
% 3.82/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.82/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3868,plain,
% 3.82/1.00      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_1699,c_1701]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_43,negated_conjecture,
% 3.82/1.00      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.82/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3880,plain,
% 3.82/1.00      ( k2_relat_1(sK3) = sK2 ),
% 3.82/1.00      inference(light_normalisation,[status(thm)],[c_3868,c_43]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_28,plain,
% 3.82/1.00      ( ~ v2_funct_1(X0)
% 3.82/1.00      | ~ v1_funct_1(X0)
% 3.82/1.00      | ~ v1_relat_1(X0)
% 3.82/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_562,plain,
% 3.82/1.00      ( ~ v1_funct_1(X0)
% 3.82/1.00      | ~ v1_relat_1(X0)
% 3.82/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.82/1.00      | sK3 != X0 ),
% 3.82/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_44]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_563,plain,
% 3.82/1.00      ( ~ v1_funct_1(sK3)
% 3.82/1.00      | ~ v1_relat_1(sK3)
% 3.82/1.00      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.82/1.00      inference(unflattening,[status(thm)],[c_562]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_565,plain,
% 3.82/1.00      ( ~ v1_relat_1(sK3)
% 3.82/1.00      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_563,c_47]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1693,plain,
% 3.82/1.00      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.82/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3889,plain,
% 3.82/1.00      ( k1_relat_1(k2_funct_1(sK3)) = sK2
% 3.82/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_3880,c_1693]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4293,plain,
% 3.82/1.00      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_3889,c_50,c_2296]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4303,plain,
% 3.82/1.00      ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_4015,c_4293]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_5535,plain,
% 3.82/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.82/1.00      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.82/1.00      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.82/1.00      inference(light_normalisation,[status(thm)],[c_5534,c_4303]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_24,plain,
% 3.82/1.00      ( ~ v1_funct_1(X0)
% 3.82/1.00      | ~ v1_relat_1(X0)
% 3.82/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 3.82/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1706,plain,
% 3.82/1.00      ( v1_funct_1(X0) != iProver_top
% 3.82/1.00      | v1_relat_1(X0) != iProver_top
% 3.82/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_5168,plain,
% 3.82/1.00      ( v1_funct_1(sK3) != iProver_top
% 3.82/1.00      | v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 3.82/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_4015,c_1706]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1707,plain,
% 3.82/1.00      ( v1_funct_1(X0) != iProver_top
% 3.82/1.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.82/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_5211,plain,
% 3.82/1.00      ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
% 3.82/1.00      | v1_funct_1(sK3) != iProver_top
% 3.82/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_4015,c_1707]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7680,plain,
% 3.82/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_5535,c_48,c_50,c_2296,c_5168,c_5211]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7685,plain,
% 3.82/1.00      ( sK2 = k1_xboole_0
% 3.82/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_4794,c_7680]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_40,plain,
% 3.82/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.82/1.00      | ~ v1_funct_1(X0)
% 3.82/1.00      | ~ v1_relat_1(X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_837,plain,
% 3.82/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.82/1.00      | ~ v1_funct_1(X0)
% 3.82/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.82/1.00      | ~ v1_relat_1(X0)
% 3.82/1.00      | k2_funct_1(sK3) != X0
% 3.82/1.00      | k2_relat_1(X0) != sK1
% 3.82/1.00      | k1_relat_1(X0) != sK2 ),
% 3.82/1.00      inference(resolution_lifted,[status(thm)],[c_40,c_42]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_838,plain,
% 3.82/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.82/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.82/1.00      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.82/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.82/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.82/1.00      inference(unflattening,[status(thm)],[c_837]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_850,plain,
% 3.82/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.82/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.82/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.82/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.82/1.00      inference(forward_subsumption_resolution,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_838,c_30]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1681,plain,
% 3.82/1.00      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.82/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.82/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.82/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_855,plain,
% 3.82/1.00      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.82/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.82/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.82/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2369,plain,
% 3.82/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.82/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.82/1.00      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_1681,c_48,c_50,c_855,c_2072,c_2296]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2370,plain,
% 3.82/1.00      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.82/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.82/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.82/1.00      inference(renaming,[status(thm)],[c_2369]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4296,plain,
% 3.82/1.00      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.82/1.00      | sK2 != sK2
% 3.82/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_4293,c_2370]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4855,plain,
% 3.82/1.00      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.82/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.82/1.00      inference(equality_resolution_simp,[status(thm)],[c_4296]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4857,plain,
% 3.82/1.00      ( k2_relat_1(k4_relat_1(sK3)) != sK1
% 3.82/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.82/1.00      inference(light_normalisation,[status(thm)],[c_4855,c_4015]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_5532,plain,
% 3.82/1.00      ( k1_relat_1(sK3) != sK1
% 3.82/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_4018,c_4857]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7716,plain,
% 3.82/1.00      ( sK2 = k1_xboole_0 ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_7685,c_4794,c_5532]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7719,plain,
% 3.82/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_7716,c_7680]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7858,plain,
% 3.82/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_7719,c_8]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_9849,plain,
% 3.82/1.00      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.82/1.00      | k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0 ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_4304,c_4794,c_5532,c_7685,c_7858]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_9850,plain,
% 3.82/1.00      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 3.82/1.00      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.82/1.00      inference(renaming,[status(thm)],[c_9849]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_0,plain,
% 3.82/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1722,plain,
% 3.82/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.82/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_6,plain,
% 3.82/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1717,plain,
% 3.82/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_29,plain,
% 3.82/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.82/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1704,plain,
% 3.82/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.82/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3215,plain,
% 3.82/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_1717,c_1704]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3264,plain,
% 3.82/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_1722,c_3215]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_15,plain,
% 3.82/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k4_relat_1(X0)) ),
% 3.82/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1711,plain,
% 3.82/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.82/1.00      | v1_xboole_0(k4_relat_1(X0)) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2,plain,
% 3.82/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.82/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1720,plain,
% 3.82/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_2932,plain,
% 3.82/1.00      ( k4_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_1711,c_1720]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_3375,plain,
% 3.82/1.00      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_3264,c_2932]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_12,plain,
% 3.82/1.00      ( m1_subset_1(X0,X1)
% 3.82/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.82/1.00      | ~ r2_hidden(X0,X2) ),
% 3.82/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1714,plain,
% 3.82/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.82/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.82/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_5775,plain,
% 3.82/1.00      ( m1_subset_1(X0,k2_zfmisc_1(sK1,sK2)) = iProver_top
% 3.82/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_1699,c_1714]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7733,plain,
% 3.82/1.00      ( m1_subset_1(X0,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top
% 3.82/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_7716,c_5775]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7,plain,
% 3.82/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.82/1.00      inference(cnf_transformation,[],[f120]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7811,plain,
% 3.82/1.00      ( m1_subset_1(X0,k1_xboole_0) = iProver_top
% 3.82/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_7733,c_7]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_10,plain,
% 3.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.82/1.00      | ~ r2_hidden(X2,X0)
% 3.82/1.00      | r2_hidden(X2,X1) ),
% 3.82/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1716,plain,
% 3.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.82/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.82/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_5830,plain,
% 3.82/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) = iProver_top
% 3.82/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_1699,c_1716]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7732,plain,
% 3.82/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top
% 3.82/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_7716,c_5830]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7816,plain,
% 3.82/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 3.82/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_7732,c_7]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_8643,plain,
% 3.82/1.00      ( r2_hidden(X0,sK3) != iProver_top ),
% 3.82/1.00      inference(global_propositional_subsumption,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_7811,c_3215,c_7816]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_8648,plain,
% 3.82/1.00      ( v1_xboole_0(sK3) = iProver_top ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_1722,c_8643]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_9366,plain,
% 3.82/1.00      ( sK3 = k1_xboole_0 ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_8648,c_1720]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_9853,plain,
% 3.82/1.00      ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k1_xboole_0
% 3.82/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.82/1.00      inference(light_normalisation,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_9850,c_3375,c_7716,c_9366]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_11,plain,
% 3.82/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.82/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_1715,plain,
% 3.82/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.82/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_4742,plain,
% 3.82/1.00      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.82/1.00      inference(superposition,[status(thm)],[c_1715,c_1702]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_9854,plain,
% 3.82/1.00      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 3.82/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_9853,c_8,c_4742]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_9857,plain,
% 3.82/1.00      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 3.82/1.00      inference(forward_subsumption_resolution,
% 3.82/1.00                [status(thm)],
% 3.82/1.00                [c_9854,c_1715]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_7743,plain,
% 3.82/1.00      ( k1_relat_1(k4_relat_1(sK3)) = k1_xboole_0 ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_7716,c_4303]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_9375,plain,
% 3.82/1.00      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.82/1.00      inference(demodulation,[status(thm)],[c_9366,c_7743]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(c_9434,plain,
% 3.82/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.82/1.00      inference(light_normalisation,[status(thm)],[c_9375,c_3375]) ).
% 3.82/1.00  
% 3.82/1.00  cnf(contradiction,plain,
% 3.82/1.00      ( $false ),
% 3.82/1.00      inference(minisat,[status(thm)],[c_9857,c_9434]) ).
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.82/1.00  
% 3.82/1.00  ------                               Statistics
% 3.82/1.00  
% 3.82/1.00  ------ General
% 3.82/1.00  
% 3.82/1.00  abstr_ref_over_cycles:                  0
% 3.82/1.00  abstr_ref_under_cycles:                 0
% 3.82/1.00  gc_basic_clause_elim:                   0
% 3.82/1.00  forced_gc_time:                         0
% 3.82/1.00  parsing_time:                           0.013
% 3.82/1.00  unif_index_cands_time:                  0.
% 3.82/1.00  unif_index_add_time:                    0.
% 3.82/1.00  orderings_time:                         0.
% 3.82/1.00  out_proof_time:                         0.015
% 3.82/1.00  total_time:                             0.391
% 3.82/1.00  num_of_symbols:                         54
% 3.82/1.00  num_of_terms:                           8885
% 3.82/1.00  
% 3.82/1.00  ------ Preprocessing
% 3.82/1.00  
% 3.82/1.00  num_of_splits:                          0
% 3.82/1.00  num_of_split_atoms:                     0
% 3.82/1.00  num_of_reused_defs:                     0
% 3.82/1.00  num_eq_ax_congr_red:                    9
% 3.82/1.00  num_of_sem_filtered_clauses:            1
% 3.82/1.00  num_of_subtypes:                        0
% 3.82/1.00  monotx_restored_types:                  0
% 3.82/1.00  sat_num_of_epr_types:                   0
% 3.82/1.00  sat_num_of_non_cyclic_types:            0
% 3.82/1.00  sat_guarded_non_collapsed_types:        0
% 3.82/1.00  num_pure_diseq_elim:                    0
% 3.82/1.00  simp_replaced_by:                       0
% 3.82/1.00  res_preprocessed:                       177
% 3.82/1.00  prep_upred:                             0
% 3.82/1.00  prep_unflattend:                        46
% 3.82/1.00  smt_new_axioms:                         0
% 3.82/1.00  pred_elim_cands:                        8
% 3.82/1.00  pred_elim:                              2
% 3.82/1.00  pred_elim_cl:                           -4
% 3.82/1.00  pred_elim_cycles:                       3
% 3.82/1.00  merged_defs:                            0
% 3.82/1.00  merged_defs_ncl:                        0
% 3.82/1.00  bin_hyper_res:                          0
% 3.82/1.00  prep_cycles:                            3
% 3.82/1.00  pred_elim_time:                         0.01
% 3.82/1.00  splitting_time:                         0.
% 3.82/1.00  sem_filter_time:                        0.
% 3.82/1.00  monotx_time:                            0.001
% 3.82/1.00  subtype_inf_time:                       0.
% 3.82/1.00  
% 3.82/1.00  ------ Problem properties
% 3.82/1.00  
% 3.82/1.00  clauses:                                48
% 3.82/1.00  conjectures:                            3
% 3.82/1.00  epr:                                    9
% 3.82/1.00  horn:                                   42
% 3.82/1.00  ground:                                 14
% 3.82/1.00  unary:                                  8
% 3.82/1.00  binary:                                 20
% 3.82/1.00  lits:                                   121
% 3.82/1.00  lits_eq:                                46
% 3.82/1.00  fd_pure:                                0
% 3.82/1.00  fd_pseudo:                              0
% 3.82/1.00  fd_cond:                                3
% 3.82/1.00  fd_pseudo_cond:                         1
% 3.82/1.00  ac_symbols:                             0
% 3.82/1.00  
% 3.82/1.00  ------ Propositional Solver
% 3.82/1.00  
% 3.82/1.00  prop_solver_calls:                      24
% 3.82/1.00  prop_fast_solver_calls:                 1334
% 3.82/1.00  smt_solver_calls:                       0
% 3.82/1.00  smt_fast_solver_calls:                  0
% 3.82/1.00  prop_num_of_clauses:                    3950
% 3.82/1.00  prop_preprocess_simplified:             11419
% 3.82/1.00  prop_fo_subsumed:                       41
% 3.82/1.00  prop_solver_time:                       0.
% 3.82/1.00  smt_solver_time:                        0.
% 3.82/1.00  smt_fast_solver_time:                   0.
% 3.82/1.00  prop_fast_solver_time:                  0.
% 3.82/1.00  prop_unsat_core_time:                   0.
% 3.82/1.00  
% 3.82/1.00  ------ QBF
% 3.82/1.00  
% 3.82/1.00  qbf_q_res:                              0
% 3.82/1.00  qbf_num_tautologies:                    0
% 3.82/1.00  qbf_prep_cycles:                        0
% 3.82/1.00  
% 3.82/1.00  ------ BMC1
% 3.82/1.00  
% 3.82/1.00  bmc1_current_bound:                     -1
% 3.82/1.00  bmc1_last_solved_bound:                 -1
% 3.82/1.00  bmc1_unsat_core_size:                   -1
% 3.82/1.00  bmc1_unsat_core_parents_size:           -1
% 3.82/1.00  bmc1_merge_next_fun:                    0
% 3.82/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.82/1.00  
% 3.82/1.00  ------ Instantiation
% 3.82/1.00  
% 3.82/1.00  inst_num_of_clauses:                    1359
% 3.82/1.00  inst_num_in_passive:                    652
% 3.82/1.00  inst_num_in_active:                     469
% 3.82/1.00  inst_num_in_unprocessed:                238
% 3.82/1.00  inst_num_of_loops:                      690
% 3.82/1.00  inst_num_of_learning_restarts:          0
% 3.82/1.00  inst_num_moves_active_passive:          219
% 3.82/1.00  inst_lit_activity:                      0
% 3.82/1.00  inst_lit_activity_moves:                0
% 3.82/1.00  inst_num_tautologies:                   0
% 3.82/1.00  inst_num_prop_implied:                  0
% 3.82/1.00  inst_num_existing_simplified:           0
% 3.82/1.00  inst_num_eq_res_simplified:             0
% 3.82/1.00  inst_num_child_elim:                    0
% 3.82/1.00  inst_num_of_dismatching_blockings:      267
% 3.82/1.00  inst_num_of_non_proper_insts:           888
% 3.82/1.00  inst_num_of_duplicates:                 0
% 3.82/1.00  inst_inst_num_from_inst_to_res:         0
% 3.82/1.00  inst_dismatching_checking_time:         0.
% 3.82/1.00  
% 3.82/1.00  ------ Resolution
% 3.82/1.00  
% 3.82/1.00  res_num_of_clauses:                     0
% 3.82/1.00  res_num_in_passive:                     0
% 3.82/1.00  res_num_in_active:                      0
% 3.82/1.00  res_num_of_loops:                       180
% 3.82/1.00  res_forward_subset_subsumed:            56
% 3.82/1.00  res_backward_subset_subsumed:           0
% 3.82/1.00  res_forward_subsumed:                   0
% 3.82/1.00  res_backward_subsumed:                  0
% 3.82/1.00  res_forward_subsumption_resolution:     6
% 3.82/1.00  res_backward_subsumption_resolution:    0
% 3.82/1.00  res_clause_to_clause_subsumption:       377
% 3.82/1.00  res_orphan_elimination:                 0
% 3.82/1.00  res_tautology_del:                      72
% 3.82/1.00  res_num_eq_res_simplified:              0
% 3.82/1.00  res_num_sel_changes:                    0
% 3.82/1.00  res_moves_from_active_to_pass:          0
% 3.82/1.00  
% 3.82/1.00  ------ Superposition
% 3.82/1.00  
% 3.82/1.00  sup_time_total:                         0.
% 3.82/1.00  sup_time_generating:                    0.
% 3.82/1.00  sup_time_sim_full:                      0.
% 3.82/1.00  sup_time_sim_immed:                     0.
% 3.82/1.00  
% 3.82/1.00  sup_num_of_clauses:                     118
% 3.82/1.00  sup_num_in_active:                      59
% 3.82/1.00  sup_num_in_passive:                     59
% 3.82/1.00  sup_num_of_loops:                       137
% 3.82/1.00  sup_fw_superposition:                   93
% 3.82/1.00  sup_bw_superposition:                   85
% 3.82/1.00  sup_immediate_simplified:               97
% 3.82/1.00  sup_given_eliminated:                   1
% 3.82/1.00  comparisons_done:                       0
% 3.82/1.00  comparisons_avoided:                    8
% 3.82/1.00  
% 3.82/1.00  ------ Simplifications
% 3.82/1.00  
% 3.82/1.00  
% 3.82/1.00  sim_fw_subset_subsumed:                 22
% 3.82/1.00  sim_bw_subset_subsumed:                 5
% 3.82/1.00  sim_fw_subsumed:                        14
% 3.82/1.00  sim_bw_subsumed:                        1
% 3.82/1.00  sim_fw_subsumption_res:                 4
% 3.82/1.00  sim_bw_subsumption_res:                 2
% 3.82/1.00  sim_tautology_del:                      5
% 3.82/1.00  sim_eq_tautology_del:                   16
% 3.82/1.00  sim_eq_res_simp:                        3
% 3.82/1.00  sim_fw_demodulated:                     24
% 3.82/1.00  sim_bw_demodulated:                     81
% 3.82/1.00  sim_light_normalised:                   53
% 3.82/1.00  sim_joinable_taut:                      0
% 3.82/1.00  sim_joinable_simp:                      0
% 3.82/1.00  sim_ac_normalised:                      0
% 3.82/1.00  sim_smt_subsumption:                    0
% 3.82/1.00  
%------------------------------------------------------------------------------

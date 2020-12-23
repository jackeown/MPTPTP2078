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
% DateTime   : Thu Dec  3 12:02:21 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  246 (7704 expanded)
%              Number of clauses        :  171 (2640 expanded)
%              Number of leaves         :   22 (1446 expanded)
%              Depth                    :   24
%              Number of atoms          :  729 (39631 expanded)
%              Number of equality atoms :  400 (8122 expanded)
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
    inference(ennf_transformation,[],[f27])).

fof(f59,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f58])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f59,f68])).

fof(f116,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f69])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f90,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f117,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f114,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f23,axiom,(
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
    inference(ennf_transformation,[],[f23])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f55])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f127,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f104])).

fof(f119,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f69])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f123,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f92,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f115,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f118,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f69])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f126,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f105])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f112,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f77])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f97,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f113,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_47,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2164,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2171,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4699,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2164,c_2171])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_46,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_722,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_46])).

cnf(c_723,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_722])).

cnf(c_49,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_725,plain,
    ( ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_723,c_49])).

cnf(c_2154,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_4929,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4699,c_2154])).

cnf(c_33,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_44,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_919,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_44])).

cnf(c_920,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_919])).

cnf(c_2148,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_920])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2438,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2148,c_6])).

cnf(c_50,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_52,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2558,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2559,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2558])).

cnf(c_2567,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2757,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2567])).

cnf(c_2758,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2757])).

cnf(c_2929,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2438,c_50,c_52,c_2559,c_2758])).

cnf(c_2930,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2929])).

cnf(c_5538,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4929,c_2930])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_48,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1045,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != sK3
    | sK1 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_48])).

cnf(c_1126,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2734,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_2736,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2734])).

cnf(c_1125,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2772,plain,
    ( X0 != X1
    | k2_funct_1(sK3) != X1
    | k2_funct_1(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_1125])).

cnf(c_3099,plain,
    ( X0 != k4_relat_1(sK3)
    | k2_funct_1(sK3) = X0
    | k2_funct_1(sK3) != k4_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2772])).

cnf(c_3100,plain,
    ( k2_funct_1(sK3) != k4_relat_1(sK3)
    | k2_funct_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k4_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3099])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3517,plain,
    ( v1_xboole_0(k4_relat_1(sK3))
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3545,plain,
    ( ~ v1_xboole_0(k4_relat_1(sK3))
    | k1_xboole_0 = k4_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2785,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_1125])).

cnf(c_3627,plain,
    ( sK1 != X0
    | sK1 = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_2785])).

cnf(c_3628,plain,
    ( sK1 = sK2
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3627])).

cnf(c_4029,plain,
    ( k2_funct_1(sK3) != X0
    | k2_funct_1(sK3) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2772])).

cnf(c_4031,plain,
    ( k2_funct_1(sK3) = sK3
    | k2_funct_1(sK3) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4029])).

cnf(c_1130,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2692,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_3292,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2692])).

cnf(c_5015,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_funct_1(sK3) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_3292])).

cnf(c_1129,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_3743,plain,
    ( k2_zfmisc_1(sK2,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_6127,plain,
    ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_3743])).

cnf(c_1124,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6128,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_2174,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6886,plain,
    ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4929,c_2174])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2169,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4804,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2164,c_2169])).

cnf(c_45,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_4816,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4804,c_45])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_42,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_838,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k2_relat_1(X2) != k1_xboole_0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_42])).

cnf(c_839,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_838])).

cnf(c_855,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_839,c_28])).

cnf(c_2151,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_855])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2417,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2151,c_5])).

cnf(c_7732,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4816,c_2417])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2792,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2793,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2792])).

cnf(c_2795,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2793])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3079,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3080,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3079])).

cnf(c_3082,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3080])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4316,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4319,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4316])).

cnf(c_4565,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4566,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4565])).

cnf(c_4568,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4566])).

cnf(c_8086,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7732,c_2795,c_3082,c_4319,c_4568])).

cnf(c_8087,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8086])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1002,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_48])).

cnf(c_1003,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_1002])).

cnf(c_1005,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1003,c_47])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2170,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6073,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2164,c_2170])).

cnf(c_6215,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1005,c_6073])).

cnf(c_26,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_690,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_46])).

cnf(c_691,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_693,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_49])).

cnf(c_2156,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_4928,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4699,c_2156])).

cnf(c_4932,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_4928,c_4929])).

cnf(c_41,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2165,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_7491,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4932,c_2165])).

cnf(c_27,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_676,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_46])).

cnf(c_677,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_679,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_49])).

cnf(c_2157,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_4915,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4816,c_2157])).

cnf(c_5365,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4915,c_52,c_2758])).

cnf(c_5536,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4929,c_5365])).

cnf(c_7492,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7491,c_5536])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2173,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6853,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4929,c_2173])).

cnf(c_8614,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7492,c_50,c_52,c_2758,c_6853,c_6886])).

cnf(c_8619,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6215,c_8614])).

cnf(c_1026,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k2_relat_1(X0) != sK1
    | k1_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_44])).

cnf(c_1027,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1026])).

cnf(c_1039,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1027,c_28])).

cnf(c_2143,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1039])).

cnf(c_1044,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1039])).

cnf(c_2823,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2143,c_50,c_52,c_1044,c_2559,c_2758])).

cnf(c_2824,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2823])).

cnf(c_5368,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5365,c_2824])).

cnf(c_6369,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5368])).

cnf(c_6371,plain,
    ( k2_relat_1(k4_relat_1(sK3)) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6369,c_4929])).

cnf(c_7489,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4932,c_6371])).

cnf(c_8901,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8619,c_6215,c_7489])).

cnf(c_8931,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8901,c_2164])).

cnf(c_8936,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8931,c_5])).

cnf(c_8904,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8901,c_8614])).

cnf(c_9010,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8904,c_6])).

cnf(c_34,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_986,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK3) != X0
    | sK1 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_44])).

cnf(c_987,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_986])).

cnf(c_2145,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_987])).

cnf(c_5540,plain,
    ( k1_relset_1(sK2,sK1,k4_relat_1(sK3)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4929,c_2145])).

cnf(c_8917,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8901,c_5540])).

cnf(c_8982,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8917,c_6])).

cnf(c_9014,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
    | sK1 = k1_xboole_0
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_9010,c_8982])).

cnf(c_2607,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_11342,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_2607])).

cnf(c_11691,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5538,c_49,c_50,c_47,c_52,c_0,c_723,c_1045,c_2558,c_2736,c_2757,c_2758,c_3100,c_3517,c_3545,c_3628,c_4031,c_5015,c_6127,c_6128,c_6215,c_6886,c_7489,c_8087,c_8619,c_8936,c_9014,c_11342])).

cnf(c_2187,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2178,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2186,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3768,plain,
    ( k4_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2178,c_2186])).

cnf(c_3793,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2187,c_3768])).

cnf(c_2181,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4191,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2164,c_2181])).

cnf(c_8927,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8901,c_4191])).

cnf(c_8946,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8927,c_5])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2182,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8092,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2182,c_8087])).

cnf(c_9328,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8946,c_8092])).

cnf(c_11693,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11691,c_3793,c_9328])).

cnf(c_6075,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2170])).

cnf(c_9414,plain,
    ( k1_relset_1(k1_xboole_0,X0,k4_relat_1(sK3)) = k1_relat_1(k4_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_9010,c_6075])).

cnf(c_8922,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8901,c_5536])).

cnf(c_10117,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8922,c_3793,c_9328])).

cnf(c_11293,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9414,c_3793,c_9328,c_10117])).

cnf(c_11694,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11693,c_11293])).

cnf(c_11695,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_11694])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.50/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/1.00  
% 3.50/1.00  ------  iProver source info
% 3.50/1.00  
% 3.50/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.50/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/1.00  git: non_committed_changes: false
% 3.50/1.00  git: last_make_outside_of_git: false
% 3.50/1.00  
% 3.50/1.00  ------ 
% 3.50/1.00  
% 3.50/1.00  ------ Input Options
% 3.50/1.00  
% 3.50/1.00  --out_options                           all
% 3.50/1.00  --tptp_safe_out                         true
% 3.50/1.00  --problem_path                          ""
% 3.50/1.00  --include_path                          ""
% 3.50/1.00  --clausifier                            res/vclausify_rel
% 3.50/1.00  --clausifier_options                    --mode clausify
% 3.50/1.00  --stdin                                 false
% 3.50/1.00  --stats_out                             all
% 3.50/1.00  
% 3.50/1.00  ------ General Options
% 3.50/1.00  
% 3.50/1.00  --fof                                   false
% 3.50/1.00  --time_out_real                         305.
% 3.50/1.00  --time_out_virtual                      -1.
% 3.50/1.00  --symbol_type_check                     false
% 3.50/1.00  --clausify_out                          false
% 3.50/1.00  --sig_cnt_out                           false
% 3.50/1.00  --trig_cnt_out                          false
% 3.50/1.00  --trig_cnt_out_tolerance                1.
% 3.50/1.00  --trig_cnt_out_sk_spl                   false
% 3.50/1.00  --abstr_cl_out                          false
% 3.50/1.00  
% 3.50/1.00  ------ Global Options
% 3.50/1.00  
% 3.50/1.00  --schedule                              default
% 3.50/1.00  --add_important_lit                     false
% 3.50/1.00  --prop_solver_per_cl                    1000
% 3.50/1.00  --min_unsat_core                        false
% 3.50/1.00  --soft_assumptions                      false
% 3.50/1.00  --soft_lemma_size                       3
% 3.50/1.00  --prop_impl_unit_size                   0
% 3.50/1.00  --prop_impl_unit                        []
% 3.50/1.00  --share_sel_clauses                     true
% 3.50/1.00  --reset_solvers                         false
% 3.50/1.00  --bc_imp_inh                            [conj_cone]
% 3.50/1.00  --conj_cone_tolerance                   3.
% 3.50/1.00  --extra_neg_conj                        none
% 3.50/1.00  --large_theory_mode                     true
% 3.50/1.00  --prolific_symb_bound                   200
% 3.50/1.00  --lt_threshold                          2000
% 3.50/1.00  --clause_weak_htbl                      true
% 3.50/1.00  --gc_record_bc_elim                     false
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing Options
% 3.50/1.00  
% 3.50/1.00  --preprocessing_flag                    true
% 3.50/1.00  --time_out_prep_mult                    0.1
% 3.50/1.00  --splitting_mode                        input
% 3.50/1.00  --splitting_grd                         true
% 3.50/1.00  --splitting_cvd                         false
% 3.50/1.00  --splitting_cvd_svl                     false
% 3.50/1.00  --splitting_nvd                         32
% 3.50/1.00  --sub_typing                            true
% 3.50/1.00  --prep_gs_sim                           true
% 3.50/1.00  --prep_unflatten                        true
% 3.50/1.00  --prep_res_sim                          true
% 3.50/1.00  --prep_upred                            true
% 3.50/1.00  --prep_sem_filter                       exhaustive
% 3.50/1.00  --prep_sem_filter_out                   false
% 3.50/1.00  --pred_elim                             true
% 3.50/1.00  --res_sim_input                         true
% 3.50/1.00  --eq_ax_congr_red                       true
% 3.50/1.00  --pure_diseq_elim                       true
% 3.50/1.00  --brand_transform                       false
% 3.50/1.00  --non_eq_to_eq                          false
% 3.50/1.00  --prep_def_merge                        true
% 3.50/1.00  --prep_def_merge_prop_impl              false
% 3.50/1.00  --prep_def_merge_mbd                    true
% 3.50/1.00  --prep_def_merge_tr_red                 false
% 3.50/1.00  --prep_def_merge_tr_cl                  false
% 3.50/1.00  --smt_preprocessing                     true
% 3.50/1.00  --smt_ac_axioms                         fast
% 3.50/1.00  --preprocessed_out                      false
% 3.50/1.00  --preprocessed_stats                    false
% 3.50/1.00  
% 3.50/1.00  ------ Abstraction refinement Options
% 3.50/1.00  
% 3.50/1.00  --abstr_ref                             []
% 3.50/1.00  --abstr_ref_prep                        false
% 3.50/1.00  --abstr_ref_until_sat                   false
% 3.50/1.00  --abstr_ref_sig_restrict                funpre
% 3.50/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/1.00  --abstr_ref_under                       []
% 3.50/1.00  
% 3.50/1.00  ------ SAT Options
% 3.50/1.00  
% 3.50/1.00  --sat_mode                              false
% 3.50/1.00  --sat_fm_restart_options                ""
% 3.50/1.00  --sat_gr_def                            false
% 3.50/1.00  --sat_epr_types                         true
% 3.50/1.00  --sat_non_cyclic_types                  false
% 3.50/1.00  --sat_finite_models                     false
% 3.50/1.00  --sat_fm_lemmas                         false
% 3.50/1.00  --sat_fm_prep                           false
% 3.50/1.00  --sat_fm_uc_incr                        true
% 3.50/1.00  --sat_out_model                         small
% 3.50/1.00  --sat_out_clauses                       false
% 3.50/1.00  
% 3.50/1.00  ------ QBF Options
% 3.50/1.00  
% 3.50/1.00  --qbf_mode                              false
% 3.50/1.00  --qbf_elim_univ                         false
% 3.50/1.00  --qbf_dom_inst                          none
% 3.50/1.00  --qbf_dom_pre_inst                      false
% 3.50/1.00  --qbf_sk_in                             false
% 3.50/1.00  --qbf_pred_elim                         true
% 3.50/1.00  --qbf_split                             512
% 3.50/1.00  
% 3.50/1.00  ------ BMC1 Options
% 3.50/1.00  
% 3.50/1.00  --bmc1_incremental                      false
% 3.50/1.00  --bmc1_axioms                           reachable_all
% 3.50/1.00  --bmc1_min_bound                        0
% 3.50/1.00  --bmc1_max_bound                        -1
% 3.50/1.00  --bmc1_max_bound_default                -1
% 3.50/1.00  --bmc1_symbol_reachability              true
% 3.50/1.00  --bmc1_property_lemmas                  false
% 3.50/1.00  --bmc1_k_induction                      false
% 3.50/1.00  --bmc1_non_equiv_states                 false
% 3.50/1.00  --bmc1_deadlock                         false
% 3.50/1.00  --bmc1_ucm                              false
% 3.50/1.00  --bmc1_add_unsat_core                   none
% 3.50/1.00  --bmc1_unsat_core_children              false
% 3.50/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/1.00  --bmc1_out_stat                         full
% 3.50/1.00  --bmc1_ground_init                      false
% 3.50/1.00  --bmc1_pre_inst_next_state              false
% 3.50/1.00  --bmc1_pre_inst_state                   false
% 3.50/1.00  --bmc1_pre_inst_reach_state             false
% 3.50/1.00  --bmc1_out_unsat_core                   false
% 3.50/1.00  --bmc1_aig_witness_out                  false
% 3.50/1.00  --bmc1_verbose                          false
% 3.50/1.00  --bmc1_dump_clauses_tptp                false
% 3.50/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.50/1.00  --bmc1_dump_file                        -
% 3.50/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.50/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.50/1.00  --bmc1_ucm_extend_mode                  1
% 3.50/1.00  --bmc1_ucm_init_mode                    2
% 3.50/1.00  --bmc1_ucm_cone_mode                    none
% 3.50/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.50/1.00  --bmc1_ucm_relax_model                  4
% 3.50/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.50/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/1.00  --bmc1_ucm_layered_model                none
% 3.50/1.00  --bmc1_ucm_max_lemma_size               10
% 3.50/1.00  
% 3.50/1.00  ------ AIG Options
% 3.50/1.00  
% 3.50/1.00  --aig_mode                              false
% 3.50/1.00  
% 3.50/1.00  ------ Instantiation Options
% 3.50/1.00  
% 3.50/1.00  --instantiation_flag                    true
% 3.50/1.00  --inst_sos_flag                         false
% 3.50/1.00  --inst_sos_phase                        true
% 3.50/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/1.00  --inst_lit_sel_side                     num_symb
% 3.50/1.00  --inst_solver_per_active                1400
% 3.50/1.00  --inst_solver_calls_frac                1.
% 3.50/1.00  --inst_passive_queue_type               priority_queues
% 3.50/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/1.00  --inst_passive_queues_freq              [25;2]
% 3.50/1.00  --inst_dismatching                      true
% 3.50/1.00  --inst_eager_unprocessed_to_passive     true
% 3.50/1.00  --inst_prop_sim_given                   true
% 3.50/1.00  --inst_prop_sim_new                     false
% 3.50/1.00  --inst_subs_new                         false
% 3.50/1.00  --inst_eq_res_simp                      false
% 3.50/1.00  --inst_subs_given                       false
% 3.50/1.00  --inst_orphan_elimination               true
% 3.50/1.00  --inst_learning_loop_flag               true
% 3.50/1.00  --inst_learning_start                   3000
% 3.50/1.00  --inst_learning_factor                  2
% 3.50/1.00  --inst_start_prop_sim_after_learn       3
% 3.50/1.00  --inst_sel_renew                        solver
% 3.50/1.00  --inst_lit_activity_flag                true
% 3.50/1.00  --inst_restr_to_given                   false
% 3.50/1.00  --inst_activity_threshold               500
% 3.50/1.00  --inst_out_proof                        true
% 3.50/1.00  
% 3.50/1.00  ------ Resolution Options
% 3.50/1.00  
% 3.50/1.00  --resolution_flag                       true
% 3.50/1.00  --res_lit_sel                           adaptive
% 3.50/1.00  --res_lit_sel_side                      none
% 3.50/1.00  --res_ordering                          kbo
% 3.50/1.00  --res_to_prop_solver                    active
% 3.50/1.00  --res_prop_simpl_new                    false
% 3.50/1.00  --res_prop_simpl_given                  true
% 3.50/1.00  --res_passive_queue_type                priority_queues
% 3.50/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/1.00  --res_passive_queues_freq               [15;5]
% 3.50/1.00  --res_forward_subs                      full
% 3.50/1.00  --res_backward_subs                     full
% 3.50/1.00  --res_forward_subs_resolution           true
% 3.50/1.00  --res_backward_subs_resolution          true
% 3.50/1.00  --res_orphan_elimination                true
% 3.50/1.00  --res_time_limit                        2.
% 3.50/1.00  --res_out_proof                         true
% 3.50/1.00  
% 3.50/1.00  ------ Superposition Options
% 3.50/1.00  
% 3.50/1.00  --superposition_flag                    true
% 3.50/1.00  --sup_passive_queue_type                priority_queues
% 3.50/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.50/1.00  --demod_completeness_check              fast
% 3.50/1.00  --demod_use_ground                      true
% 3.50/1.00  --sup_to_prop_solver                    passive
% 3.50/1.00  --sup_prop_simpl_new                    true
% 3.50/1.00  --sup_prop_simpl_given                  true
% 3.50/1.00  --sup_fun_splitting                     false
% 3.50/1.00  --sup_smt_interval                      50000
% 3.50/1.00  
% 3.50/1.00  ------ Superposition Simplification Setup
% 3.50/1.00  
% 3.50/1.00  --sup_indices_passive                   []
% 3.50/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.00  --sup_full_bw                           [BwDemod]
% 3.50/1.00  --sup_immed_triv                        [TrivRules]
% 3.50/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.00  --sup_immed_bw_main                     []
% 3.50/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.00  
% 3.50/1.00  ------ Combination Options
% 3.50/1.00  
% 3.50/1.00  --comb_res_mult                         3
% 3.50/1.00  --comb_sup_mult                         2
% 3.50/1.00  --comb_inst_mult                        10
% 3.50/1.00  
% 3.50/1.00  ------ Debug Options
% 3.50/1.00  
% 3.50/1.00  --dbg_backtrace                         false
% 3.50/1.00  --dbg_dump_prop_clauses                 false
% 3.50/1.00  --dbg_dump_prop_clauses_file            -
% 3.50/1.00  --dbg_out_stat                          false
% 3.50/1.00  ------ Parsing...
% 3.50/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/1.00  ------ Proving...
% 3.50/1.00  ------ Problem Properties 
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  clauses                                 54
% 3.50/1.00  conjectures                             3
% 3.50/1.00  EPR                                     7
% 3.50/1.00  Horn                                    47
% 3.50/1.00  unary                                   12
% 3.50/1.00  binary                                  23
% 3.50/1.00  lits                                    128
% 3.50/1.00  lits eq                                 54
% 3.50/1.00  fd_pure                                 0
% 3.50/1.00  fd_pseudo                               0
% 3.50/1.00  fd_cond                                 4
% 3.50/1.00  fd_pseudo_cond                          1
% 3.50/1.00  AC symbols                              0
% 3.50/1.00  
% 3.50/1.00  ------ Schedule dynamic 5 is on 
% 3.50/1.00  
% 3.50/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  ------ 
% 3.50/1.00  Current options:
% 3.50/1.00  ------ 
% 3.50/1.00  
% 3.50/1.00  ------ Input Options
% 3.50/1.00  
% 3.50/1.00  --out_options                           all
% 3.50/1.00  --tptp_safe_out                         true
% 3.50/1.00  --problem_path                          ""
% 3.50/1.00  --include_path                          ""
% 3.50/1.00  --clausifier                            res/vclausify_rel
% 3.50/1.00  --clausifier_options                    --mode clausify
% 3.50/1.00  --stdin                                 false
% 3.50/1.00  --stats_out                             all
% 3.50/1.00  
% 3.50/1.00  ------ General Options
% 3.50/1.00  
% 3.50/1.00  --fof                                   false
% 3.50/1.00  --time_out_real                         305.
% 3.50/1.00  --time_out_virtual                      -1.
% 3.50/1.00  --symbol_type_check                     false
% 3.50/1.00  --clausify_out                          false
% 3.50/1.00  --sig_cnt_out                           false
% 3.50/1.00  --trig_cnt_out                          false
% 3.50/1.00  --trig_cnt_out_tolerance                1.
% 3.50/1.00  --trig_cnt_out_sk_spl                   false
% 3.50/1.00  --abstr_cl_out                          false
% 3.50/1.00  
% 3.50/1.00  ------ Global Options
% 3.50/1.00  
% 3.50/1.00  --schedule                              default
% 3.50/1.00  --add_important_lit                     false
% 3.50/1.00  --prop_solver_per_cl                    1000
% 3.50/1.00  --min_unsat_core                        false
% 3.50/1.00  --soft_assumptions                      false
% 3.50/1.00  --soft_lemma_size                       3
% 3.50/1.00  --prop_impl_unit_size                   0
% 3.50/1.00  --prop_impl_unit                        []
% 3.50/1.00  --share_sel_clauses                     true
% 3.50/1.00  --reset_solvers                         false
% 3.50/1.00  --bc_imp_inh                            [conj_cone]
% 3.50/1.00  --conj_cone_tolerance                   3.
% 3.50/1.00  --extra_neg_conj                        none
% 3.50/1.00  --large_theory_mode                     true
% 3.50/1.00  --prolific_symb_bound                   200
% 3.50/1.00  --lt_threshold                          2000
% 3.50/1.00  --clause_weak_htbl                      true
% 3.50/1.00  --gc_record_bc_elim                     false
% 3.50/1.00  
% 3.50/1.00  ------ Preprocessing Options
% 3.50/1.00  
% 3.50/1.00  --preprocessing_flag                    true
% 3.50/1.00  --time_out_prep_mult                    0.1
% 3.50/1.00  --splitting_mode                        input
% 3.50/1.00  --splitting_grd                         true
% 3.50/1.00  --splitting_cvd                         false
% 3.50/1.00  --splitting_cvd_svl                     false
% 3.50/1.00  --splitting_nvd                         32
% 3.50/1.00  --sub_typing                            true
% 3.50/1.00  --prep_gs_sim                           true
% 3.50/1.00  --prep_unflatten                        true
% 3.50/1.00  --prep_res_sim                          true
% 3.50/1.00  --prep_upred                            true
% 3.50/1.00  --prep_sem_filter                       exhaustive
% 3.50/1.00  --prep_sem_filter_out                   false
% 3.50/1.00  --pred_elim                             true
% 3.50/1.00  --res_sim_input                         true
% 3.50/1.00  --eq_ax_congr_red                       true
% 3.50/1.00  --pure_diseq_elim                       true
% 3.50/1.00  --brand_transform                       false
% 3.50/1.00  --non_eq_to_eq                          false
% 3.50/1.00  --prep_def_merge                        true
% 3.50/1.00  --prep_def_merge_prop_impl              false
% 3.50/1.00  --prep_def_merge_mbd                    true
% 3.50/1.00  --prep_def_merge_tr_red                 false
% 3.50/1.00  --prep_def_merge_tr_cl                  false
% 3.50/1.00  --smt_preprocessing                     true
% 3.50/1.00  --smt_ac_axioms                         fast
% 3.50/1.00  --preprocessed_out                      false
% 3.50/1.00  --preprocessed_stats                    false
% 3.50/1.00  
% 3.50/1.00  ------ Abstraction refinement Options
% 3.50/1.00  
% 3.50/1.00  --abstr_ref                             []
% 3.50/1.00  --abstr_ref_prep                        false
% 3.50/1.00  --abstr_ref_until_sat                   false
% 3.50/1.00  --abstr_ref_sig_restrict                funpre
% 3.50/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/1.00  --abstr_ref_under                       []
% 3.50/1.00  
% 3.50/1.00  ------ SAT Options
% 3.50/1.00  
% 3.50/1.00  --sat_mode                              false
% 3.50/1.00  --sat_fm_restart_options                ""
% 3.50/1.00  --sat_gr_def                            false
% 3.50/1.00  --sat_epr_types                         true
% 3.50/1.00  --sat_non_cyclic_types                  false
% 3.50/1.00  --sat_finite_models                     false
% 3.50/1.00  --sat_fm_lemmas                         false
% 3.50/1.00  --sat_fm_prep                           false
% 3.50/1.00  --sat_fm_uc_incr                        true
% 3.50/1.00  --sat_out_model                         small
% 3.50/1.00  --sat_out_clauses                       false
% 3.50/1.00  
% 3.50/1.00  ------ QBF Options
% 3.50/1.00  
% 3.50/1.00  --qbf_mode                              false
% 3.50/1.00  --qbf_elim_univ                         false
% 3.50/1.00  --qbf_dom_inst                          none
% 3.50/1.00  --qbf_dom_pre_inst                      false
% 3.50/1.00  --qbf_sk_in                             false
% 3.50/1.00  --qbf_pred_elim                         true
% 3.50/1.00  --qbf_split                             512
% 3.50/1.00  
% 3.50/1.00  ------ BMC1 Options
% 3.50/1.00  
% 3.50/1.00  --bmc1_incremental                      false
% 3.50/1.00  --bmc1_axioms                           reachable_all
% 3.50/1.00  --bmc1_min_bound                        0
% 3.50/1.00  --bmc1_max_bound                        -1
% 3.50/1.00  --bmc1_max_bound_default                -1
% 3.50/1.00  --bmc1_symbol_reachability              true
% 3.50/1.00  --bmc1_property_lemmas                  false
% 3.50/1.00  --bmc1_k_induction                      false
% 3.50/1.00  --bmc1_non_equiv_states                 false
% 3.50/1.00  --bmc1_deadlock                         false
% 3.50/1.00  --bmc1_ucm                              false
% 3.50/1.00  --bmc1_add_unsat_core                   none
% 3.50/1.00  --bmc1_unsat_core_children              false
% 3.50/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/1.00  --bmc1_out_stat                         full
% 3.50/1.00  --bmc1_ground_init                      false
% 3.50/1.00  --bmc1_pre_inst_next_state              false
% 3.50/1.00  --bmc1_pre_inst_state                   false
% 3.50/1.00  --bmc1_pre_inst_reach_state             false
% 3.50/1.00  --bmc1_out_unsat_core                   false
% 3.50/1.00  --bmc1_aig_witness_out                  false
% 3.50/1.00  --bmc1_verbose                          false
% 3.50/1.00  --bmc1_dump_clauses_tptp                false
% 3.50/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.50/1.00  --bmc1_dump_file                        -
% 3.50/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.50/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.50/1.00  --bmc1_ucm_extend_mode                  1
% 3.50/1.00  --bmc1_ucm_init_mode                    2
% 3.50/1.00  --bmc1_ucm_cone_mode                    none
% 3.50/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.50/1.00  --bmc1_ucm_relax_model                  4
% 3.50/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.50/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/1.00  --bmc1_ucm_layered_model                none
% 3.50/1.00  --bmc1_ucm_max_lemma_size               10
% 3.50/1.00  
% 3.50/1.00  ------ AIG Options
% 3.50/1.00  
% 3.50/1.00  --aig_mode                              false
% 3.50/1.00  
% 3.50/1.00  ------ Instantiation Options
% 3.50/1.00  
% 3.50/1.00  --instantiation_flag                    true
% 3.50/1.00  --inst_sos_flag                         false
% 3.50/1.00  --inst_sos_phase                        true
% 3.50/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/1.00  --inst_lit_sel_side                     none
% 3.50/1.00  --inst_solver_per_active                1400
% 3.50/1.00  --inst_solver_calls_frac                1.
% 3.50/1.00  --inst_passive_queue_type               priority_queues
% 3.50/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/1.00  --inst_passive_queues_freq              [25;2]
% 3.50/1.00  --inst_dismatching                      true
% 3.50/1.00  --inst_eager_unprocessed_to_passive     true
% 3.50/1.00  --inst_prop_sim_given                   true
% 3.50/1.00  --inst_prop_sim_new                     false
% 3.50/1.00  --inst_subs_new                         false
% 3.50/1.00  --inst_eq_res_simp                      false
% 3.50/1.00  --inst_subs_given                       false
% 3.50/1.00  --inst_orphan_elimination               true
% 3.50/1.00  --inst_learning_loop_flag               true
% 3.50/1.00  --inst_learning_start                   3000
% 3.50/1.00  --inst_learning_factor                  2
% 3.50/1.00  --inst_start_prop_sim_after_learn       3
% 3.50/1.00  --inst_sel_renew                        solver
% 3.50/1.00  --inst_lit_activity_flag                true
% 3.50/1.00  --inst_restr_to_given                   false
% 3.50/1.00  --inst_activity_threshold               500
% 3.50/1.00  --inst_out_proof                        true
% 3.50/1.00  
% 3.50/1.00  ------ Resolution Options
% 3.50/1.00  
% 3.50/1.00  --resolution_flag                       false
% 3.50/1.00  --res_lit_sel                           adaptive
% 3.50/1.00  --res_lit_sel_side                      none
% 3.50/1.00  --res_ordering                          kbo
% 3.50/1.00  --res_to_prop_solver                    active
% 3.50/1.00  --res_prop_simpl_new                    false
% 3.50/1.00  --res_prop_simpl_given                  true
% 3.50/1.00  --res_passive_queue_type                priority_queues
% 3.50/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/1.00  --res_passive_queues_freq               [15;5]
% 3.50/1.00  --res_forward_subs                      full
% 3.50/1.00  --res_backward_subs                     full
% 3.50/1.00  --res_forward_subs_resolution           true
% 3.50/1.00  --res_backward_subs_resolution          true
% 3.50/1.00  --res_orphan_elimination                true
% 3.50/1.00  --res_time_limit                        2.
% 3.50/1.00  --res_out_proof                         true
% 3.50/1.00  
% 3.50/1.00  ------ Superposition Options
% 3.50/1.00  
% 3.50/1.00  --superposition_flag                    true
% 3.50/1.00  --sup_passive_queue_type                priority_queues
% 3.50/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.50/1.00  --demod_completeness_check              fast
% 3.50/1.00  --demod_use_ground                      true
% 3.50/1.00  --sup_to_prop_solver                    passive
% 3.50/1.00  --sup_prop_simpl_new                    true
% 3.50/1.00  --sup_prop_simpl_given                  true
% 3.50/1.00  --sup_fun_splitting                     false
% 3.50/1.00  --sup_smt_interval                      50000
% 3.50/1.00  
% 3.50/1.00  ------ Superposition Simplification Setup
% 3.50/1.00  
% 3.50/1.00  --sup_indices_passive                   []
% 3.50/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.00  --sup_full_bw                           [BwDemod]
% 3.50/1.00  --sup_immed_triv                        [TrivRules]
% 3.50/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.00  --sup_immed_bw_main                     []
% 3.50/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.00  
% 3.50/1.00  ------ Combination Options
% 3.50/1.00  
% 3.50/1.00  --comb_res_mult                         3
% 3.50/1.00  --comb_sup_mult                         2
% 3.50/1.00  --comb_inst_mult                        10
% 3.50/1.00  
% 3.50/1.00  ------ Debug Options
% 3.50/1.00  
% 3.50/1.00  --dbg_backtrace                         false
% 3.50/1.00  --dbg_dump_prop_clauses                 false
% 3.50/1.00  --dbg_dump_prop_clauses_file            -
% 3.50/1.00  --dbg_out_stat                          false
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  ------ Proving...
% 3.50/1.00  
% 3.50/1.00  
% 3.50/1.00  % SZS status Theorem for theBenchmark.p
% 3.50/1.00  
% 3.50/1.00   Resolution empty clause
% 3.50/1.00  
% 3.50/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/1.00  
% 3.50/1.00  fof(f26,conjecture,(
% 3.50/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f27,negated_conjecture,(
% 3.50/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.50/1.00    inference(negated_conjecture,[],[f26])).
% 3.50/1.00  
% 3.50/1.00  fof(f58,plain,(
% 3.50/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.50/1.00    inference(ennf_transformation,[],[f27])).
% 3.50/1.00  
% 3.50/1.00  fof(f59,plain,(
% 3.50/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.50/1.00    inference(flattening,[],[f58])).
% 3.50/1.00  
% 3.50/1.00  fof(f68,plain,(
% 3.50/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.50/1.00    introduced(choice_axiom,[])).
% 3.50/1.00  
% 3.50/1.00  fof(f69,plain,(
% 3.50/1.00    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.50/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f59,f68])).
% 3.50/1.00  
% 3.50/1.00  fof(f116,plain,(
% 3.50/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.50/1.00    inference(cnf_transformation,[],[f69])).
% 3.50/1.00  
% 3.50/1.00  fof(f20,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f51,plain,(
% 3.50/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.00    inference(ennf_transformation,[],[f20])).
% 3.50/1.00  
% 3.50/1.00  fof(f98,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.00    inference(cnf_transformation,[],[f51])).
% 3.50/1.00  
% 3.50/1.00  fof(f14,axiom,(
% 3.50/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f39,plain,(
% 3.50/1.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.50/1.00    inference(ennf_transformation,[],[f14])).
% 3.50/1.00  
% 3.50/1.00  fof(f40,plain,(
% 3.50/1.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.50/1.00    inference(flattening,[],[f39])).
% 3.50/1.00  
% 3.50/1.00  fof(f90,plain,(
% 3.50/1.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f40])).
% 3.50/1.00  
% 3.50/1.00  fof(f117,plain,(
% 3.50/1.00    v2_funct_1(sK3)),
% 3.50/1.00    inference(cnf_transformation,[],[f69])).
% 3.50/1.00  
% 3.50/1.00  fof(f114,plain,(
% 3.50/1.00    v1_funct_1(sK3)),
% 3.50/1.00    inference(cnf_transformation,[],[f69])).
% 3.50/1.00  
% 3.50/1.00  fof(f23,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f54,plain,(
% 3.50/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.00    inference(ennf_transformation,[],[f23])).
% 3.50/1.00  
% 3.50/1.00  fof(f55,plain,(
% 3.50/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.00    inference(flattening,[],[f54])).
% 3.50/1.00  
% 3.50/1.00  fof(f65,plain,(
% 3.50/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.00    inference(nnf_transformation,[],[f55])).
% 3.50/1.00  
% 3.50/1.00  fof(f104,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.00    inference(cnf_transformation,[],[f65])).
% 3.50/1.00  
% 3.50/1.00  fof(f127,plain,(
% 3.50/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.50/1.00    inference(equality_resolution,[],[f104])).
% 3.50/1.00  
% 3.50/1.00  fof(f119,plain,(
% 3.50/1.00    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.50/1.00    inference(cnf_transformation,[],[f69])).
% 3.50/1.00  
% 3.50/1.00  fof(f4,axiom,(
% 3.50/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f62,plain,(
% 3.50/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.50/1.00    inference(nnf_transformation,[],[f4])).
% 3.50/1.00  
% 3.50/1.00  fof(f63,plain,(
% 3.50/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.50/1.00    inference(flattening,[],[f62])).
% 3.50/1.00  
% 3.50/1.00  fof(f76,plain,(
% 3.50/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.50/1.00    inference(cnf_transformation,[],[f63])).
% 3.50/1.00  
% 3.50/1.00  fof(f123,plain,(
% 3.50/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.50/1.00    inference(equality_resolution,[],[f76])).
% 3.50/1.00  
% 3.50/1.00  fof(f15,axiom,(
% 3.50/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f41,plain,(
% 3.50/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.50/1.00    inference(ennf_transformation,[],[f15])).
% 3.50/1.00  
% 3.50/1.00  fof(f42,plain,(
% 3.50/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.50/1.00    inference(flattening,[],[f41])).
% 3.50/1.00  
% 3.50/1.00  fof(f92,plain,(
% 3.50/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f42])).
% 3.50/1.00  
% 3.50/1.00  fof(f1,axiom,(
% 3.50/1.00    v1_xboole_0(k1_xboole_0)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f70,plain,(
% 3.50/1.00    v1_xboole_0(k1_xboole_0)),
% 3.50/1.00    inference(cnf_transformation,[],[f1])).
% 3.50/1.00  
% 3.50/1.00  fof(f115,plain,(
% 3.50/1.00    v1_funct_2(sK3,sK1,sK2)),
% 3.50/1.00    inference(cnf_transformation,[],[f69])).
% 3.50/1.00  
% 3.50/1.00  fof(f9,axiom,(
% 3.50/1.00    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f33,plain,(
% 3.50/1.00    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 3.50/1.00    inference(ennf_transformation,[],[f9])).
% 3.50/1.00  
% 3.50/1.00  fof(f82,plain,(
% 3.50/1.00    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f33])).
% 3.50/1.00  
% 3.50/1.00  fof(f2,axiom,(
% 3.50/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f31,plain,(
% 3.50/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.50/1.00    inference(ennf_transformation,[],[f2])).
% 3.50/1.00  
% 3.50/1.00  fof(f71,plain,(
% 3.50/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f31])).
% 3.50/1.00  
% 3.50/1.00  fof(f22,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f53,plain,(
% 3.50/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.00    inference(ennf_transformation,[],[f22])).
% 3.50/1.00  
% 3.50/1.00  fof(f100,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.00    inference(cnf_transformation,[],[f53])).
% 3.50/1.00  
% 3.50/1.00  fof(f118,plain,(
% 3.50/1.00    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.50/1.00    inference(cnf_transformation,[],[f69])).
% 3.50/1.00  
% 3.50/1.00  fof(f105,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.00    inference(cnf_transformation,[],[f65])).
% 3.50/1.00  
% 3.50/1.00  fof(f126,plain,(
% 3.50/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.50/1.00    inference(equality_resolution,[],[f105])).
% 3.50/1.00  
% 3.50/1.00  fof(f25,axiom,(
% 3.50/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f56,plain,(
% 3.50/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.50/1.00    inference(ennf_transformation,[],[f25])).
% 3.50/1.00  
% 3.50/1.00  fof(f57,plain,(
% 3.50/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.50/1.00    inference(flattening,[],[f56])).
% 3.50/1.00  
% 3.50/1.00  fof(f112,plain,(
% 3.50/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f57])).
% 3.50/1.00  
% 3.50/1.00  fof(f77,plain,(
% 3.50/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.50/1.00    inference(cnf_transformation,[],[f63])).
% 3.50/1.00  
% 3.50/1.00  fof(f122,plain,(
% 3.50/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.50/1.00    inference(equality_resolution,[],[f77])).
% 3.50/1.00  
% 3.50/1.00  fof(f3,axiom,(
% 3.50/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f60,plain,(
% 3.50/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.50/1.00    inference(nnf_transformation,[],[f3])).
% 3.50/1.00  
% 3.50/1.00  fof(f61,plain,(
% 3.50/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.50/1.00    inference(flattening,[],[f60])).
% 3.50/1.00  
% 3.50/1.00  fof(f74,plain,(
% 3.50/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f61])).
% 3.50/1.00  
% 3.50/1.00  fof(f6,axiom,(
% 3.50/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f64,plain,(
% 3.50/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.50/1.00    inference(nnf_transformation,[],[f6])).
% 3.50/1.00  
% 3.50/1.00  fof(f79,plain,(
% 3.50/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.50/1.00    inference(cnf_transformation,[],[f64])).
% 3.50/1.00  
% 3.50/1.00  fof(f5,axiom,(
% 3.50/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f78,plain,(
% 3.50/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.50/1.00    inference(cnf_transformation,[],[f5])).
% 3.50/1.00  
% 3.50/1.00  fof(f101,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.00    inference(cnf_transformation,[],[f65])).
% 3.50/1.00  
% 3.50/1.00  fof(f21,axiom,(
% 3.50/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f52,plain,(
% 3.50/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.00    inference(ennf_transformation,[],[f21])).
% 3.50/1.00  
% 3.50/1.00  fof(f99,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.00    inference(cnf_transformation,[],[f52])).
% 3.50/1.00  
% 3.50/1.00  fof(f19,axiom,(
% 3.50/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.50/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/1.00  
% 3.50/1.00  fof(f49,plain,(
% 3.50/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.50/1.00    inference(ennf_transformation,[],[f19])).
% 3.50/1.00  
% 3.50/1.00  fof(f50,plain,(
% 3.50/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.50/1.00    inference(flattening,[],[f49])).
% 3.50/1.00  
% 3.50/1.00  fof(f97,plain,(
% 3.50/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f50])).
% 3.50/1.00  
% 3.50/1.00  fof(f113,plain,(
% 3.50/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f57])).
% 3.50/1.00  
% 3.50/1.00  fof(f96,plain,(
% 3.50/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f50])).
% 3.50/1.00  
% 3.50/1.00  fof(f91,plain,(
% 3.50/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.50/1.00    inference(cnf_transformation,[],[f42])).
% 3.50/1.00  
% 3.50/1.00  fof(f103,plain,(
% 3.50/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.01    inference(cnf_transformation,[],[f65])).
% 3.50/1.01  
% 3.50/1.01  fof(f80,plain,(
% 3.50/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.50/1.01    inference(cnf_transformation,[],[f64])).
% 3.50/1.01  
% 3.50/1.01  cnf(c_47,negated_conjecture,
% 3.50/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.50/1.01      inference(cnf_transformation,[],[f116]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2164,plain,
% 3.50/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_28,plain,
% 3.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.50/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2171,plain,
% 3.50/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.50/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4699,plain,
% 3.50/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_2164,c_2171]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_20,plain,
% 3.50/1.01      ( ~ v2_funct_1(X0)
% 3.50/1.01      | ~ v1_funct_1(X0)
% 3.50/1.01      | ~ v1_relat_1(X0)
% 3.50/1.01      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.50/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_46,negated_conjecture,
% 3.50/1.01      ( v2_funct_1(sK3) ),
% 3.50/1.01      inference(cnf_transformation,[],[f117]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_722,plain,
% 3.50/1.01      ( ~ v1_funct_1(X0)
% 3.50/1.01      | ~ v1_relat_1(X0)
% 3.50/1.01      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.50/1.01      | sK3 != X0 ),
% 3.50/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_46]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_723,plain,
% 3.50/1.01      ( ~ v1_funct_1(sK3)
% 3.50/1.01      | ~ v1_relat_1(sK3)
% 3.50/1.01      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.50/1.01      inference(unflattening,[status(thm)],[c_722]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_49,negated_conjecture,
% 3.50/1.01      ( v1_funct_1(sK3) ),
% 3.50/1.01      inference(cnf_transformation,[],[f114]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_725,plain,
% 3.50/1.01      ( ~ v1_relat_1(sK3) | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.50/1.01      inference(global_propositional_subsumption,[status(thm)],[c_723,c_49]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2154,plain,
% 3.50/1.01      ( k2_funct_1(sK3) = k4_relat_1(sK3) | v1_relat_1(sK3) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4929,plain,
% 3.50/1.01      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_4699,c_2154]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_33,plain,
% 3.50/1.01      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.50/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.50/1.01      inference(cnf_transformation,[],[f127]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_44,negated_conjecture,
% 3.50/1.01      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.50/1.01      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.50/1.01      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.50/1.01      inference(cnf_transformation,[],[f119]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_919,plain,
% 3.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.50/1.01      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.50/1.01      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.50/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.50/1.01      | k2_funct_1(sK3) != X0
% 3.50/1.01      | sK1 != X1
% 3.50/1.01      | sK2 != k1_xboole_0 ),
% 3.50/1.01      inference(resolution_lifted,[status(thm)],[c_33,c_44]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_920,plain,
% 3.50/1.01      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.50/1.01      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.50/1.01      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.50/1.01      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.50/1.01      | sK2 != k1_xboole_0 ),
% 3.50/1.01      inference(unflattening,[status(thm)],[c_919]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2148,plain,
% 3.50/1.01      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.50/1.01      | sK2 != k1_xboole_0
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.50/1.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_920]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_6,plain,
% 3.50/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.50/1.01      inference(cnf_transformation,[],[f123]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2438,plain,
% 3.50/1.01      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.50/1.01      | sK2 != k1_xboole_0
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.50/1.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_2148,c_6]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_50,plain,
% 3.50/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_52,plain,
% 3.50/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_21,plain,
% 3.50/1.01      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.50/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2558,plain,
% 3.50/1.01      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2559,plain,
% 3.50/1.01      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.50/1.01      | v1_funct_1(sK3) != iProver_top
% 3.50/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2558]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2567,plain,
% 3.50/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK3) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_28]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2757,plain,
% 3.50/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.50/1.01      | v1_relat_1(sK3) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_2567]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2758,plain,
% 3.50/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.50/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2757]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2929,plain,
% 3.50/1.01      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.50/1.01      | sK2 != k1_xboole_0
% 3.50/1.01      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 3.50/1.01      inference(global_propositional_subsumption,
% 3.50/1.01                [status(thm)],
% 3.50/1.01                [c_2438,c_50,c_52,c_2559,c_2758]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2930,plain,
% 3.50/1.01      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.50/1.01      | sK2 != k1_xboole_0
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.50/1.01      inference(renaming,[status(thm)],[c_2929]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_5538,plain,
% 3.50/1.01      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 3.50/1.01      | sK2 != k1_xboole_0
% 3.50/1.01      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.50/1.01      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_4929,c_2930]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_0,plain,
% 3.50/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.50/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_48,negated_conjecture,
% 3.50/1.01      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.50/1.01      inference(cnf_transformation,[],[f115]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1045,plain,
% 3.50/1.01      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.50/1.01      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.50/1.01      | k2_funct_1(sK3) != sK3
% 3.50/1.01      | sK1 != sK2 ),
% 3.50/1.01      inference(resolution_lifted,[status(thm)],[c_44,c_48]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1126,plain,
% 3.50/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.50/1.01      theory(equality) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2734,plain,
% 3.50/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_1126]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2736,plain,
% 3.50/1.01      ( v1_xboole_0(sK3) | ~ v1_xboole_0(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_2734]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1125,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2772,plain,
% 3.50/1.01      ( X0 != X1 | k2_funct_1(sK3) != X1 | k2_funct_1(sK3) = X0 ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_1125]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3099,plain,
% 3.50/1.01      ( X0 != k4_relat_1(sK3)
% 3.50/1.01      | k2_funct_1(sK3) = X0
% 3.50/1.01      | k2_funct_1(sK3) != k4_relat_1(sK3) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_2772]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3100,plain,
% 3.50/1.01      ( k2_funct_1(sK3) != k4_relat_1(sK3)
% 3.50/1.01      | k2_funct_1(sK3) = k1_xboole_0
% 3.50/1.01      | k1_xboole_0 != k4_relat_1(sK3) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_3099]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_13,plain,
% 3.50/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k4_relat_1(X0)) ),
% 3.50/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3517,plain,
% 3.50/1.01      ( v1_xboole_0(k4_relat_1(sK3)) | ~ v1_xboole_0(sK3) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1,plain,
% 3.50/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.50/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3545,plain,
% 3.50/1.01      ( ~ v1_xboole_0(k4_relat_1(sK3)) | k1_xboole_0 = k4_relat_1(sK3) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2785,plain,
% 3.50/1.01      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_1125]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3627,plain,
% 3.50/1.01      ( sK1 != X0 | sK1 = sK2 | sK2 != X0 ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_2785]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3628,plain,
% 3.50/1.01      ( sK1 = sK2 | sK1 != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_3627]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4029,plain,
% 3.50/1.01      ( k2_funct_1(sK3) != X0 | k2_funct_1(sK3) = sK3 | sK3 != X0 ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_2772]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4031,plain,
% 3.50/1.01      ( k2_funct_1(sK3) = sK3
% 3.50/1.01      | k2_funct_1(sK3) != k1_xboole_0
% 3.50/1.01      | sK3 != k1_xboole_0 ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_4029]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1130,plain,
% 3.50/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.50/1.01      theory(equality) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2692,plain,
% 3.50/1.01      ( m1_subset_1(X0,X1)
% 3.50/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 3.50/1.01      | X1 != k1_zfmisc_1(X2)
% 3.50/1.01      | X0 != k1_xboole_0 ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_1130]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3292,plain,
% 3.50/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.50/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 3.50/1.01      | X0 != k1_xboole_0
% 3.50/1.01      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_2692]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_5015,plain,
% 3.50/1.01      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.50/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.50/1.01      | k2_funct_1(sK3) != k1_xboole_0
% 3.50/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_3292]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1129,plain,
% 3.50/1.01      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.50/1.01      theory(equality) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3743,plain,
% 3.50/1.01      ( k2_zfmisc_1(sK2,sK1) != X0
% 3.50/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(X0) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_1129]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_6127,plain,
% 3.50/1.01      ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1)
% 3.50/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_3743]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1124,plain,( X0 = X0 ),theory(equality) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_6128,plain,
% 3.50/1.01      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,sK1) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_1124]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2174,plain,
% 3.50/1.01      ( v1_funct_1(X0) != iProver_top
% 3.50/1.01      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.50/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_6886,plain,
% 3.50/1.01      ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
% 3.50/1.01      | v1_funct_1(sK3) != iProver_top
% 3.50/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_4929,c_2174]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_30,plain,
% 3.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.50/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2169,plain,
% 3.50/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.50/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4804,plain,
% 3.50/1.01      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_2164,c_2169]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_45,negated_conjecture,
% 3.50/1.01      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.50/1.01      inference(cnf_transformation,[],[f118]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4816,plain,
% 3.50/1.01      ( k2_relat_1(sK3) = sK2 ),
% 3.50/1.01      inference(light_normalisation,[status(thm)],[c_4804,c_45]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_32,plain,
% 3.50/1.01      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.50/1.01      | k1_xboole_0 = X1
% 3.50/1.01      | k1_xboole_0 = X0 ),
% 3.50/1.01      inference(cnf_transformation,[],[f126]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_42,plain,
% 3.50/1.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.50/1.01      | ~ v1_funct_1(X0)
% 3.50/1.01      | ~ v1_relat_1(X0) ),
% 3.50/1.01      inference(cnf_transformation,[],[f112]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_838,plain,
% 3.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.50/1.01      | ~ v1_funct_1(X2)
% 3.50/1.01      | ~ v1_relat_1(X2)
% 3.50/1.01      | X2 != X0
% 3.50/1.01      | k2_relat_1(X2) != k1_xboole_0
% 3.50/1.01      | k1_relat_1(X2) != X1
% 3.50/1.01      | k1_xboole_0 = X0
% 3.50/1.01      | k1_xboole_0 = X1 ),
% 3.50/1.01      inference(resolution_lifted,[status(thm)],[c_32,c_42]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_839,plain,
% 3.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.50/1.01      | ~ v1_funct_1(X0)
% 3.50/1.01      | ~ v1_relat_1(X0)
% 3.50/1.01      | k2_relat_1(X0) != k1_xboole_0
% 3.50/1.01      | k1_xboole_0 = X0
% 3.50/1.01      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.50/1.01      inference(unflattening,[status(thm)],[c_838]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_855,plain,
% 3.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.50/1.01      | ~ v1_funct_1(X0)
% 3.50/1.01      | k2_relat_1(X0) != k1_xboole_0
% 3.50/1.01      | k1_xboole_0 = X0
% 3.50/1.01      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.50/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_839,c_28]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2151,plain,
% 3.50/1.01      ( k2_relat_1(X0) != k1_xboole_0
% 3.50/1.01      | k1_xboole_0 = X0
% 3.50/1.01      | k1_xboole_0 = k1_relat_1(X0)
% 3.50/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
% 3.50/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_855]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_5,plain,
% 3.50/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.50/1.01      inference(cnf_transformation,[],[f122]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2417,plain,
% 3.50/1.01      ( k2_relat_1(X0) != k1_xboole_0
% 3.50/1.01      | k1_relat_1(X0) = k1_xboole_0
% 3.50/1.01      | k1_xboole_0 = X0
% 3.50/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.50/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_2151,c_5]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_7732,plain,
% 3.50/1.01      ( k1_relat_1(sK3) = k1_xboole_0
% 3.50/1.01      | sK2 != k1_xboole_0
% 3.50/1.01      | sK3 = k1_xboole_0
% 3.50/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.50/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_4816,c_2417]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2,plain,
% 3.50/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.50/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2792,plain,
% 3.50/1.01      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2793,plain,
% 3.50/1.01      ( sK3 = X0
% 3.50/1.01      | r1_tarski(X0,sK3) != iProver_top
% 3.50/1.01      | r1_tarski(sK3,X0) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2792]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2795,plain,
% 3.50/1.01      ( sK3 = k1_xboole_0
% 3.50/1.01      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.50/1.01      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_2793]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_10,plain,
% 3.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.50/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3079,plain,
% 3.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3080,plain,
% 3.50/1.01      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 3.50/1.01      | r1_tarski(X0,sK3) = iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_3079]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3082,plain,
% 3.50/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 3.50/1.01      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_3080]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8,plain,
% 3.50/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.50/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4316,plain,
% 3.50/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4319,plain,
% 3.50/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_4316]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4565,plain,
% 3.50/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4566,plain,
% 3.50/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.50/1.01      | r1_tarski(sK3,X0) = iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_4565]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4568,plain,
% 3.50/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.50/1.01      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_4566]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8086,plain,
% 3.50/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.50/1.01      | sK3 = k1_xboole_0 ),
% 3.50/1.01      inference(global_propositional_subsumption,
% 3.50/1.01                [status(thm)],
% 3.50/1.01                [c_7732,c_2795,c_3082,c_4319,c_4568]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8087,plain,
% 3.50/1.01      ( sK3 = k1_xboole_0
% 3.50/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.50/1.01      inference(renaming,[status(thm)],[c_8086]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_36,plain,
% 3.50/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.50/1.01      | k1_xboole_0 = X2 ),
% 3.50/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1002,plain,
% 3.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.50/1.01      | sK1 != X1
% 3.50/1.01      | sK2 != X2
% 3.50/1.01      | sK3 != X0
% 3.50/1.01      | k1_xboole_0 = X2 ),
% 3.50/1.01      inference(resolution_lifted,[status(thm)],[c_36,c_48]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1003,plain,
% 3.50/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.50/1.01      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.50/1.01      | k1_xboole_0 = sK2 ),
% 3.50/1.01      inference(unflattening,[status(thm)],[c_1002]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1005,plain,
% 3.50/1.01      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.50/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1003,c_47]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_29,plain,
% 3.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.50/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2170,plain,
% 3.50/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.50/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_6073,plain,
% 3.50/1.01      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_2164,c_2170]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_6215,plain,
% 3.50/1.01      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_1005,c_6073]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_26,plain,
% 3.50/1.01      ( ~ v2_funct_1(X0)
% 3.50/1.01      | ~ v1_funct_1(X0)
% 3.50/1.01      | ~ v1_relat_1(X0)
% 3.50/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.50/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_690,plain,
% 3.50/1.01      ( ~ v1_funct_1(X0)
% 3.50/1.01      | ~ v1_relat_1(X0)
% 3.50/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.50/1.01      | sK3 != X0 ),
% 3.50/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_46]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_691,plain,
% 3.50/1.01      ( ~ v1_funct_1(sK3)
% 3.50/1.01      | ~ v1_relat_1(sK3)
% 3.50/1.01      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.50/1.01      inference(unflattening,[status(thm)],[c_690]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_693,plain,
% 3.50/1.01      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.50/1.01      inference(global_propositional_subsumption,[status(thm)],[c_691,c_49]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2156,plain,
% 3.50/1.01      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.50/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4928,plain,
% 3.50/1.01      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_4699,c_2156]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4932,plain,
% 3.50/1.01      ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
% 3.50/1.01      inference(light_normalisation,[status(thm)],[c_4928,c_4929]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_41,plain,
% 3.50/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.50/1.01      | ~ v1_funct_1(X0)
% 3.50/1.01      | ~ v1_relat_1(X0) ),
% 3.50/1.01      inference(cnf_transformation,[],[f113]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2165,plain,
% 3.50/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.50/1.01      | v1_funct_1(X0) != iProver_top
% 3.50/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_7491,plain,
% 3.50/1.01      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.50/1.01      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.50/1.01      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_4932,c_2165]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_27,plain,
% 3.50/1.01      ( ~ v2_funct_1(X0)
% 3.50/1.01      | ~ v1_funct_1(X0)
% 3.50/1.01      | ~ v1_relat_1(X0)
% 3.50/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.50/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_676,plain,
% 3.50/1.01      ( ~ v1_funct_1(X0)
% 3.50/1.01      | ~ v1_relat_1(X0)
% 3.50/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.50/1.01      | sK3 != X0 ),
% 3.50/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_46]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_677,plain,
% 3.50/1.01      ( ~ v1_funct_1(sK3)
% 3.50/1.01      | ~ v1_relat_1(sK3)
% 3.50/1.01      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.50/1.01      inference(unflattening,[status(thm)],[c_676]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_679,plain,
% 3.50/1.01      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.50/1.01      inference(global_propositional_subsumption,[status(thm)],[c_677,c_49]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2157,plain,
% 3.50/1.01      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.50/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4915,plain,
% 3.50/1.01      ( k1_relat_1(k2_funct_1(sK3)) = sK2 | v1_relat_1(sK3) != iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_4816,c_2157]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_5365,plain,
% 3.50/1.01      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.50/1.01      inference(global_propositional_subsumption,
% 3.50/1.01                [status(thm)],
% 3.50/1.01                [c_4915,c_52,c_2758]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_5536,plain,
% 3.50/1.01      ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_4929,c_5365]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_7492,plain,
% 3.50/1.01      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.50/1.01      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 3.50/1.01      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 3.50/1.01      inference(light_normalisation,[status(thm)],[c_7491,c_5536]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_22,plain,
% 3.50/1.01      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.50/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2173,plain,
% 3.50/1.01      ( v1_funct_1(X0) != iProver_top
% 3.50/1.01      | v1_relat_1(X0) != iProver_top
% 3.50/1.01      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_6853,plain,
% 3.50/1.01      ( v1_funct_1(sK3) != iProver_top
% 3.50/1.01      | v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 3.50/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_4929,c_2173]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8614,plain,
% 3.50/1.01      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.50/1.01      inference(global_propositional_subsumption,
% 3.50/1.01                [status(thm)],
% 3.50/1.01                [c_7492,c_50,c_52,c_2758,c_6853,c_6886]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8619,plain,
% 3.50/1.01      ( sK2 = k1_xboole_0
% 3.50/1.01      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_6215,c_8614]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1026,plain,
% 3.50/1.01      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.50/1.01      | ~ v1_funct_1(X0)
% 3.50/1.01      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.50/1.01      | ~ v1_relat_1(X0)
% 3.50/1.01      | k2_funct_1(sK3) != X0
% 3.50/1.01      | k2_relat_1(X0) != sK1
% 3.50/1.01      | k1_relat_1(X0) != sK2 ),
% 3.50/1.01      inference(resolution_lifted,[status(thm)],[c_42,c_44]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1027,plain,
% 3.50/1.01      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.50/1.01      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.50/1.01      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.50/1.01      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.50/1.01      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.50/1.01      inference(unflattening,[status(thm)],[c_1026]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1039,plain,
% 3.50/1.01      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.50/1.01      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.50/1.01      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.50/1.01      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.50/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_1027,c_28]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2143,plain,
% 3.50/1.01      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.50/1.01      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.50/1.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1039]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_1044,plain,
% 3.50/1.01      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.50/1.01      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.50/1.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1039]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2823,plain,
% 3.50/1.01      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.50/1.01      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.50/1.01      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.50/1.01      inference(global_propositional_subsumption,
% 3.50/1.01                [status(thm)],
% 3.50/1.01                [c_2143,c_50,c_52,c_1044,c_2559,c_2758]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2824,plain,
% 3.50/1.01      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.50/1.01      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.50/1.01      inference(renaming,[status(thm)],[c_2823]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_5368,plain,
% 3.50/1.01      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.50/1.01      | sK2 != sK2
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_5365,c_2824]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_6369,plain,
% 3.50/1.01      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.50/1.01      inference(equality_resolution_simp,[status(thm)],[c_5368]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_6371,plain,
% 3.50/1.01      ( k2_relat_1(k4_relat_1(sK3)) != sK1
% 3.50/1.01      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.50/1.01      inference(light_normalisation,[status(thm)],[c_6369,c_4929]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_7489,plain,
% 3.50/1.01      ( k1_relat_1(sK3) != sK1
% 3.50/1.01      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_4932,c_6371]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8901,plain,
% 3.50/1.01      ( sK2 = k1_xboole_0 ),
% 3.50/1.01      inference(global_propositional_subsumption,
% 3.50/1.01                [status(thm)],
% 3.50/1.01                [c_8619,c_6215,c_7489]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8931,plain,
% 3.50/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_8901,c_2164]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8936,plain,
% 3.50/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_8931,c_5]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8904,plain,
% 3.50/1.01      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_8901,c_8614]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_9010,plain,
% 3.50/1.01      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_8904,c_6]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_34,plain,
% 3.50/1.01      ( v1_funct_2(X0,X1,X2)
% 3.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.01      | k1_relset_1(X1,X2,X0) != X1
% 3.50/1.01      | k1_xboole_0 = X2 ),
% 3.50/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_986,plain,
% 3.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.01      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.50/1.01      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.50/1.01      | k1_relset_1(X1,X2,X0) != X1
% 3.50/1.01      | k2_funct_1(sK3) != X0
% 3.50/1.01      | sK1 != X2
% 3.50/1.01      | sK2 != X1
% 3.50/1.01      | k1_xboole_0 = X2 ),
% 3.50/1.01      inference(resolution_lifted,[status(thm)],[c_34,c_44]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_987,plain,
% 3.50/1.01      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.50/1.01      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.50/1.01      | k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 3.50/1.01      | k1_xboole_0 = sK1 ),
% 3.50/1.01      inference(unflattening,[status(thm)],[c_986]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2145,plain,
% 3.50/1.01      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) != sK2
% 3.50/1.01      | k1_xboole_0 = sK1
% 3.50/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.50/1.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_987]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_5540,plain,
% 3.50/1.01      ( k1_relset_1(sK2,sK1,k4_relat_1(sK3)) != sK2
% 3.50/1.01      | sK1 = k1_xboole_0
% 3.50/1.01      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.50/1.01      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_4929,c_2145]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8917,plain,
% 3.50/1.01      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 3.50/1.01      | sK1 = k1_xboole_0
% 3.50/1.01      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.50/1.01      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_8901,c_5540]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8982,plain,
% 3.50/1.01      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 3.50/1.01      | sK1 = k1_xboole_0
% 3.50/1.01      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.50/1.01      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_8917,c_6]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_9014,plain,
% 3.50/1.01      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0
% 3.50/1.01      | sK1 = k1_xboole_0
% 3.50/1.01      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 3.50/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_9010,c_8982]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2607,plain,
% 3.50/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_11342,plain,
% 3.50/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.50/1.01      inference(instantiation,[status(thm)],[c_2607]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_11691,plain,
% 3.50/1.01      ( k1_relset_1(k1_xboole_0,sK1,k4_relat_1(sK3)) != k1_xboole_0 ),
% 3.50/1.01      inference(global_propositional_subsumption,
% 3.50/1.01                [status(thm)],
% 3.50/1.01                [c_5538,c_49,c_50,c_47,c_52,c_0,c_723,c_1045,c_2558,c_2736,
% 3.50/1.01                 c_2757,c_2758,c_3100,c_3517,c_3545,c_3628,c_4031,c_5015,
% 3.50/1.01                 c_6127,c_6128,c_6215,c_6886,c_7489,c_8087,c_8619,c_8936,
% 3.50/1.01                 c_9014,c_11342]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2187,plain,
% 3.50/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2178,plain,
% 3.50/1.01      ( v1_xboole_0(X0) != iProver_top
% 3.50/1.01      | v1_xboole_0(k4_relat_1(X0)) = iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2186,plain,
% 3.50/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3768,plain,
% 3.50/1.01      ( k4_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_2178,c_2186]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_3793,plain,
% 3.50/1.01      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_2187,c_3768]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2181,plain,
% 3.50/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.50/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_4191,plain,
% 3.50/1.01      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_2164,c_2181]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8927,plain,
% 3.50/1.01      ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_8901,c_4191]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8946,plain,
% 3.50/1.01      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_8927,c_5]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_9,plain,
% 3.50/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.50/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_2182,plain,
% 3.50/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.50/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.50/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8092,plain,
% 3.50/1.01      ( sK3 = k1_xboole_0 | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_2182,c_8087]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_9328,plain,
% 3.50/1.01      ( sK3 = k1_xboole_0 ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_8946,c_8092]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_11693,plain,
% 3.50/1.01      ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k1_xboole_0 ),
% 3.50/1.01      inference(light_normalisation,[status(thm)],[c_11691,c_3793,c_9328]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_6075,plain,
% 3.50/1.01      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.50/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_6,c_2170]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_9414,plain,
% 3.50/1.01      ( k1_relset_1(k1_xboole_0,X0,k4_relat_1(sK3)) = k1_relat_1(k4_relat_1(sK3)) ),
% 3.50/1.01      inference(superposition,[status(thm)],[c_9010,c_6075]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_8922,plain,
% 3.50/1.01      ( k1_relat_1(k4_relat_1(sK3)) = k1_xboole_0 ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_8901,c_5536]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_10117,plain,
% 3.50/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.50/1.01      inference(light_normalisation,[status(thm)],[c_8922,c_3793,c_9328]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_11293,plain,
% 3.50/1.01      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 3.50/1.01      inference(light_normalisation,
% 3.50/1.01                [status(thm)],
% 3.50/1.01                [c_9414,c_3793,c_9328,c_10117]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_11694,plain,
% 3.50/1.01      ( k1_xboole_0 != k1_xboole_0 ),
% 3.50/1.01      inference(demodulation,[status(thm)],[c_11693,c_11293]) ).
% 3.50/1.01  
% 3.50/1.01  cnf(c_11695,plain,
% 3.50/1.01      ( $false ),
% 3.50/1.01      inference(equality_resolution_simp,[status(thm)],[c_11694]) ).
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/1.01  
% 3.50/1.01  ------                               Statistics
% 3.50/1.01  
% 3.50/1.01  ------ General
% 3.50/1.01  
% 3.50/1.01  abstr_ref_over_cycles:                  0
% 3.50/1.01  abstr_ref_under_cycles:                 0
% 3.50/1.01  gc_basic_clause_elim:                   0
% 3.50/1.01  forced_gc_time:                         0
% 3.50/1.01  parsing_time:                           0.008
% 3.50/1.01  unif_index_cands_time:                  0.
% 3.50/1.01  unif_index_add_time:                    0.
% 3.50/1.01  orderings_time:                         0.
% 3.50/1.01  out_proof_time:                         0.016
% 3.50/1.01  total_time:                             0.245
% 3.50/1.01  num_of_symbols:                         53
% 3.50/1.01  num_of_terms:                           7451
% 3.50/1.01  
% 3.50/1.01  ------ Preprocessing
% 3.50/1.01  
% 3.50/1.01  num_of_splits:                          0
% 3.50/1.01  num_of_split_atoms:                     0
% 3.50/1.01  num_of_reused_defs:                     0
% 3.50/1.01  num_eq_ax_congr_red:                    7
% 3.50/1.01  num_of_sem_filtered_clauses:            1
% 3.50/1.01  num_of_subtypes:                        0
% 3.50/1.01  monotx_restored_types:                  0
% 3.50/1.01  sat_num_of_epr_types:                   0
% 3.50/1.01  sat_num_of_non_cyclic_types:            0
% 3.50/1.01  sat_guarded_non_collapsed_types:        0
% 3.50/1.01  num_pure_diseq_elim:                    0
% 3.50/1.01  simp_replaced_by:                       0
% 3.50/1.01  res_preprocessed:                       191
% 3.50/1.01  prep_upred:                             0
% 3.50/1.01  prep_unflattend:                        58
% 3.50/1.01  smt_new_axioms:                         0
% 3.50/1.01  pred_elim_cands:                        7
% 3.50/1.01  pred_elim:                              2
% 3.50/1.01  pred_elim_cl:                           -8
% 3.50/1.01  pred_elim_cycles:                       3
% 3.50/1.01  merged_defs:                            6
% 3.50/1.01  merged_defs_ncl:                        0
% 3.50/1.01  bin_hyper_res:                          6
% 3.50/1.01  prep_cycles:                            3
% 3.50/1.01  pred_elim_time:                         0.007
% 3.50/1.01  splitting_time:                         0.
% 3.50/1.01  sem_filter_time:                        0.
% 3.50/1.01  monotx_time:                            0.
% 3.50/1.01  subtype_inf_time:                       0.
% 3.50/1.01  
% 3.50/1.01  ------ Problem properties
% 3.50/1.01  
% 3.50/1.01  clauses:                                54
% 3.50/1.01  conjectures:                            3
% 3.50/1.01  epr:                                    7
% 3.50/1.01  horn:                                   47
% 3.50/1.01  ground:                                 16
% 3.50/1.01  unary:                                  12
% 3.50/1.01  binary:                                 23
% 3.50/1.01  lits:                                   128
% 3.50/1.01  lits_eq:                                54
% 3.50/1.01  fd_pure:                                0
% 3.50/1.01  fd_pseudo:                              0
% 3.50/1.01  fd_cond:                                4
% 3.50/1.01  fd_pseudo_cond:                         1
% 3.50/1.01  ac_symbols:                             0
% 3.50/1.01  
% 3.50/1.01  ------ Propositional Solver
% 3.50/1.01  
% 3.50/1.01  prop_solver_calls:                      24
% 3.50/1.01  prop_fast_solver_calls:                 1411
% 3.50/1.01  smt_solver_calls:                       0
% 3.50/1.01  smt_fast_solver_calls:                  0
% 3.50/1.01  prop_num_of_clauses:                    3977
% 3.50/1.01  prop_preprocess_simplified:             12443
% 3.50/1.01  prop_fo_subsumed:                       55
% 3.50/1.01  prop_solver_time:                       0.
% 3.50/1.01  smt_solver_time:                        0.
% 3.50/1.01  smt_fast_solver_time:                   0.
% 3.50/1.01  prop_fast_solver_time:                  0.
% 3.50/1.01  prop_unsat_core_time:                   0.
% 3.50/1.01  
% 3.50/1.01  ------ QBF
% 3.50/1.01  
% 3.50/1.01  qbf_q_res:                              0
% 3.50/1.01  qbf_num_tautologies:                    0
% 3.50/1.01  qbf_prep_cycles:                        0
% 3.50/1.01  
% 3.50/1.01  ------ BMC1
% 3.50/1.01  
% 3.50/1.01  bmc1_current_bound:                     -1
% 3.50/1.01  bmc1_last_solved_bound:                 -1
% 3.50/1.01  bmc1_unsat_core_size:                   -1
% 3.50/1.01  bmc1_unsat_core_parents_size:           -1
% 3.50/1.01  bmc1_merge_next_fun:                    0
% 3.50/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.50/1.01  
% 3.50/1.01  ------ Instantiation
% 3.50/1.01  
% 3.50/1.01  inst_num_of_clauses:                    1249
% 3.50/1.01  inst_num_in_passive:                    700
% 3.50/1.01  inst_num_in_active:                     509
% 3.50/1.01  inst_num_in_unprocessed:                41
% 3.50/1.01  inst_num_of_loops:                      750
% 3.50/1.01  inst_num_of_learning_restarts:          0
% 3.50/1.01  inst_num_moves_active_passive:          238
% 3.50/1.01  inst_lit_activity:                      0
% 3.50/1.01  inst_lit_activity_moves:                0
% 3.50/1.01  inst_num_tautologies:                   0
% 3.50/1.01  inst_num_prop_implied:                  0
% 3.50/1.01  inst_num_existing_simplified:           0
% 3.50/1.01  inst_num_eq_res_simplified:             0
% 3.50/1.01  inst_num_child_elim:                    0
% 3.50/1.01  inst_num_of_dismatching_blockings:      651
% 3.50/1.01  inst_num_of_non_proper_insts:           1515
% 3.50/1.01  inst_num_of_duplicates:                 0
% 3.50/1.01  inst_inst_num_from_inst_to_res:         0
% 3.50/1.01  inst_dismatching_checking_time:         0.
% 3.50/1.01  
% 3.50/1.01  ------ Resolution
% 3.50/1.01  
% 3.50/1.01  res_num_of_clauses:                     0
% 3.50/1.01  res_num_in_passive:                     0
% 3.50/1.01  res_num_in_active:                      0
% 3.50/1.01  res_num_of_loops:                       194
% 3.50/1.01  res_forward_subset_subsumed:            47
% 3.50/1.01  res_backward_subset_subsumed:           8
% 3.50/1.01  res_forward_subsumed:                   0
% 3.50/1.01  res_backward_subsumed:                  0
% 3.50/1.01  res_forward_subsumption_resolution:     8
% 3.50/1.01  res_backward_subsumption_resolution:    0
% 3.50/1.01  res_clause_to_clause_subsumption:       459
% 3.50/1.01  res_orphan_elimination:                 0
% 3.50/1.01  res_tautology_del:                      122
% 3.50/1.01  res_num_eq_res_simplified:              0
% 3.50/1.01  res_num_sel_changes:                    0
% 3.50/1.01  res_moves_from_active_to_pass:          0
% 3.50/1.01  
% 3.50/1.01  ------ Superposition
% 3.50/1.01  
% 3.50/1.01  sup_time_total:                         0.
% 3.50/1.01  sup_time_generating:                    0.
% 3.50/1.01  sup_time_sim_full:                      0.
% 3.50/1.01  sup_time_sim_immed:                     0.
% 3.50/1.01  
% 3.50/1.01  sup_num_of_clauses:                     148
% 3.50/1.01  sup_num_in_active:                      73
% 3.50/1.01  sup_num_in_passive:                     75
% 3.50/1.01  sup_num_of_loops:                       148
% 3.50/1.01  sup_fw_superposition:                   137
% 3.50/1.01  sup_bw_superposition:                   72
% 3.50/1.01  sup_immediate_simplified:               90
% 3.50/1.01  sup_given_eliminated:                   1
% 3.50/1.01  comparisons_done:                       0
% 3.50/1.01  comparisons_avoided:                    11
% 3.50/1.01  
% 3.50/1.01  ------ Simplifications
% 3.50/1.01  
% 3.50/1.01  
% 3.50/1.01  sim_fw_subset_subsumed:                 20
% 3.50/1.01  sim_bw_subset_subsumed:                 7
% 3.50/1.01  sim_fw_subsumed:                        22
% 3.50/1.01  sim_bw_subsumed:                        1
% 3.50/1.01  sim_fw_subsumption_res:                 1
% 3.50/1.01  sim_bw_subsumption_res:                 3
% 3.50/1.01  sim_tautology_del:                      3
% 3.50/1.01  sim_eq_tautology_del:                   21
% 3.50/1.01  sim_eq_res_simp:                        2
% 3.50/1.01  sim_fw_demodulated:                     25
% 3.50/1.01  sim_bw_demodulated:                     72
% 3.50/1.01  sim_light_normalised:                   61
% 3.50/1.01  sim_joinable_taut:                      0
% 3.50/1.01  sim_joinable_simp:                      0
% 3.50/1.01  sim_ac_normalised:                      0
% 3.50/1.01  sim_smt_subsumption:                    0
% 3.50/1.01  
%------------------------------------------------------------------------------

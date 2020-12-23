%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:21 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  153 (2438 expanded)
%              Number of clauses        :   91 ( 775 expanded)
%              Number of leaves         :   17 ( 473 expanded)
%              Depth                    :   25
%              Number of atoms          :  466 (12936 expanded)
%              Number of equality atoms :  211 (2401 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,axiom,(
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

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

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
    inference(nnf_transformation,[],[f59])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f29,conjecture,(
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

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f62,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f63,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f62])).

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
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f63,f68])).

fof(f116,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

fof(f117,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f118,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f98,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f119,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f69])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f91,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f115,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f60])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f92,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f120,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f69])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f64])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f122,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_49,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_916,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_49])).

cnf(c_917,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_48,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_919,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_917,c_48])).

cnf(c_2254,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2258,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5645,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2254,c_2258])).

cnf(c_5835,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_919,c_5645])).

cnf(c_47,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2255,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_29,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2263,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6866,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2255,c_2263])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2257,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4656,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2254,c_2257])).

cnf(c_46,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_4658,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4656,c_46])).

cnf(c_21,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2271,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6324,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2255,c_2271])).

cnf(c_50,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_653,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_47])).

cnf(c_654,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2807,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_3131,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2807])).

cnf(c_6492,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6324,c_50,c_48,c_654,c_3131])).

cnf(c_6887,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6866,c_4658,c_6492])).

cnf(c_51,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_3132,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3131])).

cnf(c_7138,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6887,c_51,c_53,c_3132])).

cnf(c_42,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2256,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_7143,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7138,c_2256])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2270,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6547,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6492,c_2270])).

cnf(c_23,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2269,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6548,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6492,c_2269])).

cnf(c_7215,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7143,c_51,c_53,c_3132,c_6547,c_6548])).

cnf(c_28,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2264,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7008,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2255,c_2264])).

cnf(c_7029,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7008,c_6492])).

cnf(c_7170,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7029,c_51,c_53,c_3132])).

cnf(c_7221,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7215,c_7170])).

cnf(c_43,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_45,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_927,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_45])).

cnf(c_928,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_927])).

cnf(c_940,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_928,c_32])).

cnf(c_2243,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_6497,plain,
    ( k1_relat_1(k4_relat_1(sK2)) != sK1
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6492,c_2243])).

cnf(c_6853,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k4_relat_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6497,c_51,c_53,c_3132,c_6547])).

cnf(c_6854,plain,
    ( k1_relat_1(k4_relat_1(sK2)) != sK1
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6853])).

cnf(c_7141,plain,
    ( sK1 != sK1
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7138,c_6854])).

cnf(c_7208,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7141])).

cnf(c_7210,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7208,c_7170])).

cnf(c_7231,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7221,c_7210])).

cnf(c_14153,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5835,c_7231])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_4296,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4299,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4296])).

cnf(c_14377,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14153,c_4299])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2259,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6116,plain,
    ( v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2254,c_2259])).

cnf(c_14410,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14377,c_6116])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_158,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1508,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3943,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_3944,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3943])).

cnf(c_3946,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3944])).

cnf(c_15075,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14410,c_158,c_3946,c_4299,c_6116,c_14153])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2283,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15094,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15075,c_2283])).

cnf(c_15459,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15094,c_7231])).

cnf(c_14,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_15555,plain,
    ( r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15459,c_14])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6695,plain,
    ( r1_tarski(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6698,plain,
    ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6695])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15555,c_6698])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:23:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.54/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/0.98  
% 3.54/0.98  ------  iProver source info
% 3.54/0.98  
% 3.54/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.54/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/0.98  git: non_committed_changes: false
% 3.54/0.98  git: last_make_outside_of_git: false
% 3.54/0.98  
% 3.54/0.98  ------ 
% 3.54/0.98  
% 3.54/0.98  ------ Input Options
% 3.54/0.98  
% 3.54/0.98  --out_options                           all
% 3.54/0.98  --tptp_safe_out                         true
% 3.54/0.98  --problem_path                          ""
% 3.54/0.98  --include_path                          ""
% 3.54/0.98  --clausifier                            res/vclausify_rel
% 3.54/0.98  --clausifier_options                    --mode clausify
% 3.54/0.98  --stdin                                 false
% 3.54/0.98  --stats_out                             all
% 3.54/0.98  
% 3.54/0.98  ------ General Options
% 3.54/0.98  
% 3.54/0.98  --fof                                   false
% 3.54/0.98  --time_out_real                         305.
% 3.54/0.98  --time_out_virtual                      -1.
% 3.54/0.98  --symbol_type_check                     false
% 3.54/0.98  --clausify_out                          false
% 3.54/0.98  --sig_cnt_out                           false
% 3.54/0.98  --trig_cnt_out                          false
% 3.54/0.98  --trig_cnt_out_tolerance                1.
% 3.54/0.98  --trig_cnt_out_sk_spl                   false
% 3.54/0.98  --abstr_cl_out                          false
% 3.54/0.98  
% 3.54/0.98  ------ Global Options
% 3.54/0.98  
% 3.54/0.98  --schedule                              default
% 3.54/0.98  --add_important_lit                     false
% 3.54/0.98  --prop_solver_per_cl                    1000
% 3.54/0.98  --min_unsat_core                        false
% 3.54/0.98  --soft_assumptions                      false
% 3.54/0.98  --soft_lemma_size                       3
% 3.54/0.98  --prop_impl_unit_size                   0
% 3.54/0.98  --prop_impl_unit                        []
% 3.54/0.98  --share_sel_clauses                     true
% 3.54/0.98  --reset_solvers                         false
% 3.54/0.98  --bc_imp_inh                            [conj_cone]
% 3.54/0.98  --conj_cone_tolerance                   3.
% 3.54/0.98  --extra_neg_conj                        none
% 3.54/0.98  --large_theory_mode                     true
% 3.54/0.98  --prolific_symb_bound                   200
% 3.54/0.98  --lt_threshold                          2000
% 3.54/0.98  --clause_weak_htbl                      true
% 3.54/0.98  --gc_record_bc_elim                     false
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing Options
% 3.54/0.98  
% 3.54/0.98  --preprocessing_flag                    true
% 3.54/0.98  --time_out_prep_mult                    0.1
% 3.54/0.98  --splitting_mode                        input
% 3.54/0.98  --splitting_grd                         true
% 3.54/0.98  --splitting_cvd                         false
% 3.54/0.98  --splitting_cvd_svl                     false
% 3.54/0.98  --splitting_nvd                         32
% 3.54/0.98  --sub_typing                            true
% 3.54/0.98  --prep_gs_sim                           true
% 3.54/0.98  --prep_unflatten                        true
% 3.54/0.98  --prep_res_sim                          true
% 3.54/0.98  --prep_upred                            true
% 3.54/0.98  --prep_sem_filter                       exhaustive
% 3.54/0.98  --prep_sem_filter_out                   false
% 3.54/0.98  --pred_elim                             true
% 3.54/0.98  --res_sim_input                         true
% 3.54/0.98  --eq_ax_congr_red                       true
% 3.54/0.98  --pure_diseq_elim                       true
% 3.54/0.98  --brand_transform                       false
% 3.54/0.98  --non_eq_to_eq                          false
% 3.54/0.98  --prep_def_merge                        true
% 3.54/0.98  --prep_def_merge_prop_impl              false
% 3.54/0.98  --prep_def_merge_mbd                    true
% 3.54/0.98  --prep_def_merge_tr_red                 false
% 3.54/0.98  --prep_def_merge_tr_cl                  false
% 3.54/0.98  --smt_preprocessing                     true
% 3.54/0.98  --smt_ac_axioms                         fast
% 3.54/0.98  --preprocessed_out                      false
% 3.54/0.98  --preprocessed_stats                    false
% 3.54/0.98  
% 3.54/0.98  ------ Abstraction refinement Options
% 3.54/0.98  
% 3.54/0.98  --abstr_ref                             []
% 3.54/0.98  --abstr_ref_prep                        false
% 3.54/0.98  --abstr_ref_until_sat                   false
% 3.54/0.98  --abstr_ref_sig_restrict                funpre
% 3.54/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/0.98  --abstr_ref_under                       []
% 3.54/0.98  
% 3.54/0.98  ------ SAT Options
% 3.54/0.98  
% 3.54/0.98  --sat_mode                              false
% 3.54/0.98  --sat_fm_restart_options                ""
% 3.54/0.98  --sat_gr_def                            false
% 3.54/0.98  --sat_epr_types                         true
% 3.54/0.98  --sat_non_cyclic_types                  false
% 3.54/0.98  --sat_finite_models                     false
% 3.54/0.98  --sat_fm_lemmas                         false
% 3.54/0.98  --sat_fm_prep                           false
% 3.54/0.98  --sat_fm_uc_incr                        true
% 3.54/0.98  --sat_out_model                         small
% 3.54/0.98  --sat_out_clauses                       false
% 3.54/0.98  
% 3.54/0.98  ------ QBF Options
% 3.54/0.98  
% 3.54/0.98  --qbf_mode                              false
% 3.54/0.98  --qbf_elim_univ                         false
% 3.54/0.98  --qbf_dom_inst                          none
% 3.54/0.98  --qbf_dom_pre_inst                      false
% 3.54/0.98  --qbf_sk_in                             false
% 3.54/0.98  --qbf_pred_elim                         true
% 3.54/0.98  --qbf_split                             512
% 3.54/0.98  
% 3.54/0.98  ------ BMC1 Options
% 3.54/0.98  
% 3.54/0.98  --bmc1_incremental                      false
% 3.54/0.98  --bmc1_axioms                           reachable_all
% 3.54/0.98  --bmc1_min_bound                        0
% 3.54/0.98  --bmc1_max_bound                        -1
% 3.54/0.98  --bmc1_max_bound_default                -1
% 3.54/0.98  --bmc1_symbol_reachability              true
% 3.54/0.98  --bmc1_property_lemmas                  false
% 3.54/0.98  --bmc1_k_induction                      false
% 3.54/0.98  --bmc1_non_equiv_states                 false
% 3.54/0.98  --bmc1_deadlock                         false
% 3.54/0.98  --bmc1_ucm                              false
% 3.54/0.98  --bmc1_add_unsat_core                   none
% 3.54/0.98  --bmc1_unsat_core_children              false
% 3.54/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/0.98  --bmc1_out_stat                         full
% 3.54/0.98  --bmc1_ground_init                      false
% 3.54/0.98  --bmc1_pre_inst_next_state              false
% 3.54/0.98  --bmc1_pre_inst_state                   false
% 3.54/0.98  --bmc1_pre_inst_reach_state             false
% 3.54/0.98  --bmc1_out_unsat_core                   false
% 3.54/0.98  --bmc1_aig_witness_out                  false
% 3.54/0.98  --bmc1_verbose                          false
% 3.54/0.98  --bmc1_dump_clauses_tptp                false
% 3.54/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.54/0.98  --bmc1_dump_file                        -
% 3.54/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.54/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.54/0.98  --bmc1_ucm_extend_mode                  1
% 3.54/0.98  --bmc1_ucm_init_mode                    2
% 3.54/0.98  --bmc1_ucm_cone_mode                    none
% 3.54/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.54/0.98  --bmc1_ucm_relax_model                  4
% 3.54/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.54/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/0.98  --bmc1_ucm_layered_model                none
% 3.54/0.98  --bmc1_ucm_max_lemma_size               10
% 3.54/0.98  
% 3.54/0.98  ------ AIG Options
% 3.54/0.98  
% 3.54/0.98  --aig_mode                              false
% 3.54/0.98  
% 3.54/0.98  ------ Instantiation Options
% 3.54/0.98  
% 3.54/0.98  --instantiation_flag                    true
% 3.54/0.98  --inst_sos_flag                         false
% 3.54/0.98  --inst_sos_phase                        true
% 3.54/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/0.98  --inst_lit_sel_side                     num_symb
% 3.54/0.98  --inst_solver_per_active                1400
% 3.54/0.98  --inst_solver_calls_frac                1.
% 3.54/0.98  --inst_passive_queue_type               priority_queues
% 3.54/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/0.98  --inst_passive_queues_freq              [25;2]
% 3.54/0.98  --inst_dismatching                      true
% 3.54/0.98  --inst_eager_unprocessed_to_passive     true
% 3.54/0.98  --inst_prop_sim_given                   true
% 3.54/0.98  --inst_prop_sim_new                     false
% 3.54/0.98  --inst_subs_new                         false
% 3.54/0.98  --inst_eq_res_simp                      false
% 3.54/0.98  --inst_subs_given                       false
% 3.54/0.98  --inst_orphan_elimination               true
% 3.54/0.98  --inst_learning_loop_flag               true
% 3.54/0.98  --inst_learning_start                   3000
% 3.54/0.98  --inst_learning_factor                  2
% 3.54/0.98  --inst_start_prop_sim_after_learn       3
% 3.54/0.98  --inst_sel_renew                        solver
% 3.54/0.98  --inst_lit_activity_flag                true
% 3.54/0.98  --inst_restr_to_given                   false
% 3.54/0.98  --inst_activity_threshold               500
% 3.54/0.98  --inst_out_proof                        true
% 3.54/0.98  
% 3.54/0.98  ------ Resolution Options
% 3.54/0.98  
% 3.54/0.98  --resolution_flag                       true
% 3.54/0.98  --res_lit_sel                           adaptive
% 3.54/0.98  --res_lit_sel_side                      none
% 3.54/0.98  --res_ordering                          kbo
% 3.54/0.98  --res_to_prop_solver                    active
% 3.54/0.98  --res_prop_simpl_new                    false
% 3.54/0.98  --res_prop_simpl_given                  true
% 3.54/0.98  --res_passive_queue_type                priority_queues
% 3.54/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/0.98  --res_passive_queues_freq               [15;5]
% 3.54/0.98  --res_forward_subs                      full
% 3.54/0.98  --res_backward_subs                     full
% 3.54/0.98  --res_forward_subs_resolution           true
% 3.54/0.98  --res_backward_subs_resolution          true
% 3.54/0.98  --res_orphan_elimination                true
% 3.54/0.98  --res_time_limit                        2.
% 3.54/0.98  --res_out_proof                         true
% 3.54/0.98  
% 3.54/0.98  ------ Superposition Options
% 3.54/0.98  
% 3.54/0.98  --superposition_flag                    true
% 3.54/0.98  --sup_passive_queue_type                priority_queues
% 3.54/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.54/0.98  --demod_completeness_check              fast
% 3.54/0.98  --demod_use_ground                      true
% 3.54/0.98  --sup_to_prop_solver                    passive
% 3.54/0.98  --sup_prop_simpl_new                    true
% 3.54/0.98  --sup_prop_simpl_given                  true
% 3.54/0.98  --sup_fun_splitting                     false
% 3.54/0.98  --sup_smt_interval                      50000
% 3.54/0.98  
% 3.54/0.98  ------ Superposition Simplification Setup
% 3.54/0.98  
% 3.54/0.98  --sup_indices_passive                   []
% 3.54/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_full_bw                           [BwDemod]
% 3.54/0.98  --sup_immed_triv                        [TrivRules]
% 3.54/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_immed_bw_main                     []
% 3.54/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.98  
% 3.54/0.98  ------ Combination Options
% 3.54/0.98  
% 3.54/0.98  --comb_res_mult                         3
% 3.54/0.98  --comb_sup_mult                         2
% 3.54/0.98  --comb_inst_mult                        10
% 3.54/0.98  
% 3.54/0.98  ------ Debug Options
% 3.54/0.98  
% 3.54/0.98  --dbg_backtrace                         false
% 3.54/0.98  --dbg_dump_prop_clauses                 false
% 3.54/0.98  --dbg_dump_prop_clauses_file            -
% 3.54/0.98  --dbg_out_stat                          false
% 3.54/0.98  ------ Parsing...
% 3.54/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  ------ Proving...
% 3.54/0.98  ------ Problem Properties 
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  clauses                                 49
% 3.54/0.98  conjectures                             4
% 3.54/0.98  EPR                                     12
% 3.54/0.98  Horn                                    45
% 3.54/0.98  unary                                   16
% 3.54/0.98  binary                                  12
% 3.54/0.98  lits                                    124
% 3.54/0.98  lits eq                                 39
% 3.54/0.98  fd_pure                                 0
% 3.54/0.98  fd_pseudo                               0
% 3.54/0.98  fd_cond                                 3
% 3.54/0.98  fd_pseudo_cond                          1
% 3.54/0.98  AC symbols                              0
% 3.54/0.98  
% 3.54/0.98  ------ Schedule dynamic 5 is on 
% 3.54/0.98  
% 3.54/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ 
% 3.54/0.98  Current options:
% 3.54/0.98  ------ 
% 3.54/0.98  
% 3.54/0.98  ------ Input Options
% 3.54/0.98  
% 3.54/0.98  --out_options                           all
% 3.54/0.98  --tptp_safe_out                         true
% 3.54/0.98  --problem_path                          ""
% 3.54/0.98  --include_path                          ""
% 3.54/0.98  --clausifier                            res/vclausify_rel
% 3.54/0.98  --clausifier_options                    --mode clausify
% 3.54/0.98  --stdin                                 false
% 3.54/0.98  --stats_out                             all
% 3.54/0.98  
% 3.54/0.98  ------ General Options
% 3.54/0.98  
% 3.54/0.98  --fof                                   false
% 3.54/0.98  --time_out_real                         305.
% 3.54/0.98  --time_out_virtual                      -1.
% 3.54/0.98  --symbol_type_check                     false
% 3.54/0.98  --clausify_out                          false
% 3.54/0.98  --sig_cnt_out                           false
% 3.54/0.98  --trig_cnt_out                          false
% 3.54/0.98  --trig_cnt_out_tolerance                1.
% 3.54/0.98  --trig_cnt_out_sk_spl                   false
% 3.54/0.98  --abstr_cl_out                          false
% 3.54/0.98  
% 3.54/0.98  ------ Global Options
% 3.54/0.98  
% 3.54/0.98  --schedule                              default
% 3.54/0.98  --add_important_lit                     false
% 3.54/0.98  --prop_solver_per_cl                    1000
% 3.54/0.98  --min_unsat_core                        false
% 3.54/0.98  --soft_assumptions                      false
% 3.54/0.98  --soft_lemma_size                       3
% 3.54/0.98  --prop_impl_unit_size                   0
% 3.54/0.98  --prop_impl_unit                        []
% 3.54/0.98  --share_sel_clauses                     true
% 3.54/0.98  --reset_solvers                         false
% 3.54/0.98  --bc_imp_inh                            [conj_cone]
% 3.54/0.98  --conj_cone_tolerance                   3.
% 3.54/0.98  --extra_neg_conj                        none
% 3.54/0.98  --large_theory_mode                     true
% 3.54/0.98  --prolific_symb_bound                   200
% 3.54/0.98  --lt_threshold                          2000
% 3.54/0.98  --clause_weak_htbl                      true
% 3.54/0.98  --gc_record_bc_elim                     false
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing Options
% 3.54/0.98  
% 3.54/0.98  --preprocessing_flag                    true
% 3.54/0.98  --time_out_prep_mult                    0.1
% 3.54/0.98  --splitting_mode                        input
% 3.54/0.98  --splitting_grd                         true
% 3.54/0.98  --splitting_cvd                         false
% 3.54/0.98  --splitting_cvd_svl                     false
% 3.54/0.98  --splitting_nvd                         32
% 3.54/0.98  --sub_typing                            true
% 3.54/0.98  --prep_gs_sim                           true
% 3.54/0.98  --prep_unflatten                        true
% 3.54/0.98  --prep_res_sim                          true
% 3.54/0.98  --prep_upred                            true
% 3.54/0.98  --prep_sem_filter                       exhaustive
% 3.54/0.98  --prep_sem_filter_out                   false
% 3.54/0.98  --pred_elim                             true
% 3.54/0.98  --res_sim_input                         true
% 3.54/0.98  --eq_ax_congr_red                       true
% 3.54/0.98  --pure_diseq_elim                       true
% 3.54/0.98  --brand_transform                       false
% 3.54/0.98  --non_eq_to_eq                          false
% 3.54/0.98  --prep_def_merge                        true
% 3.54/0.98  --prep_def_merge_prop_impl              false
% 3.54/0.98  --prep_def_merge_mbd                    true
% 3.54/0.98  --prep_def_merge_tr_red                 false
% 3.54/0.98  --prep_def_merge_tr_cl                  false
% 3.54/0.98  --smt_preprocessing                     true
% 3.54/0.98  --smt_ac_axioms                         fast
% 3.54/0.98  --preprocessed_out                      false
% 3.54/0.98  --preprocessed_stats                    false
% 3.54/0.98  
% 3.54/0.98  ------ Abstraction refinement Options
% 3.54/0.98  
% 3.54/0.98  --abstr_ref                             []
% 3.54/0.98  --abstr_ref_prep                        false
% 3.54/0.98  --abstr_ref_until_sat                   false
% 3.54/0.98  --abstr_ref_sig_restrict                funpre
% 3.54/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/0.98  --abstr_ref_under                       []
% 3.54/0.98  
% 3.54/0.98  ------ SAT Options
% 3.54/0.98  
% 3.54/0.98  --sat_mode                              false
% 3.54/0.98  --sat_fm_restart_options                ""
% 3.54/0.98  --sat_gr_def                            false
% 3.54/0.98  --sat_epr_types                         true
% 3.54/0.98  --sat_non_cyclic_types                  false
% 3.54/0.98  --sat_finite_models                     false
% 3.54/0.98  --sat_fm_lemmas                         false
% 3.54/0.98  --sat_fm_prep                           false
% 3.54/0.98  --sat_fm_uc_incr                        true
% 3.54/0.98  --sat_out_model                         small
% 3.54/0.98  --sat_out_clauses                       false
% 3.54/0.98  
% 3.54/0.98  ------ QBF Options
% 3.54/0.98  
% 3.54/0.98  --qbf_mode                              false
% 3.54/0.98  --qbf_elim_univ                         false
% 3.54/0.98  --qbf_dom_inst                          none
% 3.54/0.98  --qbf_dom_pre_inst                      false
% 3.54/0.98  --qbf_sk_in                             false
% 3.54/0.98  --qbf_pred_elim                         true
% 3.54/0.98  --qbf_split                             512
% 3.54/0.98  
% 3.54/0.98  ------ BMC1 Options
% 3.54/0.98  
% 3.54/0.98  --bmc1_incremental                      false
% 3.54/0.98  --bmc1_axioms                           reachable_all
% 3.54/0.98  --bmc1_min_bound                        0
% 3.54/0.98  --bmc1_max_bound                        -1
% 3.54/0.98  --bmc1_max_bound_default                -1
% 3.54/0.98  --bmc1_symbol_reachability              true
% 3.54/0.98  --bmc1_property_lemmas                  false
% 3.54/0.98  --bmc1_k_induction                      false
% 3.54/0.98  --bmc1_non_equiv_states                 false
% 3.54/0.98  --bmc1_deadlock                         false
% 3.54/0.98  --bmc1_ucm                              false
% 3.54/0.98  --bmc1_add_unsat_core                   none
% 3.54/0.98  --bmc1_unsat_core_children              false
% 3.54/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/0.98  --bmc1_out_stat                         full
% 3.54/0.98  --bmc1_ground_init                      false
% 3.54/0.98  --bmc1_pre_inst_next_state              false
% 3.54/0.98  --bmc1_pre_inst_state                   false
% 3.54/0.98  --bmc1_pre_inst_reach_state             false
% 3.54/0.98  --bmc1_out_unsat_core                   false
% 3.54/0.98  --bmc1_aig_witness_out                  false
% 3.54/0.98  --bmc1_verbose                          false
% 3.54/0.98  --bmc1_dump_clauses_tptp                false
% 3.54/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.54/0.98  --bmc1_dump_file                        -
% 3.54/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.54/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.54/0.98  --bmc1_ucm_extend_mode                  1
% 3.54/0.98  --bmc1_ucm_init_mode                    2
% 3.54/0.98  --bmc1_ucm_cone_mode                    none
% 3.54/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.54/0.98  --bmc1_ucm_relax_model                  4
% 3.54/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.54/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/0.98  --bmc1_ucm_layered_model                none
% 3.54/0.98  --bmc1_ucm_max_lemma_size               10
% 3.54/0.98  
% 3.54/0.98  ------ AIG Options
% 3.54/0.98  
% 3.54/0.98  --aig_mode                              false
% 3.54/0.98  
% 3.54/0.98  ------ Instantiation Options
% 3.54/0.98  
% 3.54/0.98  --instantiation_flag                    true
% 3.54/0.98  --inst_sos_flag                         false
% 3.54/0.98  --inst_sos_phase                        true
% 3.54/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/0.98  --inst_lit_sel_side                     none
% 3.54/0.98  --inst_solver_per_active                1400
% 3.54/0.98  --inst_solver_calls_frac                1.
% 3.54/0.98  --inst_passive_queue_type               priority_queues
% 3.54/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/0.98  --inst_passive_queues_freq              [25;2]
% 3.54/0.98  --inst_dismatching                      true
% 3.54/0.98  --inst_eager_unprocessed_to_passive     true
% 3.54/0.98  --inst_prop_sim_given                   true
% 3.54/0.98  --inst_prop_sim_new                     false
% 3.54/0.98  --inst_subs_new                         false
% 3.54/0.98  --inst_eq_res_simp                      false
% 3.54/0.98  --inst_subs_given                       false
% 3.54/0.98  --inst_orphan_elimination               true
% 3.54/0.98  --inst_learning_loop_flag               true
% 3.54/0.98  --inst_learning_start                   3000
% 3.54/0.98  --inst_learning_factor                  2
% 3.54/0.98  --inst_start_prop_sim_after_learn       3
% 3.54/0.98  --inst_sel_renew                        solver
% 3.54/0.98  --inst_lit_activity_flag                true
% 3.54/0.98  --inst_restr_to_given                   false
% 3.54/0.98  --inst_activity_threshold               500
% 3.54/0.98  --inst_out_proof                        true
% 3.54/0.98  
% 3.54/0.98  ------ Resolution Options
% 3.54/0.98  
% 3.54/0.98  --resolution_flag                       false
% 3.54/0.98  --res_lit_sel                           adaptive
% 3.54/0.98  --res_lit_sel_side                      none
% 3.54/0.98  --res_ordering                          kbo
% 3.54/0.98  --res_to_prop_solver                    active
% 3.54/0.98  --res_prop_simpl_new                    false
% 3.54/0.98  --res_prop_simpl_given                  true
% 3.54/0.98  --res_passive_queue_type                priority_queues
% 3.54/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/0.98  --res_passive_queues_freq               [15;5]
% 3.54/0.98  --res_forward_subs                      full
% 3.54/0.98  --res_backward_subs                     full
% 3.54/0.98  --res_forward_subs_resolution           true
% 3.54/0.98  --res_backward_subs_resolution          true
% 3.54/0.98  --res_orphan_elimination                true
% 3.54/0.98  --res_time_limit                        2.
% 3.54/0.98  --res_out_proof                         true
% 3.54/0.98  
% 3.54/0.98  ------ Superposition Options
% 3.54/0.98  
% 3.54/0.98  --superposition_flag                    true
% 3.54/0.98  --sup_passive_queue_type                priority_queues
% 3.54/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.54/0.98  --demod_completeness_check              fast
% 3.54/0.98  --demod_use_ground                      true
% 3.54/0.98  --sup_to_prop_solver                    passive
% 3.54/0.98  --sup_prop_simpl_new                    true
% 3.54/0.98  --sup_prop_simpl_given                  true
% 3.54/0.98  --sup_fun_splitting                     false
% 3.54/0.98  --sup_smt_interval                      50000
% 3.54/0.98  
% 3.54/0.98  ------ Superposition Simplification Setup
% 3.54/0.98  
% 3.54/0.98  --sup_indices_passive                   []
% 3.54/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_full_bw                           [BwDemod]
% 3.54/0.98  --sup_immed_triv                        [TrivRules]
% 3.54/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_immed_bw_main                     []
% 3.54/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.98  
% 3.54/0.98  ------ Combination Options
% 3.54/0.98  
% 3.54/0.98  --comb_res_mult                         3
% 3.54/0.98  --comb_sup_mult                         2
% 3.54/0.98  --comb_inst_mult                        10
% 3.54/0.98  
% 3.54/0.98  ------ Debug Options
% 3.54/0.98  
% 3.54/0.98  --dbg_backtrace                         false
% 3.54/0.98  --dbg_dump_prop_clauses                 false
% 3.54/0.98  --dbg_dump_prop_clauses_file            -
% 3.54/0.98  --dbg_out_stat                          false
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  % SZS status Theorem for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  fof(f27,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f58,plain,(
% 3.54/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/0.98    inference(ennf_transformation,[],[f27])).
% 3.54/0.98  
% 3.54/0.98  fof(f59,plain,(
% 3.54/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/0.98    inference(flattening,[],[f58])).
% 3.54/0.98  
% 3.54/0.98  fof(f67,plain,(
% 3.54/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/0.98    inference(nnf_transformation,[],[f59])).
% 3.54/0.98  
% 3.54/0.98  fof(f106,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f67])).
% 3.54/0.98  
% 3.54/0.98  fof(f29,conjecture,(
% 3.54/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f30,negated_conjecture,(
% 3.54/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.54/0.98    inference(negated_conjecture,[],[f29])).
% 3.54/0.98  
% 3.54/0.98  fof(f62,plain,(
% 3.54/0.98    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.54/0.98    inference(ennf_transformation,[],[f30])).
% 3.54/0.98  
% 3.54/0.98  fof(f63,plain,(
% 3.54/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.54/0.98    inference(flattening,[],[f62])).
% 3.54/0.98  
% 3.54/0.98  fof(f68,plain,(
% 3.54/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f69,plain,(
% 3.54/0.98    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.54/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f63,f68])).
% 3.54/0.98  
% 3.54/0.98  fof(f116,plain,(
% 3.54/0.98    v1_funct_2(sK2,sK0,sK1)),
% 3.54/0.98    inference(cnf_transformation,[],[f69])).
% 3.54/0.98  
% 3.54/0.98  fof(f117,plain,(
% 3.54/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.54/0.98    inference(cnf_transformation,[],[f69])).
% 3.54/0.98  
% 3.54/0.98  fof(f25,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f56,plain,(
% 3.54/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/0.98    inference(ennf_transformation,[],[f25])).
% 3.54/0.98  
% 3.54/0.98  fof(f104,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f56])).
% 3.54/0.98  
% 3.54/0.98  fof(f118,plain,(
% 3.54/0.98    v2_funct_1(sK2)),
% 3.54/0.98    inference(cnf_transformation,[],[f69])).
% 3.54/0.98  
% 3.54/0.98  fof(f21,axiom,(
% 3.54/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f52,plain,(
% 3.54/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f21])).
% 3.54/0.98  
% 3.54/0.98  fof(f53,plain,(
% 3.54/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.54/0.98    inference(flattening,[],[f52])).
% 3.54/0.98  
% 3.54/0.98  fof(f98,plain,(
% 3.54/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f53])).
% 3.54/0.98  
% 3.54/0.98  fof(f26,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f57,plain,(
% 3.54/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/0.98    inference(ennf_transformation,[],[f26])).
% 3.54/0.98  
% 3.54/0.98  fof(f105,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f57])).
% 3.54/0.98  
% 3.54/0.98  fof(f119,plain,(
% 3.54/0.98    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.54/0.98    inference(cnf_transformation,[],[f69])).
% 3.54/0.98  
% 3.54/0.98  fof(f16,axiom,(
% 3.54/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f44,plain,(
% 3.54/0.98    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f16])).
% 3.54/0.98  
% 3.54/0.98  fof(f45,plain,(
% 3.54/0.98    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.54/0.98    inference(flattening,[],[f44])).
% 3.54/0.98  
% 3.54/0.98  fof(f91,plain,(
% 3.54/0.98    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f45])).
% 3.54/0.98  
% 3.54/0.98  fof(f115,plain,(
% 3.54/0.98    v1_funct_1(sK2)),
% 3.54/0.98    inference(cnf_transformation,[],[f69])).
% 3.54/0.98  
% 3.54/0.98  fof(f23,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f54,plain,(
% 3.54/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.54/0.98    inference(ennf_transformation,[],[f23])).
% 3.54/0.98  
% 3.54/0.98  fof(f102,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f54])).
% 3.54/0.98  
% 3.54/0.98  fof(f28,axiom,(
% 3.54/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f60,plain,(
% 3.54/0.98    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.54/0.98    inference(ennf_transformation,[],[f28])).
% 3.54/0.98  
% 3.54/0.98  fof(f61,plain,(
% 3.54/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.54/0.98    inference(flattening,[],[f60])).
% 3.54/0.98  
% 3.54/0.98  fof(f114,plain,(
% 3.54/0.98    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f61])).
% 3.54/0.98  
% 3.54/0.98  fof(f17,axiom,(
% 3.54/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f46,plain,(
% 3.54/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f17])).
% 3.54/0.98  
% 3.54/0.98  fof(f47,plain,(
% 3.54/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.54/0.98    inference(flattening,[],[f46])).
% 3.54/0.98  
% 3.54/0.98  fof(f93,plain,(
% 3.54/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f47])).
% 3.54/0.98  
% 3.54/0.98  fof(f92,plain,(
% 3.54/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f47])).
% 3.54/0.98  
% 3.54/0.98  fof(f99,plain,(
% 3.54/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f53])).
% 3.54/0.98  
% 3.54/0.98  fof(f113,plain,(
% 3.54/0.98    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f61])).
% 3.54/0.98  
% 3.54/0.98  fof(f120,plain,(
% 3.54/0.98    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.54/0.98    inference(cnf_transformation,[],[f69])).
% 3.54/0.98  
% 3.54/0.98  fof(f3,axiom,(
% 3.54/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f64,plain,(
% 3.54/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.54/0.98    inference(nnf_transformation,[],[f3])).
% 3.54/0.98  
% 3.54/0.98  fof(f65,plain,(
% 3.54/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.54/0.98    inference(flattening,[],[f64])).
% 3.54/0.98  
% 3.54/0.98  fof(f72,plain,(
% 3.54/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.54/0.98    inference(cnf_transformation,[],[f65])).
% 3.54/0.98  
% 3.54/0.98  fof(f122,plain,(
% 3.54/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.54/0.98    inference(equality_resolution,[],[f72])).
% 3.54/0.98  
% 3.54/0.98  fof(f24,axiom,(
% 3.54/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f55,plain,(
% 3.54/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f24])).
% 3.54/0.98  
% 3.54/0.98  fof(f103,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f55])).
% 3.54/0.98  
% 3.54/0.98  fof(f1,axiom,(
% 3.54/0.98    v1_xboole_0(k1_xboole_0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f70,plain,(
% 3.54/0.98    v1_xboole_0(k1_xboole_0)),
% 3.54/0.98    inference(cnf_transformation,[],[f1])).
% 3.54/0.98  
% 3.54/0.98  fof(f2,axiom,(
% 3.54/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f34,plain,(
% 3.54/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f2])).
% 3.54/0.98  
% 3.54/0.98  fof(f71,plain,(
% 3.54/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f34])).
% 3.54/0.98  
% 3.54/0.98  fof(f12,axiom,(
% 3.54/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f83,plain,(
% 3.54/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.54/0.98    inference(cnf_transformation,[],[f12])).
% 3.54/0.98  
% 3.54/0.98  fof(f4,axiom,(
% 3.54/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f75,plain,(
% 3.54/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f4])).
% 3.54/0.98  
% 3.54/0.98  cnf(c_41,plain,
% 3.54/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.54/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.54/0.98      | k1_xboole_0 = X2 ),
% 3.54/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_49,negated_conjecture,
% 3.54/0.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.54/0.98      inference(cnf_transformation,[],[f116]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_916,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.54/0.98      | sK0 != X1
% 3.54/0.98      | sK1 != X2
% 3.54/0.98      | sK2 != X0
% 3.54/0.98      | k1_xboole_0 = X2 ),
% 3.54/0.98      inference(resolution_lifted,[status(thm)],[c_41,c_49]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_917,plain,
% 3.54/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.54/0.98      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.54/0.98      | k1_xboole_0 = sK1 ),
% 3.54/0.98      inference(unflattening,[status(thm)],[c_916]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_48,negated_conjecture,
% 3.54/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.54/0.98      inference(cnf_transformation,[],[f117]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_919,plain,
% 3.54/0.98      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_917,c_48]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2254,plain,
% 3.54/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_34,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2258,plain,
% 3.54/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.54/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5645,plain,
% 3.54/0.98      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2254,c_2258]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5835,plain,
% 3.54/0.98      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_919,c_5645]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_47,negated_conjecture,
% 3.54/0.98      ( v2_funct_1(sK2) ),
% 3.54/0.98      inference(cnf_transformation,[],[f118]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2255,plain,
% 3.54/0.98      ( v2_funct_1(sK2) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_29,plain,
% 3.54/0.98      ( ~ v2_funct_1(X0)
% 3.54/0.98      | ~ v1_funct_1(X0)
% 3.54/0.98      | ~ v1_relat_1(X0)
% 3.54/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2263,plain,
% 3.54/0.98      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.54/0.98      | v2_funct_1(X0) != iProver_top
% 3.54/0.98      | v1_funct_1(X0) != iProver_top
% 3.54/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6866,plain,
% 3.54/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.54/0.98      | v1_funct_1(sK2) != iProver_top
% 3.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2255,c_2263]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_35,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2257,plain,
% 3.54/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.54/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4656,plain,
% 3.54/0.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2254,c_2257]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_46,negated_conjecture,
% 3.54/0.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.54/0.98      inference(cnf_transformation,[],[f119]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4658,plain,
% 3.54/0.98      ( k2_relat_1(sK2) = sK1 ),
% 3.54/0.98      inference(light_normalisation,[status(thm)],[c_4656,c_46]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_21,plain,
% 3.54/0.98      ( ~ v2_funct_1(X0)
% 3.54/0.98      | ~ v1_funct_1(X0)
% 3.54/0.98      | ~ v1_relat_1(X0)
% 3.54/0.98      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2271,plain,
% 3.54/0.98      ( k2_funct_1(X0) = k4_relat_1(X0)
% 3.54/0.98      | v2_funct_1(X0) != iProver_top
% 3.54/0.98      | v1_funct_1(X0) != iProver_top
% 3.54/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6324,plain,
% 3.54/0.98      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 3.54/0.98      | v1_funct_1(sK2) != iProver_top
% 3.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2255,c_2271]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_50,negated_conjecture,
% 3.54/0.98      ( v1_funct_1(sK2) ),
% 3.54/0.98      inference(cnf_transformation,[],[f115]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_653,plain,
% 3.54/0.98      ( ~ v1_funct_1(X0)
% 3.54/0.98      | ~ v1_relat_1(X0)
% 3.54/0.98      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.54/0.98      | sK2 != X0 ),
% 3.54/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_47]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_654,plain,
% 3.54/0.98      ( ~ v1_funct_1(sK2)
% 3.54/0.98      | ~ v1_relat_1(sK2)
% 3.54/0.98      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.54/0.98      inference(unflattening,[status(thm)],[c_653]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_32,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | v1_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2807,plain,
% 3.54/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.54/0.98      | v1_relat_1(sK2) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_32]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3131,plain,
% 3.54/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.54/0.98      | v1_relat_1(sK2) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_2807]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6492,plain,
% 3.54/0.98      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_6324,c_50,c_48,c_654,c_3131]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6887,plain,
% 3.54/0.98      ( k1_relat_1(k4_relat_1(sK2)) = sK1
% 3.54/0.98      | v1_funct_1(sK2) != iProver_top
% 3.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.54/0.98      inference(light_normalisation,[status(thm)],[c_6866,c_4658,c_6492]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_51,plain,
% 3.54/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_53,plain,
% 3.54/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3132,plain,
% 3.54/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.54/0.98      | v1_relat_1(sK2) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_3131]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7138,plain,
% 3.54/0.98      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_6887,c_51,c_53,c_3132]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_42,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.54/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.54/0.98      | ~ v1_funct_1(X0)
% 3.54/0.98      | ~ v1_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f114]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2256,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.54/0.98      | v1_funct_1(X0) != iProver_top
% 3.54/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7143,plain,
% 3.54/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) != iProver_top
% 3.54/0.98      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.54/0.98      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_7138,c_2256]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_22,plain,
% 3.54/0.98      ( ~ v1_funct_1(X0)
% 3.54/0.98      | v1_funct_1(k2_funct_1(X0))
% 3.54/0.98      | ~ v1_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2270,plain,
% 3.54/0.98      ( v1_funct_1(X0) != iProver_top
% 3.54/0.98      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.54/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6547,plain,
% 3.54/0.98      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 3.54/0.98      | v1_funct_1(sK2) != iProver_top
% 3.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_6492,c_2270]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_23,plain,
% 3.54/0.98      ( ~ v1_funct_1(X0)
% 3.54/0.98      | ~ v1_relat_1(X0)
% 3.54/0.98      | v1_relat_1(k2_funct_1(X0)) ),
% 3.54/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2269,plain,
% 3.54/0.98      ( v1_funct_1(X0) != iProver_top
% 3.54/0.98      | v1_relat_1(X0) != iProver_top
% 3.54/0.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6548,plain,
% 3.54/0.98      ( v1_funct_1(sK2) != iProver_top
% 3.54/0.98      | v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 3.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_6492,c_2269]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7215,plain,
% 3.54/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) != iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_7143,c_51,c_53,c_3132,c_6547,c_6548]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_28,plain,
% 3.54/0.98      ( ~ v2_funct_1(X0)
% 3.54/0.98      | ~ v1_funct_1(X0)
% 3.54/0.98      | ~ v1_relat_1(X0)
% 3.54/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2264,plain,
% 3.54/0.98      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.54/0.98      | v2_funct_1(X0) != iProver_top
% 3.54/0.98      | v1_funct_1(X0) != iProver_top
% 3.54/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7008,plain,
% 3.54/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.54/0.98      | v1_funct_1(sK2) != iProver_top
% 3.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2255,c_2264]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7029,plain,
% 3.54/0.98      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2)
% 3.54/0.98      | v1_funct_1(sK2) != iProver_top
% 3.54/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.54/0.98      inference(light_normalisation,[status(thm)],[c_7008,c_6492]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7170,plain,
% 3.54/0.98      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_7029,c_51,c_53,c_3132]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7221,plain,
% 3.54/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.54/0.98      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.54/0.98      inference(light_normalisation,[status(thm)],[c_7215,c_7170]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_43,plain,
% 3.54/0.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.54/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.54/0.98      | ~ v1_funct_1(X0)
% 3.54/0.98      | ~ v1_relat_1(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_45,negated_conjecture,
% 3.54/0.98      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.54/0.98      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.54/0.98      inference(cnf_transformation,[],[f120]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_927,plain,
% 3.54/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.54/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.54/0.98      | ~ v1_funct_1(X0)
% 3.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.54/0.98      | ~ v1_relat_1(X0)
% 3.54/0.98      | k2_funct_1(sK2) != X0
% 3.54/0.98      | k1_relat_1(X0) != sK1
% 3.54/0.98      | sK0 != X1 ),
% 3.54/0.98      inference(resolution_lifted,[status(thm)],[c_43,c_45]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_928,plain,
% 3.54/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.54/0.98      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.54/0.98      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.54/0.98      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.54/0.98      inference(unflattening,[status(thm)],[c_927]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_940,plain,
% 3.54/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.54/0.98      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.54/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.54/0.98      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.54/0.98      inference(forward_subsumption_resolution,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_928,c_32]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2243,plain,
% 3.54/0.98      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.54/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.54/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6497,plain,
% 3.54/0.98      ( k1_relat_1(k4_relat_1(sK2)) != sK1
% 3.54/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) != iProver_top
% 3.54/0.98      | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_6492,c_2243]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6853,plain,
% 3.54/0.98      ( r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) != iProver_top
% 3.54/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.54/0.98      | k1_relat_1(k4_relat_1(sK2)) != sK1 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_6497,c_51,c_53,c_3132,c_6547]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6854,plain,
% 3.54/0.98      ( k1_relat_1(k4_relat_1(sK2)) != sK1
% 3.54/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) != iProver_top ),
% 3.54/0.98      inference(renaming,[status(thm)],[c_6853]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7141,plain,
% 3.54/0.98      ( sK1 != sK1
% 3.54/0.98      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) != iProver_top ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_7138,c_6854]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7208,plain,
% 3.54/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.54/0.98      | r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) != iProver_top ),
% 3.54/0.98      inference(equality_resolution_simp,[status(thm)],[c_7141]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7210,plain,
% 3.54/0.98      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.54/0.98      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.54/0.98      inference(light_normalisation,[status(thm)],[c_7208,c_7170]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7231,plain,
% 3.54/0.98      ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_7221,c_7210]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_14153,plain,
% 3.54/0.98      ( sK1 = k1_xboole_0 | r1_tarski(sK0,sK0) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_5835,c_7231]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4,plain,
% 3.54/0.98      ( r1_tarski(X0,X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f122]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4296,plain,
% 3.54/0.98      ( r1_tarski(sK0,sK0) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4299,plain,
% 3.54/0.98      ( r1_tarski(sK0,sK0) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_4296]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_14377,plain,
% 3.54/0.98      ( sK1 = k1_xboole_0 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_14153,c_4299]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_33,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.54/0.98      | ~ v1_xboole_0(X2)
% 3.54/0.98      | v1_xboole_0(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2259,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.54/0.98      | v1_xboole_0(X2) != iProver_top
% 3.54/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6116,plain,
% 3.54/0.98      ( v1_xboole_0(sK1) != iProver_top
% 3.54/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2254,c_2259]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_14410,plain,
% 3.54/0.98      ( v1_xboole_0(sK2) = iProver_top
% 3.54/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_14377,c_6116]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_0,plain,
% 3.54/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_158,plain,
% 3.54/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1508,plain,
% 3.54/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.54/0.98      theory(equality) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3943,plain,
% 3.54/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_1508]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3944,plain,
% 3.54/0.98      ( sK1 != X0
% 3.54/0.98      | v1_xboole_0(X0) != iProver_top
% 3.54/0.98      | v1_xboole_0(sK1) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_3943]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3946,plain,
% 3.54/0.98      ( sK1 != k1_xboole_0
% 3.54/0.98      | v1_xboole_0(sK1) = iProver_top
% 3.54/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_3944]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_15075,plain,
% 3.54/0.98      ( v1_xboole_0(sK2) = iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_14410,c_158,c_3946,c_4299,c_6116,c_14153]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1,plain,
% 3.54/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2283,plain,
% 3.54/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_15094,plain,
% 3.54/0.98      ( sK2 = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_15075,c_2283]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_15459,plain,
% 3.54/0.98      ( r1_tarski(k1_relat_1(k1_xboole_0),sK0) != iProver_top ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_15094,c_7231]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_14,plain,
% 3.54/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_15555,plain,
% 3.54/0.98      ( r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 3.54/0.98      inference(light_normalisation,[status(thm)],[c_15459,c_14]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5,plain,
% 3.54/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6695,plain,
% 3.54/0.98      ( r1_tarski(k1_xboole_0,sK0) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6698,plain,
% 3.54/0.98      ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_6695]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(contradiction,plain,
% 3.54/0.98      ( $false ),
% 3.54/0.98      inference(minisat,[status(thm)],[c_15555,c_6698]) ).
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  ------                               Statistics
% 3.54/0.98  
% 3.54/0.98  ------ General
% 3.54/0.98  
% 3.54/0.98  abstr_ref_over_cycles:                  0
% 3.54/0.98  abstr_ref_under_cycles:                 0
% 3.54/0.98  gc_basic_clause_elim:                   0
% 3.54/0.98  forced_gc_time:                         0
% 3.54/0.98  parsing_time:                           0.009
% 3.54/0.98  unif_index_cands_time:                  0.
% 3.54/0.98  unif_index_add_time:                    0.
% 3.54/0.98  orderings_time:                         0.
% 3.54/0.98  out_proof_time:                         0.013
% 3.54/0.98  total_time:                             0.445
% 3.54/0.98  num_of_symbols:                         53
% 3.54/0.98  num_of_terms:                           9525
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing
% 3.54/0.98  
% 3.54/0.98  num_of_splits:                          0
% 3.54/0.98  num_of_split_atoms:                     0
% 3.54/0.98  num_of_reused_defs:                     0
% 3.54/0.98  num_eq_ax_congr_red:                    11
% 3.54/0.98  num_of_sem_filtered_clauses:            1
% 3.54/0.98  num_of_subtypes:                        0
% 3.54/0.98  monotx_restored_types:                  0
% 3.54/0.98  sat_num_of_epr_types:                   0
% 3.54/0.98  sat_num_of_non_cyclic_types:            0
% 3.54/0.98  sat_guarded_non_collapsed_types:        0
% 3.54/0.98  num_pure_diseq_elim:                    0
% 3.54/0.98  simp_replaced_by:                       0
% 3.54/0.98  res_preprocessed:                       229
% 3.54/0.98  prep_upred:                             0
% 3.54/0.98  prep_unflattend:                        61
% 3.54/0.98  smt_new_axioms:                         0
% 3.54/0.98  pred_elim_cands:                        6
% 3.54/0.98  pred_elim:                              1
% 3.54/0.98  pred_elim_cl:                           -2
% 3.54/0.98  pred_elim_cycles:                       4
% 3.54/0.98  merged_defs:                            0
% 3.54/0.98  merged_defs_ncl:                        0
% 3.54/0.98  bin_hyper_res:                          0
% 3.54/0.98  prep_cycles:                            4
% 3.54/0.98  pred_elim_time:                         0.017
% 3.54/0.98  splitting_time:                         0.
% 3.54/0.98  sem_filter_time:                        0.
% 3.54/0.98  monotx_time:                            0.
% 3.54/0.98  subtype_inf_time:                       0.
% 3.54/0.98  
% 3.54/0.98  ------ Problem properties
% 3.54/0.98  
% 3.54/0.98  clauses:                                49
% 3.54/0.98  conjectures:                            4
% 3.54/0.98  epr:                                    12
% 3.54/0.98  horn:                                   45
% 3.54/0.98  ground:                                 17
% 3.54/0.98  unary:                                  16
% 3.54/0.98  binary:                                 12
% 3.54/0.98  lits:                                   124
% 3.54/0.98  lits_eq:                                39
% 3.54/0.98  fd_pure:                                0
% 3.54/0.98  fd_pseudo:                              0
% 3.54/0.98  fd_cond:                                3
% 3.54/0.98  fd_pseudo_cond:                         1
% 3.54/0.98  ac_symbols:                             0
% 3.54/0.98  
% 3.54/0.98  ------ Propositional Solver
% 3.54/0.98  
% 3.54/0.98  prop_solver_calls:                      28
% 3.54/0.98  prop_fast_solver_calls:                 1973
% 3.54/0.98  smt_solver_calls:                       0
% 3.54/0.98  smt_fast_solver_calls:                  0
% 3.54/0.98  prop_num_of_clauses:                    5646
% 3.54/0.98  prop_preprocess_simplified:             13561
% 3.54/0.98  prop_fo_subsumed:                       118
% 3.54/0.98  prop_solver_time:                       0.
% 3.54/0.98  smt_solver_time:                        0.
% 3.54/0.98  smt_fast_solver_time:                   0.
% 3.54/0.98  prop_fast_solver_time:                  0.
% 3.54/0.98  prop_unsat_core_time:                   0.
% 3.54/0.98  
% 3.54/0.98  ------ QBF
% 3.54/0.98  
% 3.54/0.98  qbf_q_res:                              0
% 3.54/0.98  qbf_num_tautologies:                    0
% 3.54/0.98  qbf_prep_cycles:                        0
% 3.54/0.98  
% 3.54/0.98  ------ BMC1
% 3.54/0.98  
% 3.54/0.98  bmc1_current_bound:                     -1
% 3.54/0.98  bmc1_last_solved_bound:                 -1
% 3.54/0.98  bmc1_unsat_core_size:                   -1
% 3.54/0.98  bmc1_unsat_core_parents_size:           -1
% 3.54/0.98  bmc1_merge_next_fun:                    0
% 3.54/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.54/0.98  
% 3.54/0.98  ------ Instantiation
% 3.54/0.98  
% 3.54/0.98  inst_num_of_clauses:                    1705
% 3.54/0.98  inst_num_in_passive:                    354
% 3.54/0.98  inst_num_in_active:                     749
% 3.54/0.98  inst_num_in_unprocessed:                604
% 3.54/0.98  inst_num_of_loops:                      930
% 3.54/0.98  inst_num_of_learning_restarts:          0
% 3.54/0.98  inst_num_moves_active_passive:          178
% 3.54/0.98  inst_lit_activity:                      0
% 3.54/0.98  inst_lit_activity_moves:                0
% 3.54/0.98  inst_num_tautologies:                   0
% 3.54/0.98  inst_num_prop_implied:                  0
% 3.54/0.98  inst_num_existing_simplified:           0
% 3.54/0.98  inst_num_eq_res_simplified:             0
% 3.54/0.98  inst_num_child_elim:                    0
% 3.54/0.98  inst_num_of_dismatching_blockings:      556
% 3.54/0.98  inst_num_of_non_proper_insts:           1889
% 3.54/0.98  inst_num_of_duplicates:                 0
% 3.54/0.98  inst_inst_num_from_inst_to_res:         0
% 3.54/0.98  inst_dismatching_checking_time:         0.
% 3.54/0.98  
% 3.54/0.98  ------ Resolution
% 3.54/0.98  
% 3.54/0.98  res_num_of_clauses:                     0
% 3.54/0.98  res_num_in_passive:                     0
% 3.54/0.98  res_num_in_active:                      0
% 3.54/0.98  res_num_of_loops:                       233
% 3.54/0.98  res_forward_subset_subsumed:            122
% 3.54/0.98  res_backward_subset_subsumed:           6
% 3.54/0.98  res_forward_subsumed:                   0
% 3.54/0.98  res_backward_subsumed:                  0
% 3.54/0.98  res_forward_subsumption_resolution:     7
% 3.54/0.98  res_backward_subsumption_resolution:    0
% 3.54/0.98  res_clause_to_clause_subsumption:       819
% 3.54/0.98  res_orphan_elimination:                 0
% 3.54/0.98  res_tautology_del:                      128
% 3.54/0.98  res_num_eq_res_simplified:              0
% 3.54/0.98  res_num_sel_changes:                    0
% 3.54/0.98  res_moves_from_active_to_pass:          0
% 3.54/0.98  
% 3.54/0.98  ------ Superposition
% 3.54/0.98  
% 3.54/0.98  sup_time_total:                         0.
% 3.54/0.98  sup_time_generating:                    0.
% 3.54/0.98  sup_time_sim_full:                      0.
% 3.54/0.98  sup_time_sim_immed:                     0.
% 3.54/0.98  
% 3.54/0.98  sup_num_of_clauses:                     173
% 3.54/0.98  sup_num_in_active:                      84
% 3.54/0.98  sup_num_in_passive:                     89
% 3.54/0.98  sup_num_of_loops:                       185
% 3.54/0.98  sup_fw_superposition:                   189
% 3.54/0.98  sup_bw_superposition:                   114
% 3.54/0.98  sup_immediate_simplified:               168
% 3.54/0.98  sup_given_eliminated:                   1
% 3.54/0.98  comparisons_done:                       0
% 3.54/0.98  comparisons_avoided:                    35
% 3.54/0.98  
% 3.54/0.98  ------ Simplifications
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  sim_fw_subset_subsumed:                 36
% 3.54/0.98  sim_bw_subset_subsumed:                 8
% 3.54/0.98  sim_fw_subsumed:                        20
% 3.54/0.98  sim_bw_subsumed:                        2
% 3.54/0.98  sim_fw_subsumption_res:                 1
% 3.54/0.98  sim_bw_subsumption_res:                 0
% 3.54/0.98  sim_tautology_del:                      3
% 3.54/0.98  sim_eq_tautology_del:                   65
% 3.54/0.98  sim_eq_res_simp:                        4
% 3.54/0.98  sim_fw_demodulated:                     13
% 3.54/0.98  sim_bw_demodulated:                     95
% 3.54/0.98  sim_light_normalised:                   123
% 3.54/0.98  sim_joinable_taut:                      0
% 3.54/0.98  sim_joinable_simp:                      0
% 3.54/0.98  sim_ac_normalised:                      0
% 3.54/0.98  sim_smt_subsumption:                    0
% 3.54/0.98  
%------------------------------------------------------------------------------

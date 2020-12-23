%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:17 EST 2020

% Result     : Theorem 6.90s
% Output     : CNFRefutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :  235 (1753 expanded)
%              Number of clauses        :  137 ( 539 expanded)
%              Number of leaves         :   26 ( 344 expanded)
%              Depth                    :   24
%              Number of atoms          :  742 (7857 expanded)
%              Number of equality atoms :  310 ( 908 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f45])).

fof(f98,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f99,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f98])).

fof(f116,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3))
        | ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
      & v3_funct_2(sK4,sK3,sK3)
      & v1_funct_2(sK4,sK3,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f117,plain,
    ( ( ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3))
      | ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    & v3_funct_2(sK4,sK3,sK3)
    & v1_funct_2(sK4,sK3,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f99,f116])).

fof(f194,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f117])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f142,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f108,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f108])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f124,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f71])).

fof(f149,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f148,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f84])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f88])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f89])).

fof(f179,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f191,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f117])).

fof(f193,plain,(
    v3_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f117])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f162,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f44,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f96])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f192,plain,(
    v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f117])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f27,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f75])).

fof(f156,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f43,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f188,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f43])).

fof(f201,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f156,f188])).

fof(f25,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f153,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f196,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f153,f188])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f94])).

fof(f187,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f90])).

fof(f184,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f41,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f92])).

fof(f186,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f181,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f157,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f200,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f157,f188])).

fof(f195,plain,
    ( ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3))
    | ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) ),
    inference(cnf_transformation,[],[f117])).

fof(f40,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f40])).

fof(f185,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f32,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f81,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f80])).

fof(f113,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f81])).

fof(f164,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f204,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f164])).

cnf(c_73,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f194])).

cnf(c_4788,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_43,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_25,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_1094,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_43,c_25])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_1098,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1094,c_41])).

cnf(c_1099,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_1098])).

cnf(c_4778,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1099])).

cnf(c_5825,plain,
    ( r1_tarski(k1_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4788,c_4778])).

cnf(c_5,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_4838,plain,
    ( X0 = X1
    | r2_xboole_0(X1,X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11086,plain,
    ( k1_relat_1(sK4) = sK3
    | r2_xboole_0(k1_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5825,c_4838])).

cnf(c_9,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X1) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_4834,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_4842,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8163,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4834,c_4842])).

cnf(c_21836,plain,
    ( k1_relat_1(sK4) = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11086,c_8163])).

cnf(c_6,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_3337,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7788,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_3337])).

cnf(c_7795,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7788])).

cnf(c_49,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_4808,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_12820,plain,
    ( k7_relset_1(sK3,sK3,sK4,sK3) = k2_relset_1(sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_4788,c_4808])).

cnf(c_31,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f149])).

cnf(c_1077,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_43,c_31])).

cnf(c_1081,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1077,c_43,c_41,c_31])).

cnf(c_4779,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1081])).

cnf(c_6760,plain,
    ( k7_relat_1(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_4788,c_4779])).

cnf(c_4814,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_7859,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4788,c_4814])).

cnf(c_30,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_4821,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8169,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_7859,c_4821])).

cnf(c_8439,plain,
    ( k9_relat_1(sK4,sK3) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_6760,c_8169])).

cnf(c_52,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_42,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f161])).

cnf(c_62,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f179])).

cnf(c_1005,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_42,c_62])).

cnf(c_1017,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1005,c_41])).

cnf(c_1048,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_52,c_1017])).

cnf(c_1049,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_1048])).

cnf(c_4780,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1049])).

cnf(c_7564,plain,
    ( k2_relat_1(sK4) = sK3
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4788,c_4780])).

cnf(c_76,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f191])).

cnf(c_74,negated_conjecture,
    ( v3_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f193])).

cnf(c_5519,plain,
    ( ~ v3_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK4)
    | k2_relat_1(sK4) = X1 ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_5838,plain,
    ( ~ v3_funct_2(sK4,sK3,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_relat_1(sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_5519])).

cnf(c_6056,plain,
    ( ~ v3_funct_2(sK4,sK3,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_relat_1(sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_5838])).

cnf(c_8433,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7564,c_76,c_74,c_73,c_6056])).

cnf(c_8446,plain,
    ( k9_relat_1(sK4,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_8439,c_8433])).

cnf(c_44,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f162])).

cnf(c_4813,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_12319,plain,
    ( k7_relset_1(sK3,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_4788,c_4813])).

cnf(c_12832,plain,
    ( k2_relset_1(sK3,sK3,sK4) = sK3 ),
    inference(demodulation,[status(thm)],[c_12820,c_8446,c_12319])).

cnf(c_71,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f189])).

cnf(c_4790,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_12981,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK3)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK3,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12832,c_4790])).

cnf(c_75,negated_conjecture,
    ( v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f192])).

cnf(c_53,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f171])).

cnf(c_5454,plain,
    ( ~ v3_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_5730,plain,
    ( ~ v3_funct_2(sK4,sK3,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | v2_funct_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5454])).

cnf(c_13007,plain,
    ( ~ v1_funct_2(sK4,sK3,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12981])).

cnf(c_20737,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12981,c_76,c_75,c_74,c_73,c_5730,c_13007])).

cnf(c_4805,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_15085,plain,
    ( v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4788,c_4805])).

cnf(c_77,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_79,plain,
    ( v3_funct_2(sK4,sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_80,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_5731,plain,
    ( v3_funct_2(sK4,sK3,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5730])).

cnf(c_15271,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15085,c_77,c_79,c_80,c_5731])).

cnf(c_39,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f201])).

cnf(c_4815,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_15277,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_15271,c_4815])).

cnf(c_5380,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_6005,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_15386,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15277,c_76,c_74,c_73,c_5380,c_5730,c_6005])).

cnf(c_20739,plain,
    ( k6_partfun1(k1_relat_1(sK4)) = k6_partfun1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20737,c_15386])).

cnf(c_34,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f196])).

cnf(c_20760,plain,
    ( k2_relat_1(k6_partfun1(sK3)) = k1_relat_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20739,c_34])).

cnf(c_20768,plain,
    ( k1_relat_1(sK4) = sK3
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20760,c_34])).

cnf(c_21846,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_relat_1(sK4) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_21836])).

cnf(c_21849,plain,
    ( k1_relat_1(sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21836,c_6,c_7795,c_20768,c_21846])).

cnf(c_69,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f187])).

cnf(c_4792,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_12052,plain,
    ( k2_funct_2(sK3,sK4) = k2_funct_1(sK4)
    | v1_funct_2(sK4,sK3,sK3) != iProver_top
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4788,c_4792])).

cnf(c_5566,plain,
    ( ~ v1_funct_2(sK4,X0,X0)
    | ~ v3_funct_2(sK4,X0,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK4)
    | k2_funct_2(X0,sK4) = k2_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_5843,plain,
    ( ~ v1_funct_2(sK4,sK3,sK3)
    | ~ v3_funct_2(sK4,sK3,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_funct_2(sK3,sK4) = k2_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5566])).

cnf(c_12430,plain,
    ( k2_funct_2(sK3,sK4) = k2_funct_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12052,c_76,c_75,c_74,c_73,c_5843])).

cnf(c_63,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f184])).

cnf(c_4798,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_15527,plain,
    ( v1_funct_2(sK4,sK3,sK3) != iProver_top
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12430,c_4798])).

cnf(c_78,plain,
    ( v1_funct_2(sK4,sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_16635,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15527,c_77,c_78,c_79,c_80])).

cnf(c_68,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f186])).

cnf(c_4793,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_16660,plain,
    ( k1_partfun1(X0,X1,sK3,sK3,X2,k2_funct_1(sK4)) = k5_relat_1(X2,k2_funct_1(sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16635,c_4793])).

cnf(c_66,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f181])).

cnf(c_4795,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_13172,plain,
    ( v1_funct_2(sK4,sK3,sK3) != iProver_top
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v1_funct_1(k2_funct_2(sK3,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4788,c_4795])).

cnf(c_13189,plain,
    ( v1_funct_2(sK4,sK3,sK3) != iProver_top
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13172,c_12430])).

cnf(c_19691,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK3,X2,k2_funct_1(sK4)) = k5_relat_1(X2,k2_funct_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16660,c_77,c_78,c_79,c_13189])).

cnf(c_19692,plain,
    ( k1_partfun1(X0,X1,sK3,sK3,X2,k2_funct_1(sK4)) = k5_relat_1(X2,k2_funct_1(sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_19691])).

cnf(c_19704,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)) = k5_relat_1(sK4,k2_funct_1(sK4))
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4788,c_19692])).

cnf(c_19733,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19704,c_15386])).

cnf(c_19828,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19733,c_77])).

cnf(c_12634,plain,
    ( k1_partfun1(X0,X1,sK3,sK3,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4788,c_4793])).

cnf(c_12904,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK3,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12634,c_77])).

cnf(c_12905,plain,
    ( k1_partfun1(X0,X1,sK3,sK3,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_12904])).

cnf(c_15541,plain,
    ( k1_partfun1(X0,X0,sK3,sK3,k2_funct_2(X0,X1),sK4) = k5_relat_1(k2_funct_2(X0,X1),sK4)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4798,c_12905])).

cnf(c_17081,plain,
    ( k1_partfun1(X0,X0,sK3,sK3,k2_funct_2(X0,X1),sK4) = k5_relat_1(k2_funct_2(X0,X1),sK4)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15541,c_4795])).

cnf(c_17089,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4) = k5_relat_1(k2_funct_2(sK3,sK4),sK4)
    | v1_funct_2(sK4,sK3,sK3) != iProver_top
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4788,c_17081])).

cnf(c_38,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f200])).

cnf(c_4816,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_15276,plain,
    ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_partfun1(k2_relat_1(sK4))
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_15271,c_4816])).

cnf(c_15287,plain,
    ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_partfun1(sK3)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15276,c_8433])).

cnf(c_5381,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5380])).

cnf(c_15340,plain,
    ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_partfun1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15287,c_77,c_80,c_5381])).

cnf(c_17126,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k6_partfun1(sK3)
    | v1_funct_2(sK4,sK3,sK3) != iProver_top
    | v3_funct_2(sK4,sK3,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17089,c_12430,c_15340])).

cnf(c_16651,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k5_relat_1(k2_funct_1(sK4),sK4)
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16635,c_12905])).

cnf(c_16724,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k6_partfun1(sK3)
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16651,c_15340])).

cnf(c_17198,plain,
    ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k6_partfun1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17126,c_77,c_78,c_79,c_13189,c_16724])).

cnf(c_72,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3))
    | ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) ),
    inference(cnf_transformation,[],[f195])).

cnf(c_4789,plain,
    ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3)) != iProver_top
    | r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_12433,plain,
    ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4),k6_partfun1(sK3)) != iProver_top
    | r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)),k6_partfun1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12430,c_4789])).

cnf(c_17201,plain,
    ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)),k6_partfun1(sK3)) != iProver_top
    | r2_relset_1(sK3,sK3,k6_partfun1(sK3),k6_partfun1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17198,c_12433])).

cnf(c_67,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f185])).

cnf(c_4794,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_45,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f204])).

cnf(c_4812,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_11425,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4794,c_4812])).

cnf(c_17299,plain,
    ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)),k6_partfun1(sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17201,c_11425])).

cnf(c_19831,plain,
    ( r2_relset_1(sK3,sK3,k6_partfun1(k1_relat_1(sK4)),k6_partfun1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19828,c_17299])).

cnf(c_21853,plain,
    ( r2_relset_1(sK3,sK3,k6_partfun1(sK3),k6_partfun1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21849,c_19831])).

cnf(c_22311,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21853,c_11425])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:20:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 6.90/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.90/1.49  
% 6.90/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.90/1.49  
% 6.90/1.49  ------  iProver source info
% 6.90/1.49  
% 6.90/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.90/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.90/1.49  git: non_committed_changes: false
% 6.90/1.49  git: last_make_outside_of_git: false
% 6.90/1.49  
% 6.90/1.49  ------ 
% 6.90/1.49  
% 6.90/1.49  ------ Input Options
% 6.90/1.49  
% 6.90/1.49  --out_options                           all
% 6.90/1.49  --tptp_safe_out                         true
% 6.90/1.49  --problem_path                          ""
% 6.90/1.49  --include_path                          ""
% 6.90/1.49  --clausifier                            res/vclausify_rel
% 6.90/1.49  --clausifier_options                    --mode clausify
% 6.90/1.49  --stdin                                 false
% 6.90/1.49  --stats_out                             all
% 6.90/1.49  
% 6.90/1.49  ------ General Options
% 6.90/1.49  
% 6.90/1.49  --fof                                   false
% 6.90/1.49  --time_out_real                         305.
% 6.90/1.49  --time_out_virtual                      -1.
% 6.90/1.49  --symbol_type_check                     false
% 6.90/1.49  --clausify_out                          false
% 6.90/1.49  --sig_cnt_out                           false
% 6.90/1.49  --trig_cnt_out                          false
% 6.90/1.49  --trig_cnt_out_tolerance                1.
% 6.90/1.49  --trig_cnt_out_sk_spl                   false
% 6.90/1.49  --abstr_cl_out                          false
% 6.90/1.49  
% 6.90/1.49  ------ Global Options
% 6.90/1.49  
% 6.90/1.49  --schedule                              default
% 6.90/1.49  --add_important_lit                     false
% 6.90/1.49  --prop_solver_per_cl                    1000
% 6.90/1.49  --min_unsat_core                        false
% 6.90/1.49  --soft_assumptions                      false
% 6.90/1.49  --soft_lemma_size                       3
% 6.90/1.49  --prop_impl_unit_size                   0
% 6.90/1.49  --prop_impl_unit                        []
% 6.90/1.49  --share_sel_clauses                     true
% 6.90/1.49  --reset_solvers                         false
% 6.90/1.49  --bc_imp_inh                            [conj_cone]
% 6.90/1.49  --conj_cone_tolerance                   3.
% 6.90/1.49  --extra_neg_conj                        none
% 6.90/1.49  --large_theory_mode                     true
% 6.90/1.49  --prolific_symb_bound                   200
% 6.90/1.49  --lt_threshold                          2000
% 6.90/1.49  --clause_weak_htbl                      true
% 6.90/1.49  --gc_record_bc_elim                     false
% 6.90/1.49  
% 6.90/1.49  ------ Preprocessing Options
% 6.90/1.49  
% 6.90/1.49  --preprocessing_flag                    true
% 6.90/1.49  --time_out_prep_mult                    0.1
% 6.90/1.49  --splitting_mode                        input
% 6.90/1.49  --splitting_grd                         true
% 6.90/1.49  --splitting_cvd                         false
% 6.90/1.49  --splitting_cvd_svl                     false
% 6.90/1.49  --splitting_nvd                         32
% 6.90/1.49  --sub_typing                            true
% 6.90/1.49  --prep_gs_sim                           true
% 6.90/1.49  --prep_unflatten                        true
% 6.90/1.49  --prep_res_sim                          true
% 6.90/1.49  --prep_upred                            true
% 6.90/1.49  --prep_sem_filter                       exhaustive
% 6.90/1.49  --prep_sem_filter_out                   false
% 6.90/1.49  --pred_elim                             true
% 6.90/1.49  --res_sim_input                         true
% 6.90/1.49  --eq_ax_congr_red                       true
% 6.90/1.49  --pure_diseq_elim                       true
% 6.90/1.49  --brand_transform                       false
% 6.90/1.49  --non_eq_to_eq                          false
% 6.90/1.49  --prep_def_merge                        true
% 6.90/1.49  --prep_def_merge_prop_impl              false
% 6.90/1.49  --prep_def_merge_mbd                    true
% 6.90/1.49  --prep_def_merge_tr_red                 false
% 6.90/1.49  --prep_def_merge_tr_cl                  false
% 6.90/1.49  --smt_preprocessing                     true
% 6.90/1.49  --smt_ac_axioms                         fast
% 6.90/1.49  --preprocessed_out                      false
% 6.90/1.49  --preprocessed_stats                    false
% 6.90/1.49  
% 6.90/1.49  ------ Abstraction refinement Options
% 6.90/1.49  
% 6.90/1.49  --abstr_ref                             []
% 6.90/1.49  --abstr_ref_prep                        false
% 6.90/1.49  --abstr_ref_until_sat                   false
% 6.90/1.49  --abstr_ref_sig_restrict                funpre
% 6.90/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.90/1.49  --abstr_ref_under                       []
% 6.90/1.49  
% 6.90/1.49  ------ SAT Options
% 6.90/1.49  
% 6.90/1.49  --sat_mode                              false
% 6.90/1.49  --sat_fm_restart_options                ""
% 6.90/1.49  --sat_gr_def                            false
% 6.90/1.49  --sat_epr_types                         true
% 6.90/1.49  --sat_non_cyclic_types                  false
% 6.90/1.49  --sat_finite_models                     false
% 6.90/1.49  --sat_fm_lemmas                         false
% 6.90/1.49  --sat_fm_prep                           false
% 6.90/1.49  --sat_fm_uc_incr                        true
% 6.90/1.49  --sat_out_model                         small
% 6.90/1.49  --sat_out_clauses                       false
% 6.90/1.49  
% 6.90/1.49  ------ QBF Options
% 6.90/1.49  
% 6.90/1.49  --qbf_mode                              false
% 6.90/1.49  --qbf_elim_univ                         false
% 6.90/1.49  --qbf_dom_inst                          none
% 6.90/1.49  --qbf_dom_pre_inst                      false
% 6.90/1.49  --qbf_sk_in                             false
% 6.90/1.49  --qbf_pred_elim                         true
% 6.90/1.49  --qbf_split                             512
% 6.90/1.49  
% 6.90/1.49  ------ BMC1 Options
% 6.90/1.49  
% 6.90/1.49  --bmc1_incremental                      false
% 6.90/1.49  --bmc1_axioms                           reachable_all
% 6.90/1.49  --bmc1_min_bound                        0
% 6.90/1.49  --bmc1_max_bound                        -1
% 6.90/1.49  --bmc1_max_bound_default                -1
% 6.90/1.49  --bmc1_symbol_reachability              true
% 6.90/1.49  --bmc1_property_lemmas                  false
% 6.90/1.49  --bmc1_k_induction                      false
% 6.90/1.49  --bmc1_non_equiv_states                 false
% 6.90/1.49  --bmc1_deadlock                         false
% 6.90/1.49  --bmc1_ucm                              false
% 6.90/1.49  --bmc1_add_unsat_core                   none
% 6.90/1.49  --bmc1_unsat_core_children              false
% 6.90/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.90/1.49  --bmc1_out_stat                         full
% 6.90/1.49  --bmc1_ground_init                      false
% 6.90/1.49  --bmc1_pre_inst_next_state              false
% 6.90/1.49  --bmc1_pre_inst_state                   false
% 6.90/1.49  --bmc1_pre_inst_reach_state             false
% 6.90/1.49  --bmc1_out_unsat_core                   false
% 6.90/1.49  --bmc1_aig_witness_out                  false
% 6.90/1.49  --bmc1_verbose                          false
% 6.90/1.49  --bmc1_dump_clauses_tptp                false
% 6.90/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.90/1.49  --bmc1_dump_file                        -
% 6.90/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.90/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.90/1.49  --bmc1_ucm_extend_mode                  1
% 6.90/1.49  --bmc1_ucm_init_mode                    2
% 6.90/1.49  --bmc1_ucm_cone_mode                    none
% 6.90/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.90/1.49  --bmc1_ucm_relax_model                  4
% 6.90/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.90/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.90/1.49  --bmc1_ucm_layered_model                none
% 6.90/1.49  --bmc1_ucm_max_lemma_size               10
% 6.90/1.49  
% 6.90/1.49  ------ AIG Options
% 6.90/1.49  
% 6.90/1.49  --aig_mode                              false
% 6.90/1.49  
% 6.90/1.49  ------ Instantiation Options
% 6.90/1.49  
% 6.90/1.49  --instantiation_flag                    true
% 6.90/1.49  --inst_sos_flag                         false
% 6.90/1.49  --inst_sos_phase                        true
% 6.90/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.90/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.90/1.49  --inst_lit_sel_side                     num_symb
% 6.90/1.49  --inst_solver_per_active                1400
% 6.90/1.49  --inst_solver_calls_frac                1.
% 6.90/1.49  --inst_passive_queue_type               priority_queues
% 6.90/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.90/1.49  --inst_passive_queues_freq              [25;2]
% 6.90/1.49  --inst_dismatching                      true
% 6.90/1.49  --inst_eager_unprocessed_to_passive     true
% 6.90/1.49  --inst_prop_sim_given                   true
% 6.90/1.49  --inst_prop_sim_new                     false
% 6.90/1.49  --inst_subs_new                         false
% 6.90/1.49  --inst_eq_res_simp                      false
% 6.90/1.49  --inst_subs_given                       false
% 6.90/1.49  --inst_orphan_elimination               true
% 6.90/1.49  --inst_learning_loop_flag               true
% 6.90/1.49  --inst_learning_start                   3000
% 6.90/1.49  --inst_learning_factor                  2
% 6.90/1.49  --inst_start_prop_sim_after_learn       3
% 6.90/1.49  --inst_sel_renew                        solver
% 6.90/1.49  --inst_lit_activity_flag                true
% 6.90/1.49  --inst_restr_to_given                   false
% 6.90/1.49  --inst_activity_threshold               500
% 6.90/1.49  --inst_out_proof                        true
% 6.90/1.49  
% 6.90/1.49  ------ Resolution Options
% 6.90/1.49  
% 6.90/1.49  --resolution_flag                       true
% 6.90/1.49  --res_lit_sel                           adaptive
% 6.90/1.49  --res_lit_sel_side                      none
% 6.90/1.49  --res_ordering                          kbo
% 6.90/1.49  --res_to_prop_solver                    active
% 6.90/1.49  --res_prop_simpl_new                    false
% 6.90/1.49  --res_prop_simpl_given                  true
% 6.90/1.49  --res_passive_queue_type                priority_queues
% 6.90/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.90/1.49  --res_passive_queues_freq               [15;5]
% 6.90/1.49  --res_forward_subs                      full
% 6.90/1.49  --res_backward_subs                     full
% 6.90/1.49  --res_forward_subs_resolution           true
% 6.90/1.49  --res_backward_subs_resolution          true
% 6.90/1.49  --res_orphan_elimination                true
% 6.90/1.49  --res_time_limit                        2.
% 6.90/1.49  --res_out_proof                         true
% 6.90/1.49  
% 6.90/1.49  ------ Superposition Options
% 6.90/1.49  
% 6.90/1.49  --superposition_flag                    true
% 6.90/1.49  --sup_passive_queue_type                priority_queues
% 6.90/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.90/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.90/1.49  --demod_completeness_check              fast
% 6.90/1.49  --demod_use_ground                      true
% 6.90/1.49  --sup_to_prop_solver                    passive
% 6.90/1.49  --sup_prop_simpl_new                    true
% 6.90/1.49  --sup_prop_simpl_given                  true
% 6.90/1.49  --sup_fun_splitting                     false
% 6.90/1.49  --sup_smt_interval                      50000
% 6.90/1.49  
% 6.90/1.49  ------ Superposition Simplification Setup
% 6.90/1.49  
% 6.90/1.49  --sup_indices_passive                   []
% 6.90/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.90/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.49  --sup_full_bw                           [BwDemod]
% 6.90/1.49  --sup_immed_triv                        [TrivRules]
% 6.90/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.90/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.49  --sup_immed_bw_main                     []
% 6.90/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.90/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.90/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.90/1.49  
% 6.90/1.49  ------ Combination Options
% 6.90/1.49  
% 6.90/1.49  --comb_res_mult                         3
% 6.90/1.49  --comb_sup_mult                         2
% 6.90/1.49  --comb_inst_mult                        10
% 6.90/1.49  
% 6.90/1.49  ------ Debug Options
% 6.90/1.49  
% 6.90/1.49  --dbg_backtrace                         false
% 6.90/1.49  --dbg_dump_prop_clauses                 false
% 6.90/1.49  --dbg_dump_prop_clauses_file            -
% 6.90/1.49  --dbg_out_stat                          false
% 6.90/1.49  ------ Parsing...
% 6.90/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.90/1.49  
% 6.90/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 6.90/1.49  
% 6.90/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.90/1.49  
% 6.90/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.90/1.49  ------ Proving...
% 6.90/1.49  ------ Problem Properties 
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  clauses                                 70
% 6.90/1.49  conjectures                             5
% 6.90/1.49  EPR                                     16
% 6.90/1.49  Horn                                    60
% 6.90/1.49  unary                                   12
% 6.90/1.49  binary                                  26
% 6.90/1.49  lits                                    189
% 6.90/1.49  lits eq                                 39
% 6.90/1.49  fd_pure                                 0
% 6.90/1.49  fd_pseudo                               0
% 6.90/1.49  fd_cond                                 8
% 6.90/1.49  fd_pseudo_cond                          4
% 6.90/1.49  AC symbols                              0
% 6.90/1.49  
% 6.90/1.49  ------ Schedule dynamic 5 is on 
% 6.90/1.49  
% 6.90/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  ------ 
% 6.90/1.49  Current options:
% 6.90/1.49  ------ 
% 6.90/1.49  
% 6.90/1.49  ------ Input Options
% 6.90/1.49  
% 6.90/1.49  --out_options                           all
% 6.90/1.49  --tptp_safe_out                         true
% 6.90/1.49  --problem_path                          ""
% 6.90/1.49  --include_path                          ""
% 6.90/1.49  --clausifier                            res/vclausify_rel
% 6.90/1.49  --clausifier_options                    --mode clausify
% 6.90/1.49  --stdin                                 false
% 6.90/1.49  --stats_out                             all
% 6.90/1.49  
% 6.90/1.49  ------ General Options
% 6.90/1.49  
% 6.90/1.49  --fof                                   false
% 6.90/1.49  --time_out_real                         305.
% 6.90/1.49  --time_out_virtual                      -1.
% 6.90/1.49  --symbol_type_check                     false
% 6.90/1.49  --clausify_out                          false
% 6.90/1.49  --sig_cnt_out                           false
% 6.90/1.49  --trig_cnt_out                          false
% 6.90/1.49  --trig_cnt_out_tolerance                1.
% 6.90/1.49  --trig_cnt_out_sk_spl                   false
% 6.90/1.49  --abstr_cl_out                          false
% 6.90/1.49  
% 6.90/1.49  ------ Global Options
% 6.90/1.49  
% 6.90/1.49  --schedule                              default
% 6.90/1.49  --add_important_lit                     false
% 6.90/1.49  --prop_solver_per_cl                    1000
% 6.90/1.49  --min_unsat_core                        false
% 6.90/1.49  --soft_assumptions                      false
% 6.90/1.49  --soft_lemma_size                       3
% 6.90/1.49  --prop_impl_unit_size                   0
% 6.90/1.49  --prop_impl_unit                        []
% 6.90/1.49  --share_sel_clauses                     true
% 6.90/1.49  --reset_solvers                         false
% 6.90/1.49  --bc_imp_inh                            [conj_cone]
% 6.90/1.49  --conj_cone_tolerance                   3.
% 6.90/1.49  --extra_neg_conj                        none
% 6.90/1.49  --large_theory_mode                     true
% 6.90/1.49  --prolific_symb_bound                   200
% 6.90/1.49  --lt_threshold                          2000
% 6.90/1.49  --clause_weak_htbl                      true
% 6.90/1.49  --gc_record_bc_elim                     false
% 6.90/1.49  
% 6.90/1.49  ------ Preprocessing Options
% 6.90/1.49  
% 6.90/1.49  --preprocessing_flag                    true
% 6.90/1.49  --time_out_prep_mult                    0.1
% 6.90/1.49  --splitting_mode                        input
% 6.90/1.49  --splitting_grd                         true
% 6.90/1.49  --splitting_cvd                         false
% 6.90/1.49  --splitting_cvd_svl                     false
% 6.90/1.49  --splitting_nvd                         32
% 6.90/1.49  --sub_typing                            true
% 6.90/1.49  --prep_gs_sim                           true
% 6.90/1.49  --prep_unflatten                        true
% 6.90/1.49  --prep_res_sim                          true
% 6.90/1.49  --prep_upred                            true
% 6.90/1.49  --prep_sem_filter                       exhaustive
% 6.90/1.49  --prep_sem_filter_out                   false
% 6.90/1.49  --pred_elim                             true
% 6.90/1.49  --res_sim_input                         true
% 6.90/1.49  --eq_ax_congr_red                       true
% 6.90/1.49  --pure_diseq_elim                       true
% 6.90/1.49  --brand_transform                       false
% 6.90/1.49  --non_eq_to_eq                          false
% 6.90/1.49  --prep_def_merge                        true
% 6.90/1.49  --prep_def_merge_prop_impl              false
% 6.90/1.49  --prep_def_merge_mbd                    true
% 6.90/1.49  --prep_def_merge_tr_red                 false
% 6.90/1.49  --prep_def_merge_tr_cl                  false
% 6.90/1.49  --smt_preprocessing                     true
% 6.90/1.49  --smt_ac_axioms                         fast
% 6.90/1.49  --preprocessed_out                      false
% 6.90/1.49  --preprocessed_stats                    false
% 6.90/1.49  
% 6.90/1.49  ------ Abstraction refinement Options
% 6.90/1.49  
% 6.90/1.49  --abstr_ref                             []
% 6.90/1.49  --abstr_ref_prep                        false
% 6.90/1.49  --abstr_ref_until_sat                   false
% 6.90/1.49  --abstr_ref_sig_restrict                funpre
% 6.90/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.90/1.49  --abstr_ref_under                       []
% 6.90/1.49  
% 6.90/1.49  ------ SAT Options
% 6.90/1.49  
% 6.90/1.49  --sat_mode                              false
% 6.90/1.49  --sat_fm_restart_options                ""
% 6.90/1.49  --sat_gr_def                            false
% 6.90/1.49  --sat_epr_types                         true
% 6.90/1.49  --sat_non_cyclic_types                  false
% 6.90/1.49  --sat_finite_models                     false
% 6.90/1.49  --sat_fm_lemmas                         false
% 6.90/1.49  --sat_fm_prep                           false
% 6.90/1.49  --sat_fm_uc_incr                        true
% 6.90/1.49  --sat_out_model                         small
% 6.90/1.49  --sat_out_clauses                       false
% 6.90/1.49  
% 6.90/1.49  ------ QBF Options
% 6.90/1.49  
% 6.90/1.49  --qbf_mode                              false
% 6.90/1.49  --qbf_elim_univ                         false
% 6.90/1.49  --qbf_dom_inst                          none
% 6.90/1.49  --qbf_dom_pre_inst                      false
% 6.90/1.49  --qbf_sk_in                             false
% 6.90/1.49  --qbf_pred_elim                         true
% 6.90/1.49  --qbf_split                             512
% 6.90/1.49  
% 6.90/1.49  ------ BMC1 Options
% 6.90/1.49  
% 6.90/1.49  --bmc1_incremental                      false
% 6.90/1.49  --bmc1_axioms                           reachable_all
% 6.90/1.49  --bmc1_min_bound                        0
% 6.90/1.49  --bmc1_max_bound                        -1
% 6.90/1.49  --bmc1_max_bound_default                -1
% 6.90/1.49  --bmc1_symbol_reachability              true
% 6.90/1.49  --bmc1_property_lemmas                  false
% 6.90/1.49  --bmc1_k_induction                      false
% 6.90/1.49  --bmc1_non_equiv_states                 false
% 6.90/1.49  --bmc1_deadlock                         false
% 6.90/1.49  --bmc1_ucm                              false
% 6.90/1.49  --bmc1_add_unsat_core                   none
% 6.90/1.49  --bmc1_unsat_core_children              false
% 6.90/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.90/1.49  --bmc1_out_stat                         full
% 6.90/1.49  --bmc1_ground_init                      false
% 6.90/1.49  --bmc1_pre_inst_next_state              false
% 6.90/1.49  --bmc1_pre_inst_state                   false
% 6.90/1.49  --bmc1_pre_inst_reach_state             false
% 6.90/1.49  --bmc1_out_unsat_core                   false
% 6.90/1.49  --bmc1_aig_witness_out                  false
% 6.90/1.49  --bmc1_verbose                          false
% 6.90/1.49  --bmc1_dump_clauses_tptp                false
% 6.90/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.90/1.49  --bmc1_dump_file                        -
% 6.90/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.90/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.90/1.49  --bmc1_ucm_extend_mode                  1
% 6.90/1.49  --bmc1_ucm_init_mode                    2
% 6.90/1.49  --bmc1_ucm_cone_mode                    none
% 6.90/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.90/1.49  --bmc1_ucm_relax_model                  4
% 6.90/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.90/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.90/1.49  --bmc1_ucm_layered_model                none
% 6.90/1.49  --bmc1_ucm_max_lemma_size               10
% 6.90/1.49  
% 6.90/1.49  ------ AIG Options
% 6.90/1.49  
% 6.90/1.49  --aig_mode                              false
% 6.90/1.49  
% 6.90/1.49  ------ Instantiation Options
% 6.90/1.49  
% 6.90/1.49  --instantiation_flag                    true
% 6.90/1.49  --inst_sos_flag                         false
% 6.90/1.49  --inst_sos_phase                        true
% 6.90/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.90/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.90/1.49  --inst_lit_sel_side                     none
% 6.90/1.49  --inst_solver_per_active                1400
% 6.90/1.49  --inst_solver_calls_frac                1.
% 6.90/1.49  --inst_passive_queue_type               priority_queues
% 6.90/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.90/1.49  --inst_passive_queues_freq              [25;2]
% 6.90/1.49  --inst_dismatching                      true
% 6.90/1.49  --inst_eager_unprocessed_to_passive     true
% 6.90/1.49  --inst_prop_sim_given                   true
% 6.90/1.49  --inst_prop_sim_new                     false
% 6.90/1.49  --inst_subs_new                         false
% 6.90/1.49  --inst_eq_res_simp                      false
% 6.90/1.49  --inst_subs_given                       false
% 6.90/1.49  --inst_orphan_elimination               true
% 6.90/1.49  --inst_learning_loop_flag               true
% 6.90/1.49  --inst_learning_start                   3000
% 6.90/1.49  --inst_learning_factor                  2
% 6.90/1.49  --inst_start_prop_sim_after_learn       3
% 6.90/1.49  --inst_sel_renew                        solver
% 6.90/1.49  --inst_lit_activity_flag                true
% 6.90/1.49  --inst_restr_to_given                   false
% 6.90/1.49  --inst_activity_threshold               500
% 6.90/1.49  --inst_out_proof                        true
% 6.90/1.49  
% 6.90/1.49  ------ Resolution Options
% 6.90/1.49  
% 6.90/1.49  --resolution_flag                       false
% 6.90/1.49  --res_lit_sel                           adaptive
% 6.90/1.49  --res_lit_sel_side                      none
% 6.90/1.49  --res_ordering                          kbo
% 6.90/1.49  --res_to_prop_solver                    active
% 6.90/1.49  --res_prop_simpl_new                    false
% 6.90/1.49  --res_prop_simpl_given                  true
% 6.90/1.49  --res_passive_queue_type                priority_queues
% 6.90/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.90/1.49  --res_passive_queues_freq               [15;5]
% 6.90/1.49  --res_forward_subs                      full
% 6.90/1.49  --res_backward_subs                     full
% 6.90/1.49  --res_forward_subs_resolution           true
% 6.90/1.49  --res_backward_subs_resolution          true
% 6.90/1.49  --res_orphan_elimination                true
% 6.90/1.49  --res_time_limit                        2.
% 6.90/1.49  --res_out_proof                         true
% 6.90/1.49  
% 6.90/1.49  ------ Superposition Options
% 6.90/1.49  
% 6.90/1.49  --superposition_flag                    true
% 6.90/1.49  --sup_passive_queue_type                priority_queues
% 6.90/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.90/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.90/1.49  --demod_completeness_check              fast
% 6.90/1.49  --demod_use_ground                      true
% 6.90/1.49  --sup_to_prop_solver                    passive
% 6.90/1.49  --sup_prop_simpl_new                    true
% 6.90/1.49  --sup_prop_simpl_given                  true
% 6.90/1.49  --sup_fun_splitting                     false
% 6.90/1.49  --sup_smt_interval                      50000
% 6.90/1.49  
% 6.90/1.49  ------ Superposition Simplification Setup
% 6.90/1.49  
% 6.90/1.49  --sup_indices_passive                   []
% 6.90/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.90/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.49  --sup_full_bw                           [BwDemod]
% 6.90/1.49  --sup_immed_triv                        [TrivRules]
% 6.90/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.90/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.49  --sup_immed_bw_main                     []
% 6.90/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.90/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.90/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.90/1.49  
% 6.90/1.49  ------ Combination Options
% 6.90/1.49  
% 6.90/1.49  --comb_res_mult                         3
% 6.90/1.49  --comb_sup_mult                         2
% 6.90/1.49  --comb_inst_mult                        10
% 6.90/1.49  
% 6.90/1.49  ------ Debug Options
% 6.90/1.49  
% 6.90/1.49  --dbg_backtrace                         false
% 6.90/1.49  --dbg_dump_prop_clauses                 false
% 6.90/1.49  --dbg_dump_prop_clauses_file            -
% 6.90/1.49  --dbg_out_stat                          false
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  ------ Proving...
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  % SZS status Theorem for theBenchmark.p
% 6.90/1.49  
% 6.90/1.49   Resolution empty clause
% 6.90/1.49  
% 6.90/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.90/1.49  
% 6.90/1.49  fof(f45,conjecture,(
% 6.90/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f46,negated_conjecture,(
% 6.90/1.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 6.90/1.49    inference(negated_conjecture,[],[f45])).
% 6.90/1.49  
% 6.90/1.49  fof(f98,plain,(
% 6.90/1.49    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 6.90/1.49    inference(ennf_transformation,[],[f46])).
% 6.90/1.49  
% 6.90/1.49  fof(f99,plain,(
% 6.90/1.49    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 6.90/1.49    inference(flattening,[],[f98])).
% 6.90/1.49  
% 6.90/1.49  fof(f116,plain,(
% 6.90/1.49    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3)) | ~r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v3_funct_2(sK4,sK3,sK3) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4))),
% 6.90/1.49    introduced(choice_axiom,[])).
% 6.90/1.49  
% 6.90/1.49  fof(f117,plain,(
% 6.90/1.49    (~r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3)) | ~r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v3_funct_2(sK4,sK3,sK3) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4)),
% 6.90/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f99,f116])).
% 6.90/1.49  
% 6.90/1.49  fof(f194,plain,(
% 6.90/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))),
% 6.90/1.49    inference(cnf_transformation,[],[f117])).
% 6.90/1.49  
% 6.90/1.49  fof(f30,axiom,(
% 6.90/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f78,plain,(
% 6.90/1.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.49    inference(ennf_transformation,[],[f30])).
% 6.90/1.49  
% 6.90/1.49  fof(f160,plain,(
% 6.90/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.49    inference(cnf_transformation,[],[f78])).
% 6.90/1.49  
% 6.90/1.49  fof(f17,axiom,(
% 6.90/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f63,plain,(
% 6.90/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.90/1.49    inference(ennf_transformation,[],[f17])).
% 6.90/1.49  
% 6.90/1.49  fof(f112,plain,(
% 6.90/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.90/1.49    inference(nnf_transformation,[],[f63])).
% 6.90/1.49  
% 6.90/1.49  fof(f142,plain,(
% 6.90/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f112])).
% 6.90/1.49  
% 6.90/1.49  fof(f29,axiom,(
% 6.90/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f77,plain,(
% 6.90/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.49    inference(ennf_transformation,[],[f29])).
% 6.90/1.49  
% 6.90/1.49  fof(f159,plain,(
% 6.90/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.49    inference(cnf_transformation,[],[f77])).
% 6.90/1.49  
% 6.90/1.49  fof(f3,axiom,(
% 6.90/1.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f47,plain,(
% 6.90/1.49    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 6.90/1.49    inference(unused_predicate_definition_removal,[],[f3])).
% 6.90/1.49  
% 6.90/1.49  fof(f50,plain,(
% 6.90/1.49    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 6.90/1.49    inference(ennf_transformation,[],[f47])).
% 6.90/1.49  
% 6.90/1.49  fof(f51,plain,(
% 6.90/1.49    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 6.90/1.49    inference(flattening,[],[f50])).
% 6.90/1.49  
% 6.90/1.49  fof(f123,plain,(
% 6.90/1.49    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f51])).
% 6.90/1.49  
% 6.90/1.49  fof(f6,axiom,(
% 6.90/1.49    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f53,plain,(
% 6.90/1.49    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 6.90/1.49    inference(ennf_transformation,[],[f6])).
% 6.90/1.49  
% 6.90/1.49  fof(f108,plain,(
% 6.90/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1)))),
% 6.90/1.49    introduced(choice_axiom,[])).
% 6.90/1.49  
% 6.90/1.49  fof(f109,plain,(
% 6.90/1.49    ! [X0,X1] : ((~r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 6.90/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f108])).
% 6.90/1.49  
% 6.90/1.49  fof(f126,plain,(
% 6.90/1.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f109])).
% 6.90/1.49  
% 6.90/1.49  fof(f9,axiom,(
% 6.90/1.49    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f56,plain,(
% 6.90/1.49    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 6.90/1.49    inference(ennf_transformation,[],[f9])).
% 6.90/1.49  
% 6.90/1.49  fof(f130,plain,(
% 6.90/1.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f56])).
% 6.90/1.49  
% 6.90/1.49  fof(f4,axiom,(
% 6.90/1.49    v1_xboole_0(k1_xboole_0)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f124,plain,(
% 6.90/1.49    v1_xboole_0(k1_xboole_0)),
% 6.90/1.49    inference(cnf_transformation,[],[f4])).
% 6.90/1.49  
% 6.90/1.49  fof(f34,axiom,(
% 6.90/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f82,plain,(
% 6.90/1.49    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.49    inference(ennf_transformation,[],[f34])).
% 6.90/1.49  
% 6.90/1.49  fof(f166,plain,(
% 6.90/1.49    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.49    inference(cnf_transformation,[],[f82])).
% 6.90/1.49  
% 6.90/1.49  fof(f23,axiom,(
% 6.90/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f71,plain,(
% 6.90/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.90/1.49    inference(ennf_transformation,[],[f23])).
% 6.90/1.49  
% 6.90/1.49  fof(f72,plain,(
% 6.90/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.90/1.49    inference(flattening,[],[f71])).
% 6.90/1.49  
% 6.90/1.49  fof(f149,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f72])).
% 6.90/1.49  
% 6.90/1.49  fof(f22,axiom,(
% 6.90/1.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f70,plain,(
% 6.90/1.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.90/1.49    inference(ennf_transformation,[],[f22])).
% 6.90/1.49  
% 6.90/1.49  fof(f148,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f70])).
% 6.90/1.49  
% 6.90/1.49  fof(f36,axiom,(
% 6.90/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f84,plain,(
% 6.90/1.49    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.49    inference(ennf_transformation,[],[f36])).
% 6.90/1.49  
% 6.90/1.49  fof(f85,plain,(
% 6.90/1.49    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.49    inference(flattening,[],[f84])).
% 6.90/1.49  
% 6.90/1.49  fof(f172,plain,(
% 6.90/1.49    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.49    inference(cnf_transformation,[],[f85])).
% 6.90/1.49  
% 6.90/1.49  fof(f161,plain,(
% 6.90/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.49    inference(cnf_transformation,[],[f78])).
% 6.90/1.49  
% 6.90/1.49  fof(f38,axiom,(
% 6.90/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f88,plain,(
% 6.90/1.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.90/1.49    inference(ennf_transformation,[],[f38])).
% 6.90/1.49  
% 6.90/1.49  fof(f89,plain,(
% 6.90/1.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.90/1.49    inference(flattening,[],[f88])).
% 6.90/1.49  
% 6.90/1.49  fof(f115,plain,(
% 6.90/1.49    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.90/1.49    inference(nnf_transformation,[],[f89])).
% 6.90/1.49  
% 6.90/1.49  fof(f179,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f115])).
% 6.90/1.49  
% 6.90/1.49  fof(f191,plain,(
% 6.90/1.49    v1_funct_1(sK4)),
% 6.90/1.49    inference(cnf_transformation,[],[f117])).
% 6.90/1.49  
% 6.90/1.49  fof(f193,plain,(
% 6.90/1.49    v3_funct_2(sK4,sK3,sK3)),
% 6.90/1.49    inference(cnf_transformation,[],[f117])).
% 6.90/1.49  
% 6.90/1.49  fof(f31,axiom,(
% 6.90/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f79,plain,(
% 6.90/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.49    inference(ennf_transformation,[],[f31])).
% 6.90/1.49  
% 6.90/1.49  fof(f162,plain,(
% 6.90/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.49    inference(cnf_transformation,[],[f79])).
% 6.90/1.49  
% 6.90/1.49  fof(f44,axiom,(
% 6.90/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f96,plain,(
% 6.90/1.49    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.90/1.49    inference(ennf_transformation,[],[f44])).
% 6.90/1.49  
% 6.90/1.49  fof(f97,plain,(
% 6.90/1.49    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.90/1.49    inference(flattening,[],[f96])).
% 6.90/1.49  
% 6.90/1.49  fof(f189,plain,(
% 6.90/1.49    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f97])).
% 6.90/1.49  
% 6.90/1.49  fof(f192,plain,(
% 6.90/1.49    v1_funct_2(sK4,sK3,sK3)),
% 6.90/1.49    inference(cnf_transformation,[],[f117])).
% 6.90/1.49  
% 6.90/1.49  fof(f171,plain,(
% 6.90/1.49    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.49    inference(cnf_transformation,[],[f85])).
% 6.90/1.49  
% 6.90/1.49  fof(f27,axiom,(
% 6.90/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f75,plain,(
% 6.90/1.49    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.90/1.49    inference(ennf_transformation,[],[f27])).
% 6.90/1.49  
% 6.90/1.49  fof(f76,plain,(
% 6.90/1.49    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.90/1.49    inference(flattening,[],[f75])).
% 6.90/1.49  
% 6.90/1.49  fof(f156,plain,(
% 6.90/1.49    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f76])).
% 6.90/1.49  
% 6.90/1.49  fof(f43,axiom,(
% 6.90/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f188,plain,(
% 6.90/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f43])).
% 6.90/1.49  
% 6.90/1.49  fof(f201,plain,(
% 6.90/1.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f156,f188])).
% 6.90/1.49  
% 6.90/1.49  fof(f25,axiom,(
% 6.90/1.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f153,plain,(
% 6.90/1.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 6.90/1.49    inference(cnf_transformation,[],[f25])).
% 6.90/1.49  
% 6.90/1.49  fof(f196,plain,(
% 6.90/1.49    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 6.90/1.49    inference(definition_unfolding,[],[f153,f188])).
% 6.90/1.49  
% 6.90/1.49  fof(f42,axiom,(
% 6.90/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f94,plain,(
% 6.90/1.49    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 6.90/1.49    inference(ennf_transformation,[],[f42])).
% 6.90/1.49  
% 6.90/1.49  fof(f95,plain,(
% 6.90/1.49    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 6.90/1.49    inference(flattening,[],[f94])).
% 6.90/1.49  
% 6.90/1.49  fof(f187,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f95])).
% 6.90/1.49  
% 6.90/1.49  fof(f39,axiom,(
% 6.90/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f90,plain,(
% 6.90/1.49    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 6.90/1.49    inference(ennf_transformation,[],[f39])).
% 6.90/1.49  
% 6.90/1.49  fof(f91,plain,(
% 6.90/1.49    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 6.90/1.49    inference(flattening,[],[f90])).
% 6.90/1.49  
% 6.90/1.49  fof(f184,plain,(
% 6.90/1.49    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f91])).
% 6.90/1.49  
% 6.90/1.49  fof(f41,axiom,(
% 6.90/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f92,plain,(
% 6.90/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.90/1.49    inference(ennf_transformation,[],[f41])).
% 6.90/1.49  
% 6.90/1.49  fof(f93,plain,(
% 6.90/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.90/1.49    inference(flattening,[],[f92])).
% 6.90/1.49  
% 6.90/1.49  fof(f186,plain,(
% 6.90/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f93])).
% 6.90/1.49  
% 6.90/1.49  fof(f181,plain,(
% 6.90/1.49    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f91])).
% 6.90/1.49  
% 6.90/1.49  fof(f157,plain,(
% 6.90/1.49    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f76])).
% 6.90/1.49  
% 6.90/1.49  fof(f200,plain,(
% 6.90/1.49    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f157,f188])).
% 6.90/1.49  
% 6.90/1.49  fof(f195,plain,(
% 6.90/1.49    ~r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3)) | ~r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3))),
% 6.90/1.49    inference(cnf_transformation,[],[f117])).
% 6.90/1.49  
% 6.90/1.49  fof(f40,axiom,(
% 6.90/1.49    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f48,plain,(
% 6.90/1.49    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 6.90/1.49    inference(pure_predicate_removal,[],[f40])).
% 6.90/1.49  
% 6.90/1.49  fof(f185,plain,(
% 6.90/1.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 6.90/1.49    inference(cnf_transformation,[],[f48])).
% 6.90/1.49  
% 6.90/1.49  fof(f32,axiom,(
% 6.90/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f80,plain,(
% 6.90/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.90/1.49    inference(ennf_transformation,[],[f32])).
% 6.90/1.49  
% 6.90/1.49  fof(f81,plain,(
% 6.90/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.49    inference(flattening,[],[f80])).
% 6.90/1.49  
% 6.90/1.49  fof(f113,plain,(
% 6.90/1.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.90/1.49    inference(nnf_transformation,[],[f81])).
% 6.90/1.49  
% 6.90/1.49  fof(f164,plain,(
% 6.90/1.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.49    inference(cnf_transformation,[],[f113])).
% 6.90/1.49  
% 6.90/1.49  fof(f204,plain,(
% 6.90/1.49    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.90/1.49    inference(equality_resolution,[],[f164])).
% 6.90/1.49  
% 6.90/1.49  cnf(c_73,negated_conjecture,
% 6.90/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
% 6.90/1.49      inference(cnf_transformation,[],[f194]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_4788,plain,
% 6.90/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
% 6.90/1.49      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_43,plain,
% 6.90/1.49      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.90/1.49      inference(cnf_transformation,[],[f160]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_25,plain,
% 6.90/1.49      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 6.90/1.49      inference(cnf_transformation,[],[f142]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_1094,plain,
% 6.90/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.90/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 6.90/1.49      | ~ v1_relat_1(X0) ),
% 6.90/1.49      inference(resolution,[status(thm)],[c_43,c_25]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_41,plain,
% 6.90/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 6.90/1.49      inference(cnf_transformation,[],[f159]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_1098,plain,
% 6.90/1.49      ( r1_tarski(k1_relat_1(X0),X1)
% 6.90/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.90/1.50      inference(global_propositional_subsumption,[status(thm)],[c_1094,c_41]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_1099,plain,
% 6.90/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.90/1.50      | r1_tarski(k1_relat_1(X0),X1) ),
% 6.90/1.50      inference(renaming,[status(thm)],[c_1098]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4778,plain,
% 6.90/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.90/1.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_1099]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_5825,plain,
% 6.90/1.50      ( r1_tarski(k1_relat_1(sK4),sK3) = iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4788,c_4778]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_5,plain,
% 6.90/1.50      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 6.90/1.50      inference(cnf_transformation,[],[f123]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4838,plain,
% 6.90/1.50      ( X0 = X1
% 6.90/1.50      | r2_xboole_0(X1,X0) = iProver_top
% 6.90/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_11086,plain,
% 6.90/1.50      ( k1_relat_1(sK4) = sK3
% 6.90/1.50      | r2_xboole_0(k1_relat_1(sK4),sK3) = iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_5825,c_4838]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_9,plain,
% 6.90/1.50      ( ~ r2_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1) ),
% 6.90/1.50      inference(cnf_transformation,[],[f126]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4834,plain,
% 6.90/1.50      ( r2_xboole_0(X0,X1) != iProver_top
% 6.90/1.50      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_12,plain,
% 6.90/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 6.90/1.50      inference(cnf_transformation,[],[f130]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4842,plain,
% 6.90/1.50      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_8163,plain,
% 6.90/1.50      ( r2_xboole_0(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4834,c_4842]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_21836,plain,
% 6.90/1.50      ( k1_relat_1(sK4) = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_11086,c_8163]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_6,plain,
% 6.90/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 6.90/1.50      inference(cnf_transformation,[],[f124]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_3337,plain,
% 6.90/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 6.90/1.50      theory(equality) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_7788,plain,
% 6.90/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 6.90/1.50      inference(instantiation,[status(thm)],[c_3337]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_7795,plain,
% 6.90/1.50      ( v1_xboole_0(sK3) | ~ v1_xboole_0(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 6.90/1.50      inference(instantiation,[status(thm)],[c_7788]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_49,plain,
% 6.90/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.90/1.50      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 6.90/1.50      inference(cnf_transformation,[],[f166]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4808,plain,
% 6.90/1.50      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 6.90/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_12820,plain,
% 6.90/1.50      ( k7_relset_1(sK3,sK3,sK4,sK3) = k2_relset_1(sK3,sK3,sK4) ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4788,c_4808]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_31,plain,
% 6.90/1.50      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 6.90/1.50      inference(cnf_transformation,[],[f149]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_1077,plain,
% 6.90/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.90/1.50      | ~ v1_relat_1(X0)
% 6.90/1.50      | k7_relat_1(X0,X1) = X0 ),
% 6.90/1.50      inference(resolution,[status(thm)],[c_43,c_31]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_1081,plain,
% 6.90/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.90/1.50      | k7_relat_1(X0,X1) = X0 ),
% 6.90/1.50      inference(global_propositional_subsumption,
% 6.90/1.50                [status(thm)],
% 6.90/1.50                [c_1077,c_43,c_41,c_31]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4779,plain,
% 6.90/1.50      ( k7_relat_1(X0,X1) = X0
% 6.90/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_1081]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_6760,plain,
% 6.90/1.50      ( k7_relat_1(sK4,sK3) = sK4 ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4788,c_4779]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4814,plain,
% 6.90/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.90/1.50      | v1_relat_1(X0) = iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_7859,plain,
% 6.90/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4788,c_4814]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_30,plain,
% 6.90/1.50      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 6.90/1.50      inference(cnf_transformation,[],[f148]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4821,plain,
% 6.90/1.50      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 6.90/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_8169,plain,
% 6.90/1.50      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_7859,c_4821]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_8439,plain,
% 6.90/1.50      ( k9_relat_1(sK4,sK3) = k2_relat_1(sK4) ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_6760,c_8169]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_52,plain,
% 6.90/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 6.90/1.50      | v2_funct_2(X0,X2)
% 6.90/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.90/1.50      | ~ v1_funct_1(X0) ),
% 6.90/1.50      inference(cnf_transformation,[],[f172]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_42,plain,
% 6.90/1.50      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 6.90/1.50      inference(cnf_transformation,[],[f161]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_62,plain,
% 6.90/1.50      ( ~ v2_funct_2(X0,X1)
% 6.90/1.50      | ~ v5_relat_1(X0,X1)
% 6.90/1.50      | ~ v1_relat_1(X0)
% 6.90/1.50      | k2_relat_1(X0) = X1 ),
% 6.90/1.50      inference(cnf_transformation,[],[f179]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_1005,plain,
% 6.90/1.50      ( ~ v2_funct_2(X0,X1)
% 6.90/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 6.90/1.50      | ~ v1_relat_1(X0)
% 6.90/1.50      | k2_relat_1(X0) = X1 ),
% 6.90/1.50      inference(resolution,[status(thm)],[c_42,c_62]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_1017,plain,
% 6.90/1.50      ( ~ v2_funct_2(X0,X1)
% 6.90/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 6.90/1.50      | k2_relat_1(X0) = X1 ),
% 6.90/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_1005,c_41]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_1048,plain,
% 6.90/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 6.90/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.90/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 6.90/1.50      | ~ v1_funct_1(X0)
% 6.90/1.50      | X3 != X0
% 6.90/1.50      | X5 != X2
% 6.90/1.50      | k2_relat_1(X3) = X5 ),
% 6.90/1.50      inference(resolution_lifted,[status(thm)],[c_52,c_1017]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_1049,plain,
% 6.90/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 6.90/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.90/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 6.90/1.50      | ~ v1_funct_1(X0)
% 6.90/1.50      | k2_relat_1(X0) = X2 ),
% 6.90/1.50      inference(unflattening,[status(thm)],[c_1048]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4780,plain,
% 6.90/1.50      ( k2_relat_1(X0) = X1
% 6.90/1.50      | v3_funct_2(X0,X2,X1) != iProver_top
% 6.90/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 6.90/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 6.90/1.50      | v1_funct_1(X0) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_1049]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_7564,plain,
% 6.90/1.50      ( k2_relat_1(sK4) = sK3
% 6.90/1.50      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4788,c_4780]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_76,negated_conjecture,
% 6.90/1.50      ( v1_funct_1(sK4) ),
% 6.90/1.50      inference(cnf_transformation,[],[f191]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_74,negated_conjecture,
% 6.90/1.50      ( v3_funct_2(sK4,sK3,sK3) ),
% 6.90/1.50      inference(cnf_transformation,[],[f193]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_5519,plain,
% 6.90/1.50      ( ~ v3_funct_2(sK4,X0,X1)
% 6.90/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.90/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 6.90/1.50      | ~ v1_funct_1(sK4)
% 6.90/1.50      | k2_relat_1(sK4) = X1 ),
% 6.90/1.50      inference(instantiation,[status(thm)],[c_1049]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_5838,plain,
% 6.90/1.50      ( ~ v3_funct_2(sK4,sK3,sK3)
% 6.90/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
% 6.90/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 6.90/1.50      | ~ v1_funct_1(sK4)
% 6.90/1.50      | k2_relat_1(sK4) = sK3 ),
% 6.90/1.50      inference(instantiation,[status(thm)],[c_5519]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_6056,plain,
% 6.90/1.50      ( ~ v3_funct_2(sK4,sK3,sK3)
% 6.90/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 6.90/1.50      | ~ v1_funct_1(sK4)
% 6.90/1.50      | k2_relat_1(sK4) = sK3 ),
% 6.90/1.50      inference(instantiation,[status(thm)],[c_5838]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_8433,plain,
% 6.90/1.50      ( k2_relat_1(sK4) = sK3 ),
% 6.90/1.50      inference(global_propositional_subsumption,
% 6.90/1.50                [status(thm)],
% 6.90/1.50                [c_7564,c_76,c_74,c_73,c_6056]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_8446,plain,
% 6.90/1.50      ( k9_relat_1(sK4,sK3) = sK3 ),
% 6.90/1.50      inference(light_normalisation,[status(thm)],[c_8439,c_8433]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_44,plain,
% 6.90/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.90/1.50      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 6.90/1.50      inference(cnf_transformation,[],[f162]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4813,plain,
% 6.90/1.50      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 6.90/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_12319,plain,
% 6.90/1.50      ( k7_relset_1(sK3,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4788,c_4813]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_12832,plain,
% 6.90/1.50      ( k2_relset_1(sK3,sK3,sK4) = sK3 ),
% 6.90/1.50      inference(demodulation,[status(thm)],[c_12820,c_8446,c_12319]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_71,plain,
% 6.90/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.90/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.90/1.50      | ~ v2_funct_1(X0)
% 6.90/1.50      | ~ v1_funct_1(X0)
% 6.90/1.50      | k2_relset_1(X1,X2,X0) != X2
% 6.90/1.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 6.90/1.50      | k1_xboole_0 = X2 ),
% 6.90/1.50      inference(cnf_transformation,[],[f189]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4790,plain,
% 6.90/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 6.90/1.50      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 6.90/1.50      | k1_xboole_0 = X1
% 6.90/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.90/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.90/1.50      | v2_funct_1(X2) != iProver_top
% 6.90/1.50      | v1_funct_1(X2) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_12981,plain,
% 6.90/1.50      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK3)
% 6.90/1.50      | sK3 = k1_xboole_0
% 6.90/1.50      | v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
% 6.90/1.50      | v2_funct_1(sK4) != iProver_top
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_12832,c_4790]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_75,negated_conjecture,
% 6.90/1.50      ( v1_funct_2(sK4,sK3,sK3) ),
% 6.90/1.50      inference(cnf_transformation,[],[f192]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_53,plain,
% 6.90/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 6.90/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.90/1.50      | v2_funct_1(X0)
% 6.90/1.50      | ~ v1_funct_1(X0) ),
% 6.90/1.50      inference(cnf_transformation,[],[f171]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_5454,plain,
% 6.90/1.50      ( ~ v3_funct_2(sK4,X0,X1)
% 6.90/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.90/1.50      | v2_funct_1(sK4)
% 6.90/1.50      | ~ v1_funct_1(sK4) ),
% 6.90/1.50      inference(instantiation,[status(thm)],[c_53]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_5730,plain,
% 6.90/1.50      ( ~ v3_funct_2(sK4,sK3,sK3)
% 6.90/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 6.90/1.50      | v2_funct_1(sK4)
% 6.90/1.50      | ~ v1_funct_1(sK4) ),
% 6.90/1.50      inference(instantiation,[status(thm)],[c_5454]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_13007,plain,
% 6.90/1.50      ( ~ v1_funct_2(sK4,sK3,sK3)
% 6.90/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 6.90/1.50      | ~ v2_funct_1(sK4)
% 6.90/1.50      | ~ v1_funct_1(sK4)
% 6.90/1.50      | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK3)
% 6.90/1.50      | sK3 = k1_xboole_0 ),
% 6.90/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_12981]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_20737,plain,
% 6.90/1.50      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK3)
% 6.90/1.50      | sK3 = k1_xboole_0 ),
% 6.90/1.50      inference(global_propositional_subsumption,
% 6.90/1.50                [status(thm)],
% 6.90/1.50                [c_12981,c_76,c_75,c_74,c_73,c_5730,c_13007]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4805,plain,
% 6.90/1.50      ( v3_funct_2(X0,X1,X2) != iProver_top
% 6.90/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.90/1.50      | v2_funct_1(X0) = iProver_top
% 6.90/1.50      | v1_funct_1(X0) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_15085,plain,
% 6.90/1.50      ( v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | v2_funct_1(sK4) = iProver_top
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4788,c_4805]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_77,plain,
% 6.90/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_76]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_79,plain,
% 6.90/1.50      ( v3_funct_2(sK4,sK3,sK3) = iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_80,plain,
% 6.90/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_5731,plain,
% 6.90/1.50      ( v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
% 6.90/1.50      | v2_funct_1(sK4) = iProver_top
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_5730]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_15271,plain,
% 6.90/1.50      ( v2_funct_1(sK4) = iProver_top ),
% 6.90/1.50      inference(global_propositional_subsumption,
% 6.90/1.50                [status(thm)],
% 6.90/1.50                [c_15085,c_77,c_79,c_80,c_5731]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_39,plain,
% 6.90/1.50      ( ~ v2_funct_1(X0)
% 6.90/1.50      | ~ v1_funct_1(X0)
% 6.90/1.50      | ~ v1_relat_1(X0)
% 6.90/1.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 6.90/1.50      inference(cnf_transformation,[],[f201]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4815,plain,
% 6.90/1.50      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 6.90/1.50      | v2_funct_1(X0) != iProver_top
% 6.90/1.50      | v1_funct_1(X0) != iProver_top
% 6.90/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_15277,plain,
% 6.90/1.50      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top
% 6.90/1.50      | v1_relat_1(sK4) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_15271,c_4815]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_5380,plain,
% 6.90/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 6.90/1.50      | v1_relat_1(sK4) ),
% 6.90/1.50      inference(instantiation,[status(thm)],[c_41]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_6005,plain,
% 6.90/1.50      ( ~ v2_funct_1(sK4)
% 6.90/1.50      | ~ v1_funct_1(sK4)
% 6.90/1.50      | ~ v1_relat_1(sK4)
% 6.90/1.50      | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
% 6.90/1.50      inference(instantiation,[status(thm)],[c_39]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_15386,plain,
% 6.90/1.50      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
% 6.90/1.50      inference(global_propositional_subsumption,
% 6.90/1.50                [status(thm)],
% 6.90/1.50                [c_15277,c_76,c_74,c_73,c_5380,c_5730,c_6005]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_20739,plain,
% 6.90/1.50      ( k6_partfun1(k1_relat_1(sK4)) = k6_partfun1(sK3) | sK3 = k1_xboole_0 ),
% 6.90/1.50      inference(demodulation,[status(thm)],[c_20737,c_15386]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_34,plain,
% 6.90/1.50      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 6.90/1.50      inference(cnf_transformation,[],[f196]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_20760,plain,
% 6.90/1.50      ( k2_relat_1(k6_partfun1(sK3)) = k1_relat_1(sK4) | sK3 = k1_xboole_0 ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_20739,c_34]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_20768,plain,
% 6.90/1.50      ( k1_relat_1(sK4) = sK3 | sK3 = k1_xboole_0 ),
% 6.90/1.50      inference(demodulation,[status(thm)],[c_20760,c_34]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_21846,plain,
% 6.90/1.50      ( ~ v1_xboole_0(sK3) | k1_relat_1(sK4) = sK3 ),
% 6.90/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_21836]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_21849,plain,
% 6.90/1.50      ( k1_relat_1(sK4) = sK3 ),
% 6.90/1.50      inference(global_propositional_subsumption,
% 6.90/1.50                [status(thm)],
% 6.90/1.50                [c_21836,c_6,c_7795,c_20768,c_21846]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_69,plain,
% 6.90/1.50      ( ~ v1_funct_2(X0,X1,X1)
% 6.90/1.50      | ~ v3_funct_2(X0,X1,X1)
% 6.90/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 6.90/1.50      | ~ v1_funct_1(X0)
% 6.90/1.50      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 6.90/1.50      inference(cnf_transformation,[],[f187]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4792,plain,
% 6.90/1.50      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 6.90/1.50      | v1_funct_2(X1,X0,X0) != iProver_top
% 6.90/1.50      | v3_funct_2(X1,X0,X0) != iProver_top
% 6.90/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 6.90/1.50      | v1_funct_1(X1) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_12052,plain,
% 6.90/1.50      ( k2_funct_2(sK3,sK4) = k2_funct_1(sK4)
% 6.90/1.50      | v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4788,c_4792]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_5566,plain,
% 6.90/1.50      ( ~ v1_funct_2(sK4,X0,X0)
% 6.90/1.50      | ~ v3_funct_2(sK4,X0,X0)
% 6.90/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 6.90/1.50      | ~ v1_funct_1(sK4)
% 6.90/1.50      | k2_funct_2(X0,sK4) = k2_funct_1(sK4) ),
% 6.90/1.50      inference(instantiation,[status(thm)],[c_69]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_5843,plain,
% 6.90/1.50      ( ~ v1_funct_2(sK4,sK3,sK3)
% 6.90/1.50      | ~ v3_funct_2(sK4,sK3,sK3)
% 6.90/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 6.90/1.50      | ~ v1_funct_1(sK4)
% 6.90/1.50      | k2_funct_2(sK3,sK4) = k2_funct_1(sK4) ),
% 6.90/1.50      inference(instantiation,[status(thm)],[c_5566]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_12430,plain,
% 6.90/1.50      ( k2_funct_2(sK3,sK4) = k2_funct_1(sK4) ),
% 6.90/1.50      inference(global_propositional_subsumption,
% 6.90/1.50                [status(thm)],
% 6.90/1.50                [c_12052,c_76,c_75,c_74,c_73,c_5843]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_63,plain,
% 6.90/1.50      ( ~ v1_funct_2(X0,X1,X1)
% 6.90/1.50      | ~ v3_funct_2(X0,X1,X1)
% 6.90/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 6.90/1.50      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 6.90/1.50      | ~ v1_funct_1(X0) ),
% 6.90/1.50      inference(cnf_transformation,[],[f184]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4798,plain,
% 6.90/1.50      ( v1_funct_2(X0,X1,X1) != iProver_top
% 6.90/1.50      | v3_funct_2(X0,X1,X1) != iProver_top
% 6.90/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 6.90/1.50      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 6.90/1.50      | v1_funct_1(X0) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_15527,plain,
% 6.90/1.50      ( v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top
% 6.90/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_12430,c_4798]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_78,plain,
% 6.90/1.50      ( v1_funct_2(sK4,sK3,sK3) = iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_16635,plain,
% 6.90/1.50      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) = iProver_top ),
% 6.90/1.50      inference(global_propositional_subsumption,
% 6.90/1.50                [status(thm)],
% 6.90/1.50                [c_15527,c_77,c_78,c_79,c_80]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_68,plain,
% 6.90/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.90/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 6.90/1.50      | ~ v1_funct_1(X0)
% 6.90/1.50      | ~ v1_funct_1(X3)
% 6.90/1.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 6.90/1.50      inference(cnf_transformation,[],[f186]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4793,plain,
% 6.90/1.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 6.90/1.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 6.90/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.90/1.50      | v1_funct_1(X5) != iProver_top
% 6.90/1.50      | v1_funct_1(X4) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_16660,plain,
% 6.90/1.50      ( k1_partfun1(X0,X1,sK3,sK3,X2,k2_funct_1(sK4)) = k5_relat_1(X2,k2_funct_1(sK4))
% 6.90/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.90/1.50      | v1_funct_1(X2) != iProver_top
% 6.90/1.50      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_16635,c_4793]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_66,plain,
% 6.90/1.50      ( ~ v1_funct_2(X0,X1,X1)
% 6.90/1.50      | ~ v3_funct_2(X0,X1,X1)
% 6.90/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 6.90/1.50      | ~ v1_funct_1(X0)
% 6.90/1.50      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 6.90/1.50      inference(cnf_transformation,[],[f181]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4795,plain,
% 6.90/1.50      ( v1_funct_2(X0,X1,X1) != iProver_top
% 6.90/1.50      | v3_funct_2(X0,X1,X1) != iProver_top
% 6.90/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 6.90/1.50      | v1_funct_1(X0) != iProver_top
% 6.90/1.50      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_13172,plain,
% 6.90/1.50      ( v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | v1_funct_1(k2_funct_2(sK3,sK4)) = iProver_top
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4788,c_4795]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_13189,plain,
% 6.90/1.50      ( v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(light_normalisation,[status(thm)],[c_13172,c_12430]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_19691,plain,
% 6.90/1.50      ( v1_funct_1(X2) != iProver_top
% 6.90/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.90/1.50      | k1_partfun1(X0,X1,sK3,sK3,X2,k2_funct_1(sK4)) = k5_relat_1(X2,k2_funct_1(sK4)) ),
% 6.90/1.50      inference(global_propositional_subsumption,
% 6.90/1.50                [status(thm)],
% 6.90/1.50                [c_16660,c_77,c_78,c_79,c_13189]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_19692,plain,
% 6.90/1.50      ( k1_partfun1(X0,X1,sK3,sK3,X2,k2_funct_1(sK4)) = k5_relat_1(X2,k2_funct_1(sK4))
% 6.90/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.90/1.50      | v1_funct_1(X2) != iProver_top ),
% 6.90/1.50      inference(renaming,[status(thm)],[c_19691]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_19704,plain,
% 6.90/1.50      ( k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)) = k5_relat_1(sK4,k2_funct_1(sK4))
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4788,c_19692]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_19733,plain,
% 6.90/1.50      ( k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4))
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(light_normalisation,[status(thm)],[c_19704,c_15386]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_19828,plain,
% 6.90/1.50      ( k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)) = k6_partfun1(k1_relat_1(sK4)) ),
% 6.90/1.50      inference(global_propositional_subsumption,[status(thm)],[c_19733,c_77]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_12634,plain,
% 6.90/1.50      ( k1_partfun1(X0,X1,sK3,sK3,X2,sK4) = k5_relat_1(X2,sK4)
% 6.90/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.90/1.50      | v1_funct_1(X2) != iProver_top
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4788,c_4793]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_12904,plain,
% 6.90/1.50      ( v1_funct_1(X2) != iProver_top
% 6.90/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.90/1.50      | k1_partfun1(X0,X1,sK3,sK3,X2,sK4) = k5_relat_1(X2,sK4) ),
% 6.90/1.50      inference(global_propositional_subsumption,[status(thm)],[c_12634,c_77]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_12905,plain,
% 6.90/1.50      ( k1_partfun1(X0,X1,sK3,sK3,X2,sK4) = k5_relat_1(X2,sK4)
% 6.90/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.90/1.50      | v1_funct_1(X2) != iProver_top ),
% 6.90/1.50      inference(renaming,[status(thm)],[c_12904]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_15541,plain,
% 6.90/1.50      ( k1_partfun1(X0,X0,sK3,sK3,k2_funct_2(X0,X1),sK4) = k5_relat_1(k2_funct_2(X0,X1),sK4)
% 6.90/1.50      | v1_funct_2(X1,X0,X0) != iProver_top
% 6.90/1.50      | v3_funct_2(X1,X0,X0) != iProver_top
% 6.90/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 6.90/1.50      | v1_funct_1(X1) != iProver_top
% 6.90/1.50      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4798,c_12905]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_17081,plain,
% 6.90/1.50      ( k1_partfun1(X0,X0,sK3,sK3,k2_funct_2(X0,X1),sK4) = k5_relat_1(k2_funct_2(X0,X1),sK4)
% 6.90/1.50      | v1_funct_2(X1,X0,X0) != iProver_top
% 6.90/1.50      | v3_funct_2(X1,X0,X0) != iProver_top
% 6.90/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 6.90/1.50      | v1_funct_1(X1) != iProver_top ),
% 6.90/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_15541,c_4795]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_17089,plain,
% 6.90/1.50      ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4) = k5_relat_1(k2_funct_2(sK3,sK4),sK4)
% 6.90/1.50      | v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4788,c_17081]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_38,plain,
% 6.90/1.50      ( ~ v2_funct_1(X0)
% 6.90/1.50      | ~ v1_funct_1(X0)
% 6.90/1.50      | ~ v1_relat_1(X0)
% 6.90/1.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 6.90/1.50      inference(cnf_transformation,[],[f200]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4816,plain,
% 6.90/1.50      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 6.90/1.50      | v2_funct_1(X0) != iProver_top
% 6.90/1.50      | v1_funct_1(X0) != iProver_top
% 6.90/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_15276,plain,
% 6.90/1.50      ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_partfun1(k2_relat_1(sK4))
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top
% 6.90/1.50      | v1_relat_1(sK4) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_15271,c_4816]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_15287,plain,
% 6.90/1.50      ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_partfun1(sK3)
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top
% 6.90/1.50      | v1_relat_1(sK4) != iProver_top ),
% 6.90/1.50      inference(light_normalisation,[status(thm)],[c_15276,c_8433]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_5381,plain,
% 6.90/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top
% 6.90/1.50      | v1_relat_1(sK4) = iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_5380]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_15340,plain,
% 6.90/1.50      ( k5_relat_1(k2_funct_1(sK4),sK4) = k6_partfun1(sK3) ),
% 6.90/1.50      inference(global_propositional_subsumption,
% 6.90/1.50                [status(thm)],
% 6.90/1.50                [c_15287,c_77,c_80,c_5381]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_17126,plain,
% 6.90/1.50      ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k6_partfun1(sK3)
% 6.90/1.50      | v1_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | v3_funct_2(sK4,sK3,sK3) != iProver_top
% 6.90/1.50      | v1_funct_1(sK4) != iProver_top ),
% 6.90/1.50      inference(light_normalisation,[status(thm)],[c_17089,c_12430,c_15340]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_16651,plain,
% 6.90/1.50      ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k5_relat_1(k2_funct_1(sK4),sK4)
% 6.90/1.50      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_16635,c_12905]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_16724,plain,
% 6.90/1.50      ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k6_partfun1(sK3)
% 6.90/1.50      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 6.90/1.50      inference(light_normalisation,[status(thm)],[c_16651,c_15340]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_17198,plain,
% 6.90/1.50      ( k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4) = k6_partfun1(sK3) ),
% 6.90/1.50      inference(global_propositional_subsumption,
% 6.90/1.50                [status(thm)],
% 6.90/1.50                [c_17126,c_77,c_78,c_79,c_13189,c_16724]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_72,negated_conjecture,
% 6.90/1.50      ( ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3))
% 6.90/1.50      | ~ r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) ),
% 6.90/1.50      inference(cnf_transformation,[],[f195]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4789,plain,
% 6.90/1.50      ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_2(sK3,sK4),sK4),k6_partfun1(sK3)) != iProver_top
% 6.90/1.50      | r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_2(sK3,sK4)),k6_partfun1(sK3)) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_12433,plain,
% 6.90/1.50      ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,k2_funct_1(sK4),sK4),k6_partfun1(sK3)) != iProver_top
% 6.90/1.50      | r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)),k6_partfun1(sK3)) != iProver_top ),
% 6.90/1.50      inference(demodulation,[status(thm)],[c_12430,c_4789]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_17201,plain,
% 6.90/1.50      ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)),k6_partfun1(sK3)) != iProver_top
% 6.90/1.50      | r2_relset_1(sK3,sK3,k6_partfun1(sK3),k6_partfun1(sK3)) != iProver_top ),
% 6.90/1.50      inference(demodulation,[status(thm)],[c_17198,c_12433]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_67,plain,
% 6.90/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 6.90/1.50      inference(cnf_transformation,[],[f185]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4794,plain,
% 6.90/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_45,plain,
% 6.90/1.50      ( r2_relset_1(X0,X1,X2,X2)
% 6.90/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 6.90/1.50      inference(cnf_transformation,[],[f204]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_4812,plain,
% 6.90/1.50      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 6.90/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.90/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_11425,plain,
% 6.90/1.50      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 6.90/1.50      inference(superposition,[status(thm)],[c_4794,c_4812]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_17299,plain,
% 6.90/1.50      ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK3,sK3,sK3,sK4,k2_funct_1(sK4)),k6_partfun1(sK3)) != iProver_top ),
% 6.90/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_17201,c_11425]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_19831,plain,
% 6.90/1.50      ( r2_relset_1(sK3,sK3,k6_partfun1(k1_relat_1(sK4)),k6_partfun1(sK3)) != iProver_top ),
% 6.90/1.50      inference(demodulation,[status(thm)],[c_19828,c_17299]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_21853,plain,
% 6.90/1.50      ( r2_relset_1(sK3,sK3,k6_partfun1(sK3),k6_partfun1(sK3)) != iProver_top ),
% 6.90/1.50      inference(demodulation,[status(thm)],[c_21849,c_19831]) ).
% 6.90/1.50  
% 6.90/1.50  cnf(c_22311,plain,
% 6.90/1.50      ( $false ),
% 6.90/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_21853,c_11425]) ).
% 6.90/1.50  
% 6.90/1.50  
% 6.90/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.90/1.50  
% 6.90/1.50  ------                               Statistics
% 6.90/1.50  
% 6.90/1.50  ------ General
% 6.90/1.50  
% 6.90/1.50  abstr_ref_over_cycles:                  0
% 6.90/1.50  abstr_ref_under_cycles:                 0
% 6.90/1.50  gc_basic_clause_elim:                   0
% 6.90/1.50  forced_gc_time:                         0
% 6.90/1.50  parsing_time:                           0.015
% 6.90/1.50  unif_index_cands_time:                  0.
% 6.90/1.50  unif_index_add_time:                    0.
% 6.90/1.50  orderings_time:                         0.
% 6.90/1.50  out_proof_time:                         0.018
% 6.90/1.50  total_time:                             0.55
% 6.90/1.50  num_of_symbols:                         67
% 6.90/1.50  num_of_terms:                           13914
% 6.90/1.50  
% 6.90/1.50  ------ Preprocessing
% 6.90/1.50  
% 6.90/1.50  num_of_splits:                          0
% 6.90/1.50  num_of_split_atoms:                     0
% 6.90/1.50  num_of_reused_defs:                     0
% 6.90/1.50  num_eq_ax_congr_red:                    77
% 6.90/1.50  num_of_sem_filtered_clauses:            1
% 6.90/1.50  num_of_subtypes:                        0
% 6.90/1.50  monotx_restored_types:                  0
% 6.90/1.50  sat_num_of_epr_types:                   0
% 6.90/1.50  sat_num_of_non_cyclic_types:            0
% 6.90/1.50  sat_guarded_non_collapsed_types:        0
% 6.90/1.50  num_pure_diseq_elim:                    0
% 6.90/1.50  simp_replaced_by:                       0
% 6.90/1.50  res_preprocessed:                       332
% 6.90/1.50  prep_upred:                             0
% 6.90/1.50  prep_unflattend:                        96
% 6.90/1.50  smt_new_axioms:                         0
% 6.90/1.50  pred_elim_cands:                        11
% 6.90/1.50  pred_elim:                              4
% 6.90/1.50  pred_elim_cl:                           5
% 6.90/1.50  pred_elim_cycles:                       12
% 6.90/1.50  merged_defs:                            8
% 6.90/1.50  merged_defs_ncl:                        0
% 6.90/1.50  bin_hyper_res:                          10
% 6.90/1.50  prep_cycles:                            4
% 6.90/1.50  pred_elim_time:                         0.04
% 6.90/1.50  splitting_time:                         0.
% 6.90/1.50  sem_filter_time:                        0.
% 6.90/1.50  monotx_time:                            0.001
% 6.90/1.50  subtype_inf_time:                       0.
% 6.90/1.50  
% 6.90/1.50  ------ Problem properties
% 6.90/1.50  
% 6.90/1.50  clauses:                                70
% 6.90/1.50  conjectures:                            5
% 6.90/1.50  epr:                                    16
% 6.90/1.50  horn:                                   60
% 6.90/1.50  ground:                                 6
% 6.90/1.50  unary:                                  12
% 6.90/1.50  binary:                                 26
% 6.90/1.50  lits:                                   189
% 6.90/1.50  lits_eq:                                39
% 6.90/1.50  fd_pure:                                0
% 6.90/1.50  fd_pseudo:                              0
% 6.90/1.50  fd_cond:                                8
% 6.90/1.50  fd_pseudo_cond:                         4
% 6.90/1.50  ac_symbols:                             0
% 6.90/1.50  
% 6.90/1.50  ------ Propositional Solver
% 6.90/1.50  
% 6.90/1.50  prop_solver_calls:                      29
% 6.90/1.50  prop_fast_solver_calls:                 2858
% 6.90/1.50  smt_solver_calls:                       0
% 6.90/1.50  smt_fast_solver_calls:                  0
% 6.90/1.50  prop_num_of_clauses:                    6532
% 6.90/1.50  prop_preprocess_simplified:             18319
% 6.90/1.50  prop_fo_subsumed:                       87
% 6.90/1.50  prop_solver_time:                       0.
% 6.90/1.50  smt_solver_time:                        0.
% 6.90/1.50  smt_fast_solver_time:                   0.
% 6.90/1.50  prop_fast_solver_time:                  0.
% 6.90/1.50  prop_unsat_core_time:                   0.
% 6.90/1.50  
% 6.90/1.50  ------ QBF
% 6.90/1.50  
% 6.90/1.50  qbf_q_res:                              0
% 6.90/1.50  qbf_num_tautologies:                    0
% 6.90/1.50  qbf_prep_cycles:                        0
% 6.90/1.50  
% 6.90/1.50  ------ BMC1
% 6.90/1.50  
% 6.90/1.50  bmc1_current_bound:                     -1
% 6.90/1.50  bmc1_last_solved_bound:                 -1
% 6.90/1.50  bmc1_unsat_core_size:                   -1
% 6.90/1.50  bmc1_unsat_core_parents_size:           -1
% 6.90/1.50  bmc1_merge_next_fun:                    0
% 6.90/1.50  bmc1_unsat_core_clauses_time:           0.
% 6.90/1.50  
% 6.90/1.50  ------ Instantiation
% 6.90/1.50  
% 6.90/1.50  inst_num_of_clauses:                    1557
% 6.90/1.50  inst_num_in_passive:                    797
% 6.90/1.50  inst_num_in_active:                     720
% 6.90/1.50  inst_num_in_unprocessed:                42
% 6.90/1.50  inst_num_of_loops:                      1190
% 6.90/1.50  inst_num_of_learning_restarts:          0
% 6.90/1.50  inst_num_moves_active_passive:          467
% 6.90/1.50  inst_lit_activity:                      0
% 6.90/1.50  inst_lit_activity_moves:                0
% 6.90/1.50  inst_num_tautologies:                   0
% 6.90/1.50  inst_num_prop_implied:                  0
% 6.90/1.50  inst_num_existing_simplified:           0
% 6.90/1.50  inst_num_eq_res_simplified:             0
% 6.90/1.50  inst_num_child_elim:                    0
% 6.90/1.50  inst_num_of_dismatching_blockings:      784
% 6.90/1.50  inst_num_of_non_proper_insts:           1963
% 6.90/1.50  inst_num_of_duplicates:                 0
% 6.90/1.50  inst_inst_num_from_inst_to_res:         0
% 6.90/1.50  inst_dismatching_checking_time:         0.
% 6.90/1.50  
% 6.90/1.50  ------ Resolution
% 6.90/1.50  
% 6.90/1.50  res_num_of_clauses:                     0
% 6.90/1.50  res_num_in_passive:                     0
% 6.90/1.50  res_num_in_active:                      0
% 6.90/1.50  res_num_of_loops:                       336
% 6.90/1.50  res_forward_subset_subsumed:            16
% 6.90/1.50  res_backward_subset_subsumed:           8
% 6.90/1.50  res_forward_subsumed:                   6
% 6.90/1.50  res_backward_subsumed:                  0
% 6.90/1.50  res_forward_subsumption_resolution:     2
% 6.90/1.50  res_backward_subsumption_resolution:    0
% 6.90/1.50  res_clause_to_clause_subsumption:       1808
% 6.90/1.50  res_orphan_elimination:                 0
% 6.90/1.50  res_tautology_del:                      54
% 6.90/1.50  res_num_eq_res_simplified:              0
% 6.90/1.50  res_num_sel_changes:                    0
% 6.90/1.50  res_moves_from_active_to_pass:          0
% 6.90/1.50  
% 6.90/1.50  ------ Superposition
% 6.90/1.50  
% 6.90/1.50  sup_time_total:                         0.
% 6.90/1.50  sup_time_generating:                    0.
% 6.90/1.50  sup_time_sim_full:                      0.
% 6.90/1.50  sup_time_sim_immed:                     0.
% 6.90/1.50  
% 6.90/1.50  sup_num_of_clauses:                     541
% 6.90/1.50  sup_num_in_active:                      222
% 6.90/1.50  sup_num_in_passive:                     319
% 6.90/1.50  sup_num_of_loops:                       237
% 6.90/1.50  sup_fw_superposition:                   426
% 6.90/1.50  sup_bw_superposition:                   226
% 6.90/1.50  sup_immediate_simplified:               133
% 6.90/1.50  sup_given_eliminated:                   1
% 6.90/1.50  comparisons_done:                       0
% 6.90/1.50  comparisons_avoided:                    5
% 6.90/1.50  
% 6.90/1.50  ------ Simplifications
% 6.90/1.50  
% 6.90/1.50  
% 6.90/1.50  sim_fw_subset_subsumed:                 19
% 6.90/1.50  sim_bw_subset_subsumed:                 10
% 6.90/1.50  sim_fw_subsumed:                        11
% 6.90/1.50  sim_bw_subsumed:                        0
% 6.90/1.50  sim_fw_subsumption_res:                 4
% 6.90/1.50  sim_bw_subsumption_res:                 0
% 6.90/1.50  sim_tautology_del:                      14
% 6.90/1.50  sim_eq_tautology_del:                   48
% 6.90/1.50  sim_eq_res_simp:                        0
% 6.90/1.50  sim_fw_demodulated:                     27
% 6.90/1.50  sim_bw_demodulated:                     12
% 6.90/1.50  sim_light_normalised:                   93
% 6.90/1.50  sim_joinable_taut:                      0
% 6.90/1.50  sim_joinable_simp:                      0
% 6.90/1.50  sim_ac_normalised:                      0
% 6.90/1.50  sim_smt_subsumption:                    0
% 6.90/1.50  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:23 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  158 (1197 expanded)
%              Number of clauses        :   95 ( 414 expanded)
%              Number of leaves         :   17 ( 225 expanded)
%              Depth                    :   25
%              Number of atoms          :  509 (6123 expanded)
%              Number of equality atoms :  203 (1196 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f48,plain,
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

fof(f49,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f48])).

fof(f83,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f92,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_749,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_36])).

cnf(c_750,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_749])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_752,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_750,c_35])).

cnf(c_1816,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1819,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4317,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1816,c_1819])).

cnf(c_4339,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_752,c_4317])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1818,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3350,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1816,c_1818])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3362,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3350,c_33])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1821,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2894,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1816,c_1821])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_358,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_359,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_361,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_37])).

cnf(c_1814,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_2963,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2894,c_1814])).

cnf(c_3427,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3362,c_2963])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1817,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3942,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3427,c_1817])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_372,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_373,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_375,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_37])).

cnf(c_1813,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_2964,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2894,c_1813])).

cnf(c_3957,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3942,c_2964])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2116,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2117,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2116])).

cnf(c_2125,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2302,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2125])).

cnf(c_2303,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2302])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3538,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3539,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3538])).

cnf(c_5249,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3957,c_38,c_40,c_2117,c_2303,c_3539])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_760,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_761,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_760])).

cnf(c_773,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_761,c_19])).

cnf(c_1804,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_2970,plain,
    ( k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2963,c_1804])).

cnf(c_3142,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k2_relat_1(sK3) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2970,c_38,c_40,c_2117,c_2303])).

cnf(c_3143,plain,
    ( k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3142])).

cnf(c_3146,plain,
    ( k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3143,c_2964])).

cnf(c_3425,plain,
    ( sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3362,c_3146])).

cnf(c_3436,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3425])).

cnf(c_5262,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5249,c_3436])).

cnf(c_5311,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_5262])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1832,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1833,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3209,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1832,c_1833])).

cnf(c_5392,plain,
    ( sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5311,c_3209])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X2),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 != X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_619,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_603,c_29])).

cnf(c_1811,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_3445,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3362,c_1811])).

cnf(c_3675,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3445,c_38,c_40,c_2303])).

cnf(c_5410,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5392,c_3675])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1247,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2272,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1247])).

cnf(c_2274,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2272])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2331,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2333,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2331])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2287,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2592,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2287])).

cnf(c_6298,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5410,c_35,c_3,c_2274,c_2333,c_2592,c_5392])).

cnf(c_6312,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6298,c_5262])).

cnf(c_13,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6321,plain,
    ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6312,c_13])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1829,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6489,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6321,c_1829])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:05:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.14/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/0.99  
% 3.14/0.99  ------  iProver source info
% 3.14/0.99  
% 3.14/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.14/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/0.99  git: non_committed_changes: false
% 3.14/0.99  git: last_make_outside_of_git: false
% 3.14/0.99  
% 3.14/0.99  ------ 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options
% 3.14/0.99  
% 3.14/0.99  --out_options                           all
% 3.14/0.99  --tptp_safe_out                         true
% 3.14/0.99  --problem_path                          ""
% 3.14/0.99  --include_path                          ""
% 3.14/0.99  --clausifier                            res/vclausify_rel
% 3.14/0.99  --clausifier_options                    --mode clausify
% 3.14/0.99  --stdin                                 false
% 3.14/0.99  --stats_out                             all
% 3.14/0.99  
% 3.14/0.99  ------ General Options
% 3.14/0.99  
% 3.14/0.99  --fof                                   false
% 3.14/0.99  --time_out_real                         305.
% 3.14/0.99  --time_out_virtual                      -1.
% 3.14/0.99  --symbol_type_check                     false
% 3.14/0.99  --clausify_out                          false
% 3.14/0.99  --sig_cnt_out                           false
% 3.14/0.99  --trig_cnt_out                          false
% 3.14/0.99  --trig_cnt_out_tolerance                1.
% 3.14/0.99  --trig_cnt_out_sk_spl                   false
% 3.14/0.99  --abstr_cl_out                          false
% 3.14/0.99  
% 3.14/0.99  ------ Global Options
% 3.14/0.99  
% 3.14/0.99  --schedule                              default
% 3.14/0.99  --add_important_lit                     false
% 3.14/0.99  --prop_solver_per_cl                    1000
% 3.14/0.99  --min_unsat_core                        false
% 3.14/0.99  --soft_assumptions                      false
% 3.14/0.99  --soft_lemma_size                       3
% 3.14/0.99  --prop_impl_unit_size                   0
% 3.14/0.99  --prop_impl_unit                        []
% 3.14/0.99  --share_sel_clauses                     true
% 3.14/0.99  --reset_solvers                         false
% 3.14/0.99  --bc_imp_inh                            [conj_cone]
% 3.14/0.99  --conj_cone_tolerance                   3.
% 3.14/0.99  --extra_neg_conj                        none
% 3.14/0.99  --large_theory_mode                     true
% 3.14/0.99  --prolific_symb_bound                   200
% 3.14/0.99  --lt_threshold                          2000
% 3.14/0.99  --clause_weak_htbl                      true
% 3.14/0.99  --gc_record_bc_elim                     false
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing Options
% 3.14/0.99  
% 3.14/0.99  --preprocessing_flag                    true
% 3.14/0.99  --time_out_prep_mult                    0.1
% 3.14/0.99  --splitting_mode                        input
% 3.14/0.99  --splitting_grd                         true
% 3.14/0.99  --splitting_cvd                         false
% 3.14/0.99  --splitting_cvd_svl                     false
% 3.14/0.99  --splitting_nvd                         32
% 3.14/0.99  --sub_typing                            true
% 3.14/0.99  --prep_gs_sim                           true
% 3.14/0.99  --prep_unflatten                        true
% 3.14/0.99  --prep_res_sim                          true
% 3.14/0.99  --prep_upred                            true
% 3.14/0.99  --prep_sem_filter                       exhaustive
% 3.14/0.99  --prep_sem_filter_out                   false
% 3.14/0.99  --pred_elim                             true
% 3.14/0.99  --res_sim_input                         true
% 3.14/0.99  --eq_ax_congr_red                       true
% 3.14/0.99  --pure_diseq_elim                       true
% 3.14/0.99  --brand_transform                       false
% 3.14/0.99  --non_eq_to_eq                          false
% 3.14/0.99  --prep_def_merge                        true
% 3.14/0.99  --prep_def_merge_prop_impl              false
% 3.14/1.00  --prep_def_merge_mbd                    true
% 3.14/1.00  --prep_def_merge_tr_red                 false
% 3.14/1.00  --prep_def_merge_tr_cl                  false
% 3.14/1.00  --smt_preprocessing                     true
% 3.14/1.00  --smt_ac_axioms                         fast
% 3.14/1.00  --preprocessed_out                      false
% 3.14/1.00  --preprocessed_stats                    false
% 3.14/1.00  
% 3.14/1.00  ------ Abstraction refinement Options
% 3.14/1.00  
% 3.14/1.00  --abstr_ref                             []
% 3.14/1.00  --abstr_ref_prep                        false
% 3.14/1.00  --abstr_ref_until_sat                   false
% 3.14/1.00  --abstr_ref_sig_restrict                funpre
% 3.14/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/1.00  --abstr_ref_under                       []
% 3.14/1.00  
% 3.14/1.00  ------ SAT Options
% 3.14/1.00  
% 3.14/1.00  --sat_mode                              false
% 3.14/1.00  --sat_fm_restart_options                ""
% 3.14/1.00  --sat_gr_def                            false
% 3.14/1.00  --sat_epr_types                         true
% 3.14/1.00  --sat_non_cyclic_types                  false
% 3.14/1.00  --sat_finite_models                     false
% 3.14/1.00  --sat_fm_lemmas                         false
% 3.14/1.00  --sat_fm_prep                           false
% 3.14/1.00  --sat_fm_uc_incr                        true
% 3.14/1.00  --sat_out_model                         small
% 3.14/1.00  --sat_out_clauses                       false
% 3.14/1.00  
% 3.14/1.00  ------ QBF Options
% 3.14/1.00  
% 3.14/1.00  --qbf_mode                              false
% 3.14/1.00  --qbf_elim_univ                         false
% 3.14/1.00  --qbf_dom_inst                          none
% 3.14/1.00  --qbf_dom_pre_inst                      false
% 3.14/1.00  --qbf_sk_in                             false
% 3.14/1.00  --qbf_pred_elim                         true
% 3.14/1.00  --qbf_split                             512
% 3.14/1.00  
% 3.14/1.00  ------ BMC1 Options
% 3.14/1.00  
% 3.14/1.00  --bmc1_incremental                      false
% 3.14/1.00  --bmc1_axioms                           reachable_all
% 3.14/1.00  --bmc1_min_bound                        0
% 3.14/1.00  --bmc1_max_bound                        -1
% 3.14/1.00  --bmc1_max_bound_default                -1
% 3.14/1.00  --bmc1_symbol_reachability              true
% 3.14/1.00  --bmc1_property_lemmas                  false
% 3.14/1.00  --bmc1_k_induction                      false
% 3.14/1.00  --bmc1_non_equiv_states                 false
% 3.14/1.00  --bmc1_deadlock                         false
% 3.14/1.00  --bmc1_ucm                              false
% 3.14/1.00  --bmc1_add_unsat_core                   none
% 3.14/1.00  --bmc1_unsat_core_children              false
% 3.14/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/1.00  --bmc1_out_stat                         full
% 3.14/1.00  --bmc1_ground_init                      false
% 3.14/1.00  --bmc1_pre_inst_next_state              false
% 3.14/1.00  --bmc1_pre_inst_state                   false
% 3.14/1.00  --bmc1_pre_inst_reach_state             false
% 3.14/1.00  --bmc1_out_unsat_core                   false
% 3.14/1.00  --bmc1_aig_witness_out                  false
% 3.14/1.00  --bmc1_verbose                          false
% 3.14/1.00  --bmc1_dump_clauses_tptp                false
% 3.14/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.14/1.00  --bmc1_dump_file                        -
% 3.14/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.14/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.14/1.00  --bmc1_ucm_extend_mode                  1
% 3.14/1.00  --bmc1_ucm_init_mode                    2
% 3.14/1.00  --bmc1_ucm_cone_mode                    none
% 3.14/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.14/1.00  --bmc1_ucm_relax_model                  4
% 3.14/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.14/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/1.00  --bmc1_ucm_layered_model                none
% 3.14/1.00  --bmc1_ucm_max_lemma_size               10
% 3.14/1.00  
% 3.14/1.00  ------ AIG Options
% 3.14/1.00  
% 3.14/1.00  --aig_mode                              false
% 3.14/1.00  
% 3.14/1.00  ------ Instantiation Options
% 3.14/1.00  
% 3.14/1.00  --instantiation_flag                    true
% 3.14/1.00  --inst_sos_flag                         false
% 3.14/1.00  --inst_sos_phase                        true
% 3.14/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/1.00  --inst_lit_sel_side                     num_symb
% 3.14/1.00  --inst_solver_per_active                1400
% 3.14/1.00  --inst_solver_calls_frac                1.
% 3.14/1.00  --inst_passive_queue_type               priority_queues
% 3.14/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/1.00  --inst_passive_queues_freq              [25;2]
% 3.14/1.00  --inst_dismatching                      true
% 3.14/1.00  --inst_eager_unprocessed_to_passive     true
% 3.14/1.00  --inst_prop_sim_given                   true
% 3.14/1.00  --inst_prop_sim_new                     false
% 3.14/1.00  --inst_subs_new                         false
% 3.14/1.00  --inst_eq_res_simp                      false
% 3.14/1.00  --inst_subs_given                       false
% 3.14/1.00  --inst_orphan_elimination               true
% 3.14/1.00  --inst_learning_loop_flag               true
% 3.14/1.00  --inst_learning_start                   3000
% 3.14/1.00  --inst_learning_factor                  2
% 3.14/1.00  --inst_start_prop_sim_after_learn       3
% 3.14/1.00  --inst_sel_renew                        solver
% 3.14/1.00  --inst_lit_activity_flag                true
% 3.14/1.00  --inst_restr_to_given                   false
% 3.14/1.00  --inst_activity_threshold               500
% 3.14/1.00  --inst_out_proof                        true
% 3.14/1.00  
% 3.14/1.00  ------ Resolution Options
% 3.14/1.00  
% 3.14/1.00  --resolution_flag                       true
% 3.14/1.00  --res_lit_sel                           adaptive
% 3.14/1.00  --res_lit_sel_side                      none
% 3.14/1.00  --res_ordering                          kbo
% 3.14/1.00  --res_to_prop_solver                    active
% 3.14/1.00  --res_prop_simpl_new                    false
% 3.14/1.00  --res_prop_simpl_given                  true
% 3.14/1.00  --res_passive_queue_type                priority_queues
% 3.14/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/1.00  --res_passive_queues_freq               [15;5]
% 3.14/1.00  --res_forward_subs                      full
% 3.14/1.00  --res_backward_subs                     full
% 3.14/1.00  --res_forward_subs_resolution           true
% 3.14/1.00  --res_backward_subs_resolution          true
% 3.14/1.00  --res_orphan_elimination                true
% 3.14/1.00  --res_time_limit                        2.
% 3.14/1.00  --res_out_proof                         true
% 3.14/1.00  
% 3.14/1.00  ------ Superposition Options
% 3.14/1.00  
% 3.14/1.00  --superposition_flag                    true
% 3.14/1.00  --sup_passive_queue_type                priority_queues
% 3.14/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.14/1.00  --demod_completeness_check              fast
% 3.14/1.00  --demod_use_ground                      true
% 3.14/1.00  --sup_to_prop_solver                    passive
% 3.14/1.00  --sup_prop_simpl_new                    true
% 3.14/1.00  --sup_prop_simpl_given                  true
% 3.14/1.00  --sup_fun_splitting                     false
% 3.14/1.00  --sup_smt_interval                      50000
% 3.14/1.00  
% 3.14/1.00  ------ Superposition Simplification Setup
% 3.14/1.00  
% 3.14/1.00  --sup_indices_passive                   []
% 3.14/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.00  --sup_full_bw                           [BwDemod]
% 3.14/1.00  --sup_immed_triv                        [TrivRules]
% 3.14/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.00  --sup_immed_bw_main                     []
% 3.14/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.00  
% 3.14/1.00  ------ Combination Options
% 3.14/1.00  
% 3.14/1.00  --comb_res_mult                         3
% 3.14/1.00  --comb_sup_mult                         2
% 3.14/1.00  --comb_inst_mult                        10
% 3.14/1.00  
% 3.14/1.00  ------ Debug Options
% 3.14/1.00  
% 3.14/1.00  --dbg_backtrace                         false
% 3.14/1.00  --dbg_dump_prop_clauses                 false
% 3.14/1.00  --dbg_dump_prop_clauses_file            -
% 3.14/1.00  --dbg_out_stat                          false
% 3.14/1.00  ------ Parsing...
% 3.14/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/1.00  ------ Proving...
% 3.14/1.00  ------ Problem Properties 
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  clauses                                 38
% 3.14/1.00  conjectures                             3
% 3.14/1.00  EPR                                     7
% 3.14/1.00  Horn                                    32
% 3.14/1.00  unary                                   10
% 3.14/1.00  binary                                  10
% 3.14/1.00  lits                                    99
% 3.14/1.00  lits eq                                 36
% 3.14/1.00  fd_pure                                 0
% 3.14/1.00  fd_pseudo                               0
% 3.14/1.00  fd_cond                                 3
% 3.14/1.00  fd_pseudo_cond                          1
% 3.14/1.00  AC symbols                              0
% 3.14/1.00  
% 3.14/1.00  ------ Schedule dynamic 5 is on 
% 3.14/1.00  
% 3.14/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  ------ 
% 3.14/1.00  Current options:
% 3.14/1.00  ------ 
% 3.14/1.00  
% 3.14/1.00  ------ Input Options
% 3.14/1.00  
% 3.14/1.00  --out_options                           all
% 3.14/1.00  --tptp_safe_out                         true
% 3.14/1.00  --problem_path                          ""
% 3.14/1.00  --include_path                          ""
% 3.14/1.00  --clausifier                            res/vclausify_rel
% 3.14/1.00  --clausifier_options                    --mode clausify
% 3.14/1.00  --stdin                                 false
% 3.14/1.00  --stats_out                             all
% 3.14/1.00  
% 3.14/1.00  ------ General Options
% 3.14/1.00  
% 3.14/1.00  --fof                                   false
% 3.14/1.00  --time_out_real                         305.
% 3.14/1.00  --time_out_virtual                      -1.
% 3.14/1.00  --symbol_type_check                     false
% 3.14/1.00  --clausify_out                          false
% 3.14/1.00  --sig_cnt_out                           false
% 3.14/1.00  --trig_cnt_out                          false
% 3.14/1.00  --trig_cnt_out_tolerance                1.
% 3.14/1.00  --trig_cnt_out_sk_spl                   false
% 3.14/1.00  --abstr_cl_out                          false
% 3.14/1.00  
% 3.14/1.00  ------ Global Options
% 3.14/1.00  
% 3.14/1.00  --schedule                              default
% 3.14/1.00  --add_important_lit                     false
% 3.14/1.00  --prop_solver_per_cl                    1000
% 3.14/1.00  --min_unsat_core                        false
% 3.14/1.00  --soft_assumptions                      false
% 3.14/1.00  --soft_lemma_size                       3
% 3.14/1.00  --prop_impl_unit_size                   0
% 3.14/1.00  --prop_impl_unit                        []
% 3.14/1.00  --share_sel_clauses                     true
% 3.14/1.00  --reset_solvers                         false
% 3.14/1.00  --bc_imp_inh                            [conj_cone]
% 3.14/1.00  --conj_cone_tolerance                   3.
% 3.14/1.00  --extra_neg_conj                        none
% 3.14/1.00  --large_theory_mode                     true
% 3.14/1.00  --prolific_symb_bound                   200
% 3.14/1.00  --lt_threshold                          2000
% 3.14/1.00  --clause_weak_htbl                      true
% 3.14/1.00  --gc_record_bc_elim                     false
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing Options
% 3.14/1.00  
% 3.14/1.00  --preprocessing_flag                    true
% 3.14/1.00  --time_out_prep_mult                    0.1
% 3.14/1.00  --splitting_mode                        input
% 3.14/1.00  --splitting_grd                         true
% 3.14/1.00  --splitting_cvd                         false
% 3.14/1.00  --splitting_cvd_svl                     false
% 3.14/1.00  --splitting_nvd                         32
% 3.14/1.00  --sub_typing                            true
% 3.14/1.00  --prep_gs_sim                           true
% 3.14/1.00  --prep_unflatten                        true
% 3.14/1.00  --prep_res_sim                          true
% 3.14/1.00  --prep_upred                            true
% 3.14/1.00  --prep_sem_filter                       exhaustive
% 3.14/1.00  --prep_sem_filter_out                   false
% 3.14/1.00  --pred_elim                             true
% 3.14/1.00  --res_sim_input                         true
% 3.14/1.00  --eq_ax_congr_red                       true
% 3.14/1.00  --pure_diseq_elim                       true
% 3.14/1.00  --brand_transform                       false
% 3.14/1.00  --non_eq_to_eq                          false
% 3.14/1.00  --prep_def_merge                        true
% 3.14/1.00  --prep_def_merge_prop_impl              false
% 3.14/1.00  --prep_def_merge_mbd                    true
% 3.14/1.00  --prep_def_merge_tr_red                 false
% 3.14/1.00  --prep_def_merge_tr_cl                  false
% 3.14/1.00  --smt_preprocessing                     true
% 3.14/1.00  --smt_ac_axioms                         fast
% 3.14/1.00  --preprocessed_out                      false
% 3.14/1.00  --preprocessed_stats                    false
% 3.14/1.00  
% 3.14/1.00  ------ Abstraction refinement Options
% 3.14/1.00  
% 3.14/1.00  --abstr_ref                             []
% 3.14/1.00  --abstr_ref_prep                        false
% 3.14/1.00  --abstr_ref_until_sat                   false
% 3.14/1.00  --abstr_ref_sig_restrict                funpre
% 3.14/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/1.00  --abstr_ref_under                       []
% 3.14/1.00  
% 3.14/1.00  ------ SAT Options
% 3.14/1.00  
% 3.14/1.00  --sat_mode                              false
% 3.14/1.00  --sat_fm_restart_options                ""
% 3.14/1.00  --sat_gr_def                            false
% 3.14/1.00  --sat_epr_types                         true
% 3.14/1.00  --sat_non_cyclic_types                  false
% 3.14/1.00  --sat_finite_models                     false
% 3.14/1.00  --sat_fm_lemmas                         false
% 3.14/1.00  --sat_fm_prep                           false
% 3.14/1.00  --sat_fm_uc_incr                        true
% 3.14/1.00  --sat_out_model                         small
% 3.14/1.00  --sat_out_clauses                       false
% 3.14/1.00  
% 3.14/1.00  ------ QBF Options
% 3.14/1.00  
% 3.14/1.00  --qbf_mode                              false
% 3.14/1.00  --qbf_elim_univ                         false
% 3.14/1.00  --qbf_dom_inst                          none
% 3.14/1.00  --qbf_dom_pre_inst                      false
% 3.14/1.00  --qbf_sk_in                             false
% 3.14/1.00  --qbf_pred_elim                         true
% 3.14/1.00  --qbf_split                             512
% 3.14/1.00  
% 3.14/1.00  ------ BMC1 Options
% 3.14/1.00  
% 3.14/1.00  --bmc1_incremental                      false
% 3.14/1.00  --bmc1_axioms                           reachable_all
% 3.14/1.00  --bmc1_min_bound                        0
% 3.14/1.00  --bmc1_max_bound                        -1
% 3.14/1.00  --bmc1_max_bound_default                -1
% 3.14/1.00  --bmc1_symbol_reachability              true
% 3.14/1.00  --bmc1_property_lemmas                  false
% 3.14/1.00  --bmc1_k_induction                      false
% 3.14/1.00  --bmc1_non_equiv_states                 false
% 3.14/1.00  --bmc1_deadlock                         false
% 3.14/1.00  --bmc1_ucm                              false
% 3.14/1.00  --bmc1_add_unsat_core                   none
% 3.14/1.00  --bmc1_unsat_core_children              false
% 3.14/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/1.00  --bmc1_out_stat                         full
% 3.14/1.00  --bmc1_ground_init                      false
% 3.14/1.00  --bmc1_pre_inst_next_state              false
% 3.14/1.00  --bmc1_pre_inst_state                   false
% 3.14/1.00  --bmc1_pre_inst_reach_state             false
% 3.14/1.00  --bmc1_out_unsat_core                   false
% 3.14/1.00  --bmc1_aig_witness_out                  false
% 3.14/1.00  --bmc1_verbose                          false
% 3.14/1.00  --bmc1_dump_clauses_tptp                false
% 3.14/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.14/1.00  --bmc1_dump_file                        -
% 3.14/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.14/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.14/1.00  --bmc1_ucm_extend_mode                  1
% 3.14/1.00  --bmc1_ucm_init_mode                    2
% 3.14/1.00  --bmc1_ucm_cone_mode                    none
% 3.14/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.14/1.00  --bmc1_ucm_relax_model                  4
% 3.14/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.14/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/1.00  --bmc1_ucm_layered_model                none
% 3.14/1.00  --bmc1_ucm_max_lemma_size               10
% 3.14/1.00  
% 3.14/1.00  ------ AIG Options
% 3.14/1.00  
% 3.14/1.00  --aig_mode                              false
% 3.14/1.00  
% 3.14/1.00  ------ Instantiation Options
% 3.14/1.00  
% 3.14/1.00  --instantiation_flag                    true
% 3.14/1.00  --inst_sos_flag                         false
% 3.14/1.00  --inst_sos_phase                        true
% 3.14/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/1.00  --inst_lit_sel_side                     none
% 3.14/1.00  --inst_solver_per_active                1400
% 3.14/1.00  --inst_solver_calls_frac                1.
% 3.14/1.00  --inst_passive_queue_type               priority_queues
% 3.14/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/1.00  --inst_passive_queues_freq              [25;2]
% 3.14/1.00  --inst_dismatching                      true
% 3.14/1.00  --inst_eager_unprocessed_to_passive     true
% 3.14/1.00  --inst_prop_sim_given                   true
% 3.14/1.00  --inst_prop_sim_new                     false
% 3.14/1.00  --inst_subs_new                         false
% 3.14/1.00  --inst_eq_res_simp                      false
% 3.14/1.00  --inst_subs_given                       false
% 3.14/1.00  --inst_orphan_elimination               true
% 3.14/1.00  --inst_learning_loop_flag               true
% 3.14/1.00  --inst_learning_start                   3000
% 3.14/1.00  --inst_learning_factor                  2
% 3.14/1.00  --inst_start_prop_sim_after_learn       3
% 3.14/1.00  --inst_sel_renew                        solver
% 3.14/1.00  --inst_lit_activity_flag                true
% 3.14/1.00  --inst_restr_to_given                   false
% 3.14/1.00  --inst_activity_threshold               500
% 3.14/1.00  --inst_out_proof                        true
% 3.14/1.00  
% 3.14/1.00  ------ Resolution Options
% 3.14/1.00  
% 3.14/1.00  --resolution_flag                       false
% 3.14/1.00  --res_lit_sel                           adaptive
% 3.14/1.00  --res_lit_sel_side                      none
% 3.14/1.00  --res_ordering                          kbo
% 3.14/1.00  --res_to_prop_solver                    active
% 3.14/1.00  --res_prop_simpl_new                    false
% 3.14/1.00  --res_prop_simpl_given                  true
% 3.14/1.00  --res_passive_queue_type                priority_queues
% 3.14/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/1.00  --res_passive_queues_freq               [15;5]
% 3.14/1.00  --res_forward_subs                      full
% 3.14/1.00  --res_backward_subs                     full
% 3.14/1.00  --res_forward_subs_resolution           true
% 3.14/1.00  --res_backward_subs_resolution          true
% 3.14/1.00  --res_orphan_elimination                true
% 3.14/1.00  --res_time_limit                        2.
% 3.14/1.00  --res_out_proof                         true
% 3.14/1.00  
% 3.14/1.00  ------ Superposition Options
% 3.14/1.00  
% 3.14/1.00  --superposition_flag                    true
% 3.14/1.00  --sup_passive_queue_type                priority_queues
% 3.14/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.14/1.00  --demod_completeness_check              fast
% 3.14/1.00  --demod_use_ground                      true
% 3.14/1.00  --sup_to_prop_solver                    passive
% 3.14/1.00  --sup_prop_simpl_new                    true
% 3.14/1.00  --sup_prop_simpl_given                  true
% 3.14/1.00  --sup_fun_splitting                     false
% 3.14/1.00  --sup_smt_interval                      50000
% 3.14/1.00  
% 3.14/1.00  ------ Superposition Simplification Setup
% 3.14/1.00  
% 3.14/1.00  --sup_indices_passive                   []
% 3.14/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.00  --sup_full_bw                           [BwDemod]
% 3.14/1.00  --sup_immed_triv                        [TrivRules]
% 3.14/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.00  --sup_immed_bw_main                     []
% 3.14/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.00  
% 3.14/1.00  ------ Combination Options
% 3.14/1.00  
% 3.14/1.00  --comb_res_mult                         3
% 3.14/1.00  --comb_sup_mult                         2
% 3.14/1.00  --comb_inst_mult                        10
% 3.14/1.00  
% 3.14/1.00  ------ Debug Options
% 3.14/1.00  
% 3.14/1.00  --dbg_backtrace                         false
% 3.14/1.00  --dbg_dump_prop_clauses                 false
% 3.14/1.00  --dbg_dump_prop_clauses_file            -
% 3.14/1.00  --dbg_out_stat                          false
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  ------ Proving...
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  % SZS status Theorem for theBenchmark.p
% 3.14/1.00  
% 3.14/1.00   Resolution empty clause
% 3.14/1.00  
% 3.14/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/1.00  
% 3.14/1.00  fof(f17,axiom,(
% 3.14/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f35,plain,(
% 3.14/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.00    inference(ennf_transformation,[],[f17])).
% 3.14/1.00  
% 3.14/1.00  fof(f36,plain,(
% 3.14/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.00    inference(flattening,[],[f35])).
% 3.14/1.00  
% 3.14/1.00  fof(f47,plain,(
% 3.14/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.00    inference(nnf_transformation,[],[f36])).
% 3.14/1.00  
% 3.14/1.00  fof(f73,plain,(
% 3.14/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.00    inference(cnf_transformation,[],[f47])).
% 3.14/1.00  
% 3.14/1.00  fof(f19,conjecture,(
% 3.14/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f20,negated_conjecture,(
% 3.14/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.14/1.00    inference(negated_conjecture,[],[f19])).
% 3.14/1.00  
% 3.14/1.00  fof(f39,plain,(
% 3.14/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.14/1.00    inference(ennf_transformation,[],[f20])).
% 3.14/1.00  
% 3.14/1.00  fof(f40,plain,(
% 3.14/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.14/1.00    inference(flattening,[],[f39])).
% 3.14/1.00  
% 3.14/1.00  fof(f48,plain,(
% 3.14/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.14/1.00    introduced(choice_axiom,[])).
% 3.14/1.00  
% 3.14/1.00  fof(f49,plain,(
% 3.14/1.00    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.14/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f48])).
% 3.14/1.00  
% 3.14/1.00  fof(f83,plain,(
% 3.14/1.00    v1_funct_2(sK3,sK1,sK2)),
% 3.14/1.00    inference(cnf_transformation,[],[f49])).
% 3.14/1.00  
% 3.14/1.00  fof(f84,plain,(
% 3.14/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.14/1.00    inference(cnf_transformation,[],[f49])).
% 3.14/1.00  
% 3.14/1.00  fof(f15,axiom,(
% 3.14/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f33,plain,(
% 3.14/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.00    inference(ennf_transformation,[],[f15])).
% 3.14/1.00  
% 3.14/1.00  fof(f71,plain,(
% 3.14/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.00    inference(cnf_transformation,[],[f33])).
% 3.14/1.00  
% 3.14/1.00  fof(f16,axiom,(
% 3.14/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f34,plain,(
% 3.14/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.00    inference(ennf_transformation,[],[f16])).
% 3.14/1.00  
% 3.14/1.00  fof(f72,plain,(
% 3.14/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.00    inference(cnf_transformation,[],[f34])).
% 3.14/1.00  
% 3.14/1.00  fof(f86,plain,(
% 3.14/1.00    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.14/1.00    inference(cnf_transformation,[],[f49])).
% 3.14/1.00  
% 3.14/1.00  fof(f13,axiom,(
% 3.14/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f31,plain,(
% 3.14/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.00    inference(ennf_transformation,[],[f13])).
% 3.14/1.00  
% 3.14/1.00  fof(f69,plain,(
% 3.14/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.00    inference(cnf_transformation,[],[f31])).
% 3.14/1.00  
% 3.14/1.00  fof(f12,axiom,(
% 3.14/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f29,plain,(
% 3.14/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.14/1.00    inference(ennf_transformation,[],[f12])).
% 3.14/1.00  
% 3.14/1.00  fof(f30,plain,(
% 3.14/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/1.00    inference(flattening,[],[f29])).
% 3.14/1.00  
% 3.14/1.00  fof(f67,plain,(
% 3.14/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f30])).
% 3.14/1.00  
% 3.14/1.00  fof(f85,plain,(
% 3.14/1.00    v2_funct_1(sK3)),
% 3.14/1.00    inference(cnf_transformation,[],[f49])).
% 3.14/1.00  
% 3.14/1.00  fof(f82,plain,(
% 3.14/1.00    v1_funct_1(sK3)),
% 3.14/1.00    inference(cnf_transformation,[],[f49])).
% 3.14/1.00  
% 3.14/1.00  fof(f18,axiom,(
% 3.14/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f37,plain,(
% 3.14/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.14/1.00    inference(ennf_transformation,[],[f18])).
% 3.14/1.00  
% 3.14/1.00  fof(f38,plain,(
% 3.14/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.14/1.00    inference(flattening,[],[f37])).
% 3.14/1.00  
% 3.14/1.00  fof(f81,plain,(
% 3.14/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f38])).
% 3.14/1.00  
% 3.14/1.00  fof(f68,plain,(
% 3.14/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f30])).
% 3.14/1.00  
% 3.14/1.00  fof(f11,axiom,(
% 3.14/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f27,plain,(
% 3.14/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.14/1.00    inference(ennf_transformation,[],[f11])).
% 3.14/1.00  
% 3.14/1.00  fof(f28,plain,(
% 3.14/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/1.00    inference(flattening,[],[f27])).
% 3.14/1.00  
% 3.14/1.00  fof(f66,plain,(
% 3.14/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f28])).
% 3.14/1.00  
% 3.14/1.00  fof(f65,plain,(
% 3.14/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f28])).
% 3.14/1.00  
% 3.14/1.00  fof(f80,plain,(
% 3.14/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f38])).
% 3.14/1.00  
% 3.14/1.00  fof(f87,plain,(
% 3.14/1.00    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.14/1.00    inference(cnf_transformation,[],[f49])).
% 3.14/1.00  
% 3.14/1.00  fof(f1,axiom,(
% 3.14/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f21,plain,(
% 3.14/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.14/1.00    inference(ennf_transformation,[],[f1])).
% 3.14/1.00  
% 3.14/1.00  fof(f41,plain,(
% 3.14/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.14/1.00    inference(nnf_transformation,[],[f21])).
% 3.14/1.00  
% 3.14/1.00  fof(f42,plain,(
% 3.14/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.14/1.00    inference(rectify,[],[f41])).
% 3.14/1.00  
% 3.14/1.00  fof(f43,plain,(
% 3.14/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.14/1.00    introduced(choice_axiom,[])).
% 3.14/1.00  
% 3.14/1.00  fof(f44,plain,(
% 3.14/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.14/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 3.14/1.00  
% 3.14/1.00  fof(f51,plain,(
% 3.14/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f44])).
% 3.14/1.00  
% 3.14/1.00  fof(f52,plain,(
% 3.14/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f44])).
% 3.14/1.00  
% 3.14/1.00  fof(f77,plain,(
% 3.14/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.00    inference(cnf_transformation,[],[f47])).
% 3.14/1.00  
% 3.14/1.00  fof(f92,plain,(
% 3.14/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.14/1.00    inference(equality_resolution,[],[f77])).
% 3.14/1.00  
% 3.14/1.00  fof(f2,axiom,(
% 3.14/1.00    v1_xboole_0(k1_xboole_0)),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f53,plain,(
% 3.14/1.00    v1_xboole_0(k1_xboole_0)),
% 3.14/1.00    inference(cnf_transformation,[],[f2])).
% 3.14/1.00  
% 3.14/1.00  fof(f4,axiom,(
% 3.14/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f22,plain,(
% 3.14/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.14/1.00    inference(ennf_transformation,[],[f4])).
% 3.14/1.00  
% 3.14/1.00  fof(f55,plain,(
% 3.14/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f22])).
% 3.14/1.00  
% 3.14/1.00  fof(f14,axiom,(
% 3.14/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f32,plain,(
% 3.14/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.14/1.00    inference(ennf_transformation,[],[f14])).
% 3.14/1.00  
% 3.14/1.00  fof(f70,plain,(
% 3.14/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f32])).
% 3.14/1.00  
% 3.14/1.00  fof(f9,axiom,(
% 3.14/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f62,plain,(
% 3.14/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.14/1.00    inference(cnf_transformation,[],[f9])).
% 3.14/1.00  
% 3.14/1.00  fof(f3,axiom,(
% 3.14/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f54,plain,(
% 3.14/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f3])).
% 3.14/1.00  
% 3.14/1.00  cnf(c_28,plain,
% 3.14/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.14/1.00      | k1_xboole_0 = X2 ),
% 3.14/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_36,negated_conjecture,
% 3.14/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.14/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_749,plain,
% 3.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.14/1.00      | sK1 != X1
% 3.14/1.00      | sK2 != X2
% 3.14/1.00      | sK3 != X0
% 3.14/1.00      | k1_xboole_0 = X2 ),
% 3.14/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_36]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_750,plain,
% 3.14/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.14/1.00      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.14/1.00      | k1_xboole_0 = sK2 ),
% 3.14/1.00      inference(unflattening,[status(thm)],[c_749]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_35,negated_conjecture,
% 3.14/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.14/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_752,plain,
% 3.14/1.00      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.14/1.00      inference(global_propositional_subsumption,[status(thm)],[c_750,c_35]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1816,plain,
% 3.14/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_21,plain,
% 3.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1819,plain,
% 3.14/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.14/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_4317,plain,
% 3.14/1.00      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_1816,c_1819]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_4339,plain,
% 3.14/1.00      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_752,c_4317]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_22,plain,
% 3.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1818,plain,
% 3.14/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.14/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3350,plain,
% 3.14/1.00      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_1816,c_1818]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_33,negated_conjecture,
% 3.14/1.00      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.14/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3362,plain,
% 3.14/1.00      ( k2_relat_1(sK3) = sK2 ),
% 3.14/1.00      inference(light_normalisation,[status(thm)],[c_3350,c_33]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_19,plain,
% 3.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1821,plain,
% 3.14/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.14/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2894,plain,
% 3.14/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_1816,c_1821]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_18,plain,
% 3.14/1.00      ( ~ v2_funct_1(X0)
% 3.14/1.00      | ~ v1_funct_1(X0)
% 3.14/1.00      | ~ v1_relat_1(X0)
% 3.14/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_34,negated_conjecture,
% 3.14/1.00      ( v2_funct_1(sK3) ),
% 3.14/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_358,plain,
% 3.14/1.00      ( ~ v1_funct_1(X0)
% 3.14/1.00      | ~ v1_relat_1(X0)
% 3.14/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.14/1.00      | sK3 != X0 ),
% 3.14/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_359,plain,
% 3.14/1.00      ( ~ v1_funct_1(sK3)
% 3.14/1.00      | ~ v1_relat_1(sK3)
% 3.14/1.00      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.14/1.00      inference(unflattening,[status(thm)],[c_358]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_37,negated_conjecture,
% 3.14/1.00      ( v1_funct_1(sK3) ),
% 3.14/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_361,plain,
% 3.14/1.00      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.14/1.00      inference(global_propositional_subsumption,[status(thm)],[c_359,c_37]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1814,plain,
% 3.14/1.00      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.14/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2963,plain,
% 3.14/1.00      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_2894,c_1814]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3427,plain,
% 3.14/1.00      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.14/1.00      inference(demodulation,[status(thm)],[c_3362,c_2963]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_29,plain,
% 3.14/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.14/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.14/1.00      | ~ v1_funct_1(X0)
% 3.14/1.00      | ~ v1_relat_1(X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1817,plain,
% 3.14/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.14/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.14/1.00      | v1_funct_1(X0) != iProver_top
% 3.14/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3942,plain,
% 3.14/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.14/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top
% 3.14/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.14/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_3427,c_1817]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_17,plain,
% 3.14/1.00      ( ~ v2_funct_1(X0)
% 3.14/1.00      | ~ v1_funct_1(X0)
% 3.14/1.00      | ~ v1_relat_1(X0)
% 3.14/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_372,plain,
% 3.14/1.00      ( ~ v1_funct_1(X0)
% 3.14/1.00      | ~ v1_relat_1(X0)
% 3.14/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.14/1.00      | sK3 != X0 ),
% 3.14/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_373,plain,
% 3.14/1.00      ( ~ v1_funct_1(sK3)
% 3.14/1.00      | ~ v1_relat_1(sK3)
% 3.14/1.00      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.14/1.00      inference(unflattening,[status(thm)],[c_372]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_375,plain,
% 3.14/1.00      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.14/1.00      inference(global_propositional_subsumption,[status(thm)],[c_373,c_37]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1813,plain,
% 3.14/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.14/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2964,plain,
% 3.14/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_2894,c_1813]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3957,plain,
% 3.14/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.14/1.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.14/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.14/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.14/1.00      inference(light_normalisation,[status(thm)],[c_3942,c_2964]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_38,plain,
% 3.14/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_40,plain,
% 3.14/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_15,plain,
% 3.14/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2116,plain,
% 3.14/1.00      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2117,plain,
% 3.14/1.00      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.14/1.00      | v1_funct_1(sK3) != iProver_top
% 3.14/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_2116]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2125,plain,
% 3.14/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK3) ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2302,plain,
% 3.14/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.14/1.00      | v1_relat_1(sK3) ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_2125]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2303,plain,
% 3.14/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.14/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_2302]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_16,plain,
% 3.14/1.00      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.14/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3538,plain,
% 3.14/1.00      ( ~ v1_funct_1(sK3) | v1_relat_1(k2_funct_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3539,plain,
% 3.14/1.00      ( v1_funct_1(sK3) != iProver_top
% 3.14/1.00      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 3.14/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_3538]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5249,plain,
% 3.14/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.14/1.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_3957,c_38,c_40,c_2117,c_2303,c_3539]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_30,plain,
% 3.14/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.14/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.14/1.00      | ~ v1_funct_1(X0)
% 3.14/1.00      | ~ v1_relat_1(X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_32,negated_conjecture,
% 3.14/1.00      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.14/1.00      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.14/1.00      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.14/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_760,plain,
% 3.14/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.14/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.14/1.00      | ~ v1_funct_1(X0)
% 3.14/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.14/1.00      | ~ v1_relat_1(X0)
% 3.14/1.00      | k2_funct_1(sK3) != X0
% 3.14/1.00      | k1_relat_1(X0) != sK2
% 3.14/1.00      | sK1 != X1 ),
% 3.14/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_761,plain,
% 3.14/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.14/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 3.14/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.14/1.00      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.14/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.14/1.00      inference(unflattening,[status(thm)],[c_760]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_773,plain,
% 3.14/1.00      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.14/1.00      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
% 3.14/1.00      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.14/1.00      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.14/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_761,c_19]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1804,plain,
% 3.14/1.00      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.14/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.14/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 3.14/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2970,plain,
% 3.14/1.00      ( k2_relat_1(sK3) != sK2
% 3.14/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.14/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 3.14/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.14/1.00      inference(demodulation,[status(thm)],[c_2963,c_1804]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3142,plain,
% 3.14/1.00      ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top
% 3.14/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.14/1.00      | k2_relat_1(sK3) != sK2 ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_2970,c_38,c_40,c_2117,c_2303]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3143,plain,
% 3.14/1.00      ( k2_relat_1(sK3) != sK2
% 3.14/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.14/1.00      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) != iProver_top ),
% 3.14/1.00      inference(renaming,[status(thm)],[c_3142]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3146,plain,
% 3.14/1.00      ( k2_relat_1(sK3) != sK2
% 3.14/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.14/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.14/1.00      inference(light_normalisation,[status(thm)],[c_3143,c_2964]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3425,plain,
% 3.14/1.00      ( sK2 != sK2
% 3.14/1.00      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.14/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.14/1.00      inference(demodulation,[status(thm)],[c_3362,c_3146]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3436,plain,
% 3.14/1.00      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.14/1.00      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.14/1.00      inference(equality_resolution_simp,[status(thm)],[c_3425]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5262,plain,
% 3.14/1.00      ( r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_5249,c_3436]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5311,plain,
% 3.14/1.00      ( sK2 = k1_xboole_0 | r1_tarski(sK1,sK1) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_4339,c_5262]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1,plain,
% 3.14/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.14/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1832,plain,
% 3.14/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.14/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_0,plain,
% 3.14/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.14/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1833,plain,
% 3.14/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.14/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3209,plain,
% 3.14/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_1832,c_1833]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5392,plain,
% 3.14/1.00      ( sK2 = k1_xboole_0 ),
% 3.14/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5311,c_3209]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_24,plain,
% 3.14/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.14/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.14/1.00      | k1_xboole_0 = X1
% 3.14/1.00      | k1_xboole_0 = X0 ),
% 3.14/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_602,plain,
% 3.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.14/1.00      | ~ r1_tarski(k2_relat_1(X2),X3)
% 3.14/1.00      | ~ v1_funct_1(X2)
% 3.14/1.00      | ~ v1_relat_1(X2)
% 3.14/1.00      | X2 != X0
% 3.14/1.00      | k1_relat_1(X2) != X1
% 3.14/1.00      | k1_xboole_0 != X3
% 3.14/1.00      | k1_xboole_0 = X1
% 3.14/1.00      | k1_xboole_0 = X0 ),
% 3.14/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_603,plain,
% 3.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.14/1.00      | ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 3.14/1.00      | ~ v1_funct_1(X0)
% 3.14/1.00      | ~ v1_relat_1(X0)
% 3.14/1.00      | k1_xboole_0 = X0
% 3.14/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.14/1.00      inference(unflattening,[status(thm)],[c_602]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_619,plain,
% 3.14/1.00      ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
% 3.14/1.00      | ~ v1_funct_1(X0)
% 3.14/1.00      | ~ v1_relat_1(X0)
% 3.14/1.00      | k1_xboole_0 = X0
% 3.14/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.14/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_603,c_29]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1811,plain,
% 3.14/1.00      ( k1_xboole_0 = X0
% 3.14/1.00      | k1_xboole_0 = k1_relat_1(X0)
% 3.14/1.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.14/1.00      | v1_funct_1(X0) != iProver_top
% 3.14/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3445,plain,
% 3.14/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.00      | sK3 = k1_xboole_0
% 3.14/1.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.14/1.00      | v1_funct_1(sK3) != iProver_top
% 3.14/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_3362,c_1811]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3675,plain,
% 3.14/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.00      | sK3 = k1_xboole_0
% 3.14/1.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_3445,c_38,c_40,c_2303]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5410,plain,
% 3.14/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.00      | sK3 = k1_xboole_0
% 3.14/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.14/1.00      inference(demodulation,[status(thm)],[c_5392,c_3675]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3,plain,
% 3.14/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1247,plain,
% 3.14/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.14/1.00      theory(equality) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2272,plain,
% 3.14/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_1247]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2274,plain,
% 3.14/1.00      ( v1_xboole_0(sK2) | ~ v1_xboole_0(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_2272]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5,plain,
% 3.14/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.14/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2331,plain,
% 3.14/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK3) | sK3 = X0 ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2333,plain,
% 3.14/1.00      ( ~ v1_xboole_0(sK3) | ~ v1_xboole_0(k1_xboole_0) | sK3 = k1_xboole_0 ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_2331]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_20,plain,
% 3.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.00      | ~ v1_xboole_0(X2)
% 3.14/1.00      | v1_xboole_0(X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2287,plain,
% 3.14/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/1.00      | ~ v1_xboole_0(X1)
% 3.14/1.00      | v1_xboole_0(sK3) ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2592,plain,
% 3.14/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.14/1.00      | ~ v1_xboole_0(sK2)
% 3.14/1.00      | v1_xboole_0(sK3) ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_2287]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6298,plain,
% 3.14/1.00      ( sK3 = k1_xboole_0 ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_5410,c_35,c_3,c_2274,c_2333,c_2592,c_5392]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6312,plain,
% 3.14/1.00      ( r1_tarski(k1_relat_1(k1_xboole_0),sK1) != iProver_top ),
% 3.14/1.00      inference(demodulation,[status(thm)],[c_6298,c_5262]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_13,plain,
% 3.14/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.14/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6321,plain,
% 3.14/1.00      ( r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.14/1.00      inference(light_normalisation,[status(thm)],[c_6312,c_13]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_4,plain,
% 3.14/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1829,plain,
% 3.14/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6489,plain,
% 3.14/1.00      ( $false ),
% 3.14/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_6321,c_1829]) ).
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/1.00  
% 3.14/1.00  ------                               Statistics
% 3.14/1.00  
% 3.14/1.00  ------ General
% 3.14/1.00  
% 3.14/1.00  abstr_ref_over_cycles:                  0
% 3.14/1.00  abstr_ref_under_cycles:                 0
% 3.14/1.00  gc_basic_clause_elim:                   0
% 3.14/1.00  forced_gc_time:                         0
% 3.14/1.00  parsing_time:                           0.01
% 3.14/1.00  unif_index_cands_time:                  0.
% 3.14/1.00  unif_index_add_time:                    0.
% 3.14/1.00  orderings_time:                         0.
% 3.14/1.00  out_proof_time:                         0.01
% 3.14/1.00  total_time:                             0.198
% 3.14/1.00  num_of_symbols:                         51
% 3.14/1.00  num_of_terms:                           4428
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing
% 3.14/1.00  
% 3.14/1.00  num_of_splits:                          0
% 3.14/1.00  num_of_split_atoms:                     0
% 3.14/1.00  num_of_reused_defs:                     0
% 3.14/1.00  num_eq_ax_congr_red:                    9
% 3.14/1.00  num_of_sem_filtered_clauses:            1
% 3.14/1.00  num_of_subtypes:                        0
% 3.14/1.00  monotx_restored_types:                  0
% 3.14/1.00  sat_num_of_epr_types:                   0
% 3.14/1.00  sat_num_of_non_cyclic_types:            0
% 3.14/1.00  sat_guarded_non_collapsed_types:        0
% 3.14/1.00  num_pure_diseq_elim:                    0
% 3.14/1.00  simp_replaced_by:                       0
% 3.14/1.00  res_preprocessed:                       144
% 3.14/1.00  prep_upred:                             0
% 3.14/1.00  prep_unflattend:                        92
% 3.14/1.00  smt_new_axioms:                         0
% 3.14/1.00  pred_elim_cands:                        8
% 3.14/1.00  pred_elim:                              2
% 3.14/1.00  pred_elim_cl:                           -1
% 3.14/1.00  pred_elim_cycles:                       4
% 3.14/1.00  merged_defs:                            0
% 3.14/1.00  merged_defs_ncl:                        0
% 3.14/1.00  bin_hyper_res:                          0
% 3.14/1.00  prep_cycles:                            3
% 3.14/1.00  pred_elim_time:                         0.019
% 3.14/1.00  splitting_time:                         0.
% 3.14/1.00  sem_filter_time:                        0.
% 3.14/1.00  monotx_time:                            0.001
% 3.14/1.00  subtype_inf_time:                       0.
% 3.14/1.00  
% 3.14/1.00  ------ Problem properties
% 3.14/1.00  
% 3.14/1.00  clauses:                                38
% 3.14/1.00  conjectures:                            3
% 3.14/1.00  epr:                                    7
% 3.14/1.00  horn:                                   32
% 3.14/1.00  ground:                                 16
% 3.14/1.00  unary:                                  10
% 3.14/1.00  binary:                                 10
% 3.14/1.00  lits:                                   99
% 3.14/1.00  lits_eq:                                36
% 3.14/1.00  fd_pure:                                0
% 3.14/1.00  fd_pseudo:                              0
% 3.14/1.00  fd_cond:                                3
% 3.14/1.00  fd_pseudo_cond:                         1
% 3.14/1.00  ac_symbols:                             0
% 3.14/1.00  
% 3.14/1.00  ------ Propositional Solver
% 3.14/1.00  
% 3.14/1.00  prop_solver_calls:                      23
% 3.14/1.00  prop_fast_solver_calls:                 1209
% 3.14/1.00  smt_solver_calls:                       0
% 3.14/1.00  smt_fast_solver_calls:                  0
% 3.14/1.00  prop_num_of_clauses:                    2135
% 3.14/1.00  prop_preprocess_simplified:             5984
% 3.14/1.00  prop_fo_subsumed:                       29
% 3.14/1.00  prop_solver_time:                       0.
% 3.14/1.00  smt_solver_time:                        0.
% 3.14/1.00  smt_fast_solver_time:                   0.
% 3.14/1.00  prop_fast_solver_time:                  0.
% 3.14/1.00  prop_unsat_core_time:                   0.
% 3.14/1.00  
% 3.14/1.00  ------ QBF
% 3.14/1.00  
% 3.14/1.00  qbf_q_res:                              0
% 3.14/1.00  qbf_num_tautologies:                    0
% 3.14/1.00  qbf_prep_cycles:                        0
% 3.14/1.00  
% 3.14/1.00  ------ BMC1
% 3.14/1.00  
% 3.14/1.00  bmc1_current_bound:                     -1
% 3.14/1.00  bmc1_last_solved_bound:                 -1
% 3.14/1.00  bmc1_unsat_core_size:                   -1
% 3.14/1.00  bmc1_unsat_core_parents_size:           -1
% 3.14/1.00  bmc1_merge_next_fun:                    0
% 3.14/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.14/1.00  
% 3.14/1.00  ------ Instantiation
% 3.14/1.00  
% 3.14/1.00  inst_num_of_clauses:                    659
% 3.14/1.00  inst_num_in_passive:                    78
% 3.14/1.00  inst_num_in_active:                     388
% 3.14/1.00  inst_num_in_unprocessed:                193
% 3.14/1.00  inst_num_of_loops:                      500
% 3.14/1.00  inst_num_of_learning_restarts:          0
% 3.14/1.00  inst_num_moves_active_passive:          109
% 3.14/1.00  inst_lit_activity:                      0
% 3.14/1.00  inst_lit_activity_moves:                0
% 3.14/1.00  inst_num_tautologies:                   0
% 3.14/1.00  inst_num_prop_implied:                  0
% 3.14/1.00  inst_num_existing_simplified:           0
% 3.14/1.00  inst_num_eq_res_simplified:             0
% 3.14/1.00  inst_num_child_elim:                    0
% 3.14/1.00  inst_num_of_dismatching_blockings:      362
% 3.14/1.00  inst_num_of_non_proper_insts:           747
% 3.14/1.00  inst_num_of_duplicates:                 0
% 3.14/1.00  inst_inst_num_from_inst_to_res:         0
% 3.14/1.00  inst_dismatching_checking_time:         0.
% 3.14/1.00  
% 3.14/1.00  ------ Resolution
% 3.14/1.00  
% 3.14/1.00  res_num_of_clauses:                     0
% 3.14/1.00  res_num_in_passive:                     0
% 3.14/1.00  res_num_in_active:                      0
% 3.14/1.00  res_num_of_loops:                       147
% 3.14/1.00  res_forward_subset_subsumed:            26
% 3.14/1.00  res_backward_subset_subsumed:           2
% 3.14/1.00  res_forward_subsumed:                   0
% 3.14/1.00  res_backward_subsumed:                  0
% 3.14/1.00  res_forward_subsumption_resolution:     4
% 3.14/1.00  res_backward_subsumption_resolution:    0
% 3.14/1.00  res_clause_to_clause_subsumption:       327
% 3.14/1.00  res_orphan_elimination:                 0
% 3.14/1.00  res_tautology_del:                      72
% 3.14/1.00  res_num_eq_res_simplified:              0
% 3.14/1.00  res_num_sel_changes:                    0
% 3.14/1.00  res_moves_from_active_to_pass:          0
% 3.14/1.00  
% 3.14/1.00  ------ Superposition
% 3.14/1.00  
% 3.14/1.00  sup_time_total:                         0.
% 3.14/1.00  sup_time_generating:                    0.
% 3.14/1.00  sup_time_sim_full:                      0.
% 3.14/1.00  sup_time_sim_immed:                     0.
% 3.14/1.00  
% 3.14/1.00  sup_num_of_clauses:                     80
% 3.14/1.00  sup_num_in_active:                      41
% 3.14/1.00  sup_num_in_passive:                     39
% 3.14/1.00  sup_num_of_loops:                       99
% 3.14/1.00  sup_fw_superposition:                   66
% 3.14/1.00  sup_bw_superposition:                   54
% 3.14/1.00  sup_immediate_simplified:               67
% 3.14/1.00  sup_given_eliminated:                   0
% 3.14/1.00  comparisons_done:                       0
% 3.14/1.00  comparisons_avoided:                    8
% 3.14/1.00  
% 3.14/1.00  ------ Simplifications
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  sim_fw_subset_subsumed:                 17
% 3.14/1.00  sim_bw_subset_subsumed:                 12
% 3.14/1.00  sim_fw_subsumed:                        12
% 3.14/1.00  sim_bw_subsumed:                        1
% 3.14/1.00  sim_fw_subsumption_res:                 4
% 3.14/1.00  sim_bw_subsumption_res:                 0
% 3.14/1.00  sim_tautology_del:                      1
% 3.14/1.00  sim_eq_tautology_del:                   15
% 3.14/1.00  sim_eq_res_simp:                        3
% 3.14/1.00  sim_fw_demodulated:                     12
% 3.14/1.00  sim_bw_demodulated:                     51
% 3.14/1.00  sim_light_normalised:                   37
% 3.14/1.00  sim_joinable_taut:                      0
% 3.14/1.00  sim_joinable_simp:                      0
% 3.14/1.00  sim_ac_normalised:                      0
% 3.14/1.00  sim_smt_subsumption:                    0
% 3.14/1.00  
%------------------------------------------------------------------------------

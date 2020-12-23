%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0985+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:34 EST 2020

% Result     : Theorem 19.19s
% Output     : CNFRefutation 19.19s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 577 expanded)
%              Number of clauses        :  128 ( 224 expanded)
%              Number of leaves         :   22 ( 119 expanded)
%              Depth                    :   18
%              Number of atoms          :  579 (2768 expanded)
%              Number of equality atoms :  245 ( 625 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f47,plain,
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

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f47])).

fof(f77,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f72,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_44438,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | k1_relset_1(sK3,sK2,k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_868,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_44377,plain,
    ( k1_relset_1(sK3,sK2,k2_funct_1(sK4)) != X0
    | k1_relset_1(sK3,sK2,k2_funct_1(sK4)) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_44391,plain,
    ( k1_relset_1(sK3,sK2,k2_funct_1(sK4)) != k1_relat_1(k2_funct_1(sK4))
    | k1_relset_1(sK3,sK2,k2_funct_1(sK4)) = sK3
    | sK3 != k1_relat_1(k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_44377])).

cnf(c_1655,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_2683,plain,
    ( X0 != k2_relset_1(sK2,sK3,sK4)
    | sK3 = X0
    | sK3 != k2_relset_1(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_20359,plain,
    ( k1_relat_1(X0) != k2_relset_1(sK2,sK3,sK4)
    | sK3 != k2_relset_1(sK2,sK3,sK4)
    | sK3 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_2683])).

cnf(c_40505,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != k2_relset_1(sK2,sK3,sK4)
    | sK3 != k2_relset_1(sK2,sK3,sK4)
    | sK3 = k1_relat_1(k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_20359])).

cnf(c_8,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4249,plain,
    ( ~ r2_hidden(sK0(X0,sK3),sK3)
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_21493,plain,
    ( ~ r2_hidden(sK0(sK3,sK3),sK3)
    | r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_4249])).

cnf(c_9,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4250,plain,
    ( r2_hidden(sK0(X0,sK3),X0)
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_21492,plain,
    ( r2_hidden(sK0(sK3,sK3),sK3)
    | r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_4250])).

cnf(c_875,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_3154,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(k2_funct_1(sK4)),X1)
    | k2_relat_1(k2_funct_1(sK4)) != X0 ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_13128,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),X0)
    | r1_tarski(k2_relat_1(k2_funct_1(sK4)),X0)
    | k2_relat_1(k2_funct_1(sK4)) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3154])).

cnf(c_15938,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK2)
    | r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK2)
    | k2_relat_1(k2_funct_1(sK4)) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13128])).

cnf(c_1800,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_8967,plain,
    ( k2_funct_1(sK4) != X0
    | k2_funct_1(sK4) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1800])).

cnf(c_8968,plain,
    ( k2_funct_1(sK4) = sK4
    | k2_funct_1(sK4) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8967])).

cnf(c_1832,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK3)
    | k1_relat_1(k2_funct_1(sK4)) != X0 ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_7575,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK3)
    | ~ r1_tarski(sK3,sK3)
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(instantiation,[status(thm)],[c_1832])).

cnf(c_2846,plain,
    ( X0 != X1
    | X0 = k2_relset_1(sK2,sK3,sK4)
    | k2_relset_1(sK2,sK3,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_4024,plain,
    ( X0 = k2_relset_1(sK2,sK3,sK4)
    | X0 != sK3
    | k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_7236,plain,
    ( k2_relset_1(sK2,sK3,sK4) != sK3
    | k1_relat_1(k2_funct_1(sK4)) = k2_relset_1(sK2,sK3,sK4)
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(instantiation,[status(thm)],[c_4024])).

cnf(c_873,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7137,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_7139,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7137])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1541,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1547,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2879,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1541,c_1547])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1554,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3271,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2879,c_1554])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3557,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3271,c_34])).

cnf(c_22,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1543,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3562,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3557,c_1543])).

cnf(c_3563,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3562])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1558,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3382,plain,
    ( v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1558])).

cnf(c_3391,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3382])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_30])).

cnf(c_552,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_554,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_552,c_29])).

cnf(c_2931,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_554,c_2879])).

cnf(c_17,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1548,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2944,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2931,c_1548])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1598,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1627,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_1628,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1627])).

cnf(c_1610,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_1654,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1610])).

cnf(c_867,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1714,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_25,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2172,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2173,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2172])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1546,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2792,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1541,c_1546])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2793,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2792,c_27])).

cnf(c_16,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1549,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2873,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2793,c_1549])).

cnf(c_3110,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2944,c_34,c_1628,c_1654,c_1714,c_2173,c_2873])).

cnf(c_3112,plain,
    ( ~ v1_xboole_0(sK2)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3110])).

cnf(c_3084,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_3086,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3084])).

cnf(c_24,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_415,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_416,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_418,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_31])).

cnf(c_1539,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_1722,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1539,c_31,c_29,c_416,c_1627])).

cnf(c_2872,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2793,c_1722])).

cnf(c_2913,plain,
    ( v1_xboole_0(k2_funct_1(sK4)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2872,c_1548])).

cnf(c_32,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1772,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1773,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1772])).

cnf(c_2947,plain,
    ( v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(k2_funct_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2913,c_32,c_34,c_1628,c_1773])).

cnf(c_2948,plain,
    ( v1_xboole_0(k2_funct_1(sK4)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2947])).

cnf(c_1542,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2953,plain,
    ( k2_funct_1(sK4) = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2948,c_1542])).

cnf(c_2957,plain,
    ( ~ v1_xboole_0(sK3)
    | k2_funct_1(sK4) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2953])).

cnf(c_2866,plain,
    ( ~ v1_xboole_0(sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1764,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_2310,plain,
    ( k2_relset_1(sK2,sK3,sK4) != sK3
    | sK3 = k2_relset_1(sK2,sK3,sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1764])).

cnf(c_14,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1551,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1941,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1551,c_1542])).

cnf(c_2131,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1941,c_1551])).

cnf(c_2132,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2131])).

cnf(c_2090,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_1771,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_1966,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_1967,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1966])).

cnf(c_1819,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_1619,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_1679,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_1677,plain,
    ( sK2 != X0
    | sK2 = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_1678,plain,
    ( sK2 = sK3
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1677])).

cnf(c_20,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1666,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK3)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK2)
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_relat_1(k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1616,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_562,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k2_funct_1(sK4) != sK4
    | sK2 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_5,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK4) != X0
    | sK2 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_26])).

cnf(c_536,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(sK3,sK2,k2_funct_1(sK4)) != sK3
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_23,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_429,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_430,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44438,c_44391,c_40505,c_21493,c_21492,c_15938,c_8968,c_7575,c_7236,c_7139,c_3563,c_3391,c_3112,c_3086,c_2957,c_2872,c_2866,c_2310,c_2132,c_2090,c_1967,c_1819,c_1772,c_1714,c_1679,c_1678,c_1666,c_1627,c_1616,c_562,c_536,c_430,c_27,c_29,c_31])).


%------------------------------------------------------------------------------

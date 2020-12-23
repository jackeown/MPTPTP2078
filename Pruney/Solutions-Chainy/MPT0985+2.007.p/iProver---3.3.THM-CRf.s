%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:20 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  169 (3523 expanded)
%              Number of clauses        :   97 (1096 expanded)
%              Number of leaves         :   18 ( 687 expanded)
%              Depth                    :   20
%              Number of atoms          :  549 (18899 expanded)
%              Number of equality atoms :  221 (3559 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f70])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f71,f72])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f67,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f66])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f67,f68])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

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

fof(f64,plain,(
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

fof(f65,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f64])).

fof(f79,plain,
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

fof(f80,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f65,f79])).

fof(f135,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f108,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f132,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

fof(f134,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f80])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f116,plain,(
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

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f62])).

fof(f130,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f137,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f80])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f110,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f114,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f136,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f80])).

fof(f115,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f26,axiom,(
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
    inference(ennf_transformation,[],[f26])).

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

fof(f78,plain,(
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

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f133,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f80])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f27,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f60])).

fof(f127,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f128,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f109,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f131,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f93,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3156,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3158,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5225,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3156,c_3158])).

cnf(c_53,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_3126,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_27,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3139,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8811,plain,
    ( k2_funct_1(sK4) = k4_relat_1(sK4)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3126,c_3139])).

cnf(c_56,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_54,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_851,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_53])).

cnf(c_852,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_funct_1(sK4) = k4_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_851])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3774,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_4092,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3774])).

cnf(c_9440,plain,
    ( k2_funct_1(sK4) = k4_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8811,c_56,c_54,c_852,c_4092])).

cnf(c_49,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_51,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_1217,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK4) != X0
    | k1_relat_1(X0) != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_49,c_51])).

cnf(c_1218,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK2)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(unflattening,[status(thm)],[c_1217])).

cnf(c_1230,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK2)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1218,c_35])).

cnf(c_3109,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_9446,plain,
    ( k1_relat_1(k4_relat_1(sK4)) != sK3
    | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK4)),sK2) != iProver_top
    | v1_funct_1(k4_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9440,c_3109])).

cnf(c_57,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_59,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_4093,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4092])).

cnf(c_28,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_3138,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_9496,plain,
    ( v1_funct_1(k4_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9440,c_3138])).

cnf(c_34,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3132,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9894,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3126,c_3132])).

cnf(c_3125,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3129,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6194,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3125,c_3129])).

cnf(c_52,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_6196,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_6194,c_52])).

cnf(c_9923,plain,
    ( k1_relat_1(k4_relat_1(sK4)) = sK3
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9894,c_6196,c_9440])).

cnf(c_13522,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(sK4)),sK2) != iProver_top
    | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9446,c_57,c_59,c_4093,c_9496,c_9923])).

cnf(c_13523,plain,
    ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK4)),sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_13522])).

cnf(c_33,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3133,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10059,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3126,c_3133])).

cnf(c_10088,plain,
    ( k2_relat_1(k4_relat_1(sK4)) = k1_relat_1(sK4)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10059,c_9440])).

cnf(c_10667,plain,
    ( k2_relat_1(k4_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10088,c_57,c_59,c_4093])).

cnf(c_44,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_55,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1187,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_55])).

cnf(c_1188,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_1187])).

cnf(c_1190,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1188,c_54])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_3130,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6900,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3125,c_3130])).

cnf(c_7062,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1190,c_6900])).

cnf(c_46,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1198,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK4) != X0
    | k1_relat_1(X0) != sK3
    | k2_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_46,c_51])).

cnf(c_1199,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1198])).

cnf(c_1211,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1199,c_35])).

cnf(c_3110,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1211])).

cnf(c_9443,plain,
    ( k1_relat_1(k4_relat_1(sK4)) != sK3
    | k2_relat_1(k4_relat_1(sK4)) != sK2
    | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k4_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9440,c_3110])).

cnf(c_12432,plain,
    ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | k2_relat_1(k4_relat_1(sK4)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9443,c_57,c_59,c_4093,c_9496,c_9923])).

cnf(c_12433,plain,
    ( k2_relat_1(k4_relat_1(sK4)) != sK2
    | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12432])).

cnf(c_12436,plain,
    ( k1_relat_1(sK4) != sK2
    | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12433,c_10667])).

cnf(c_12440,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7062,c_12436])).

cnf(c_45,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_3128,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_10671,plain,
    ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK4)),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK4)) != iProver_top
    | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10667,c_3128])).

cnf(c_10269,plain,
    ( k1_relat_1(k4_relat_1(sK4)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9923,c_57,c_59,c_4093])).

cnf(c_10740,plain,
    ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK4)) != iProver_top
    | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10671,c_10269])).

cnf(c_29,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3137,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_9497,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9440,c_3137])).

cnf(c_11149,plain,
    ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10740,c_57,c_59,c_4093,c_9496,c_9497])).

cnf(c_11154,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7062,c_11149])).

cnf(c_12443,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12440,c_11154])).

cnf(c_13526,plain,
    ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13523,c_10667,c_12443])).

cnf(c_48,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_3127,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_10272,plain,
    ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK4)),X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK4)) != iProver_top
    | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10269,c_3127])).

cnf(c_13392,plain,
    ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK4)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10272,c_57,c_59,c_4093,c_9496,c_9497])).

cnf(c_13398,plain,
    ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13392,c_10667,c_12443])).

cnf(c_13529,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13526,c_13398])).

cnf(c_14859,plain,
    ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5225,c_13529])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3145,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10274,plain,
    ( v1_relat_1(k4_relat_1(sK4)) != iProver_top
    | v1_xboole_0(k4_relat_1(sK4)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10269,c_3145])).

cnf(c_10968,plain,
    ( v1_xboole_0(k4_relat_1(sK4)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10274,c_57,c_59,c_4093,c_9497])).

cnf(c_12450,plain,
    ( v1_xboole_0(k4_relat_1(sK4)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12443,c_10968])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3148,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10678,plain,
    ( v1_xboole_0(k1_relat_1(sK4)) = iProver_top
    | v1_xboole_0(k4_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10667,c_3148])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_183,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14859,c_12450,c_10678,c_183])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : iproveropt_run.sh %d %s
% 0.09/0.29  % Computer   : n015.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 10:38:08 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.14/0.29  % Running in FOF mode
% 3.75/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/0.94  
% 3.75/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/0.94  
% 3.75/0.94  ------  iProver source info
% 3.75/0.94  
% 3.75/0.94  git: date: 2020-06-30 10:37:57 +0100
% 3.75/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/0.94  git: non_committed_changes: false
% 3.75/0.94  git: last_make_outside_of_git: false
% 3.75/0.94  
% 3.75/0.94  ------ 
% 3.75/0.94  
% 3.75/0.94  ------ Input Options
% 3.75/0.94  
% 3.75/0.94  --out_options                           all
% 3.75/0.94  --tptp_safe_out                         true
% 3.75/0.94  --problem_path                          ""
% 3.75/0.94  --include_path                          ""
% 3.75/0.94  --clausifier                            res/vclausify_rel
% 3.75/0.94  --clausifier_options                    --mode clausify
% 3.75/0.94  --stdin                                 false
% 3.75/0.94  --stats_out                             all
% 3.75/0.94  
% 3.75/0.94  ------ General Options
% 3.75/0.94  
% 3.75/0.94  --fof                                   false
% 3.75/0.94  --time_out_real                         305.
% 3.75/0.94  --time_out_virtual                      -1.
% 3.75/0.94  --symbol_type_check                     false
% 3.75/0.94  --clausify_out                          false
% 3.75/0.94  --sig_cnt_out                           false
% 3.75/0.94  --trig_cnt_out                          false
% 3.75/0.94  --trig_cnt_out_tolerance                1.
% 3.75/0.94  --trig_cnt_out_sk_spl                   false
% 3.75/0.94  --abstr_cl_out                          false
% 3.75/0.94  
% 3.75/0.94  ------ Global Options
% 3.75/0.94  
% 3.75/0.94  --schedule                              default
% 3.75/0.94  --add_important_lit                     false
% 3.75/0.94  --prop_solver_per_cl                    1000
% 3.75/0.94  --min_unsat_core                        false
% 3.75/0.94  --soft_assumptions                      false
% 3.75/0.94  --soft_lemma_size                       3
% 3.75/0.94  --prop_impl_unit_size                   0
% 3.75/0.94  --prop_impl_unit                        []
% 3.75/0.94  --share_sel_clauses                     true
% 3.75/0.94  --reset_solvers                         false
% 3.75/0.94  --bc_imp_inh                            [conj_cone]
% 3.75/0.94  --conj_cone_tolerance                   3.
% 3.75/0.94  --extra_neg_conj                        none
% 3.75/0.94  --large_theory_mode                     true
% 3.75/0.94  --prolific_symb_bound                   200
% 3.75/0.94  --lt_threshold                          2000
% 3.75/0.94  --clause_weak_htbl                      true
% 3.75/0.94  --gc_record_bc_elim                     false
% 3.75/0.94  
% 3.75/0.94  ------ Preprocessing Options
% 3.75/0.94  
% 3.75/0.94  --preprocessing_flag                    true
% 3.75/0.94  --time_out_prep_mult                    0.1
% 3.75/0.94  --splitting_mode                        input
% 3.75/0.94  --splitting_grd                         true
% 3.75/0.94  --splitting_cvd                         false
% 3.75/0.94  --splitting_cvd_svl                     false
% 3.75/0.94  --splitting_nvd                         32
% 3.75/0.94  --sub_typing                            true
% 3.75/0.94  --prep_gs_sim                           true
% 3.75/0.94  --prep_unflatten                        true
% 3.75/0.94  --prep_res_sim                          true
% 3.75/0.94  --prep_upred                            true
% 3.75/0.94  --prep_sem_filter                       exhaustive
% 3.75/0.94  --prep_sem_filter_out                   false
% 3.75/0.94  --pred_elim                             true
% 3.75/0.94  --res_sim_input                         true
% 3.75/0.94  --eq_ax_congr_red                       true
% 3.75/0.94  --pure_diseq_elim                       true
% 3.75/0.94  --brand_transform                       false
% 3.75/0.94  --non_eq_to_eq                          false
% 3.75/0.94  --prep_def_merge                        true
% 3.75/0.94  --prep_def_merge_prop_impl              false
% 3.75/0.94  --prep_def_merge_mbd                    true
% 3.75/0.94  --prep_def_merge_tr_red                 false
% 3.75/0.94  --prep_def_merge_tr_cl                  false
% 3.75/0.94  --smt_preprocessing                     true
% 3.75/0.94  --smt_ac_axioms                         fast
% 3.75/0.94  --preprocessed_out                      false
% 3.75/0.94  --preprocessed_stats                    false
% 3.75/0.94  
% 3.75/0.94  ------ Abstraction refinement Options
% 3.75/0.94  
% 3.75/0.94  --abstr_ref                             []
% 3.75/0.94  --abstr_ref_prep                        false
% 3.75/0.94  --abstr_ref_until_sat                   false
% 3.75/0.94  --abstr_ref_sig_restrict                funpre
% 3.75/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/0.94  --abstr_ref_under                       []
% 3.75/0.94  
% 3.75/0.94  ------ SAT Options
% 3.75/0.94  
% 3.75/0.94  --sat_mode                              false
% 3.75/0.94  --sat_fm_restart_options                ""
% 3.75/0.94  --sat_gr_def                            false
% 3.75/0.94  --sat_epr_types                         true
% 3.75/0.94  --sat_non_cyclic_types                  false
% 3.75/0.94  --sat_finite_models                     false
% 3.75/0.94  --sat_fm_lemmas                         false
% 3.75/0.94  --sat_fm_prep                           false
% 3.75/0.94  --sat_fm_uc_incr                        true
% 3.75/0.94  --sat_out_model                         small
% 3.75/0.94  --sat_out_clauses                       false
% 3.75/0.94  
% 3.75/0.94  ------ QBF Options
% 3.75/0.94  
% 3.75/0.94  --qbf_mode                              false
% 3.75/0.94  --qbf_elim_univ                         false
% 3.75/0.94  --qbf_dom_inst                          none
% 3.75/0.94  --qbf_dom_pre_inst                      false
% 3.75/0.94  --qbf_sk_in                             false
% 3.75/0.94  --qbf_pred_elim                         true
% 3.75/0.94  --qbf_split                             512
% 3.75/0.94  
% 3.75/0.94  ------ BMC1 Options
% 3.75/0.94  
% 3.75/0.94  --bmc1_incremental                      false
% 3.75/0.94  --bmc1_axioms                           reachable_all
% 3.75/0.94  --bmc1_min_bound                        0
% 3.75/0.94  --bmc1_max_bound                        -1
% 3.75/0.94  --bmc1_max_bound_default                -1
% 3.75/0.94  --bmc1_symbol_reachability              true
% 3.75/0.94  --bmc1_property_lemmas                  false
% 3.75/0.94  --bmc1_k_induction                      false
% 3.75/0.94  --bmc1_non_equiv_states                 false
% 3.75/0.94  --bmc1_deadlock                         false
% 3.75/0.94  --bmc1_ucm                              false
% 3.75/0.94  --bmc1_add_unsat_core                   none
% 3.75/0.94  --bmc1_unsat_core_children              false
% 3.75/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/0.94  --bmc1_out_stat                         full
% 3.75/0.94  --bmc1_ground_init                      false
% 3.75/0.94  --bmc1_pre_inst_next_state              false
% 3.75/0.94  --bmc1_pre_inst_state                   false
% 3.75/0.94  --bmc1_pre_inst_reach_state             false
% 3.75/0.94  --bmc1_out_unsat_core                   false
% 3.75/0.94  --bmc1_aig_witness_out                  false
% 3.75/0.94  --bmc1_verbose                          false
% 3.75/0.94  --bmc1_dump_clauses_tptp                false
% 3.75/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.75/0.94  --bmc1_dump_file                        -
% 3.75/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.75/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.75/0.94  --bmc1_ucm_extend_mode                  1
% 3.75/0.94  --bmc1_ucm_init_mode                    2
% 3.75/0.94  --bmc1_ucm_cone_mode                    none
% 3.75/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.75/0.94  --bmc1_ucm_relax_model                  4
% 3.75/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.75/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/0.94  --bmc1_ucm_layered_model                none
% 3.75/0.94  --bmc1_ucm_max_lemma_size               10
% 3.75/0.94  
% 3.75/0.94  ------ AIG Options
% 3.75/0.94  
% 3.75/0.94  --aig_mode                              false
% 3.75/0.94  
% 3.75/0.94  ------ Instantiation Options
% 3.75/0.94  
% 3.75/0.94  --instantiation_flag                    true
% 3.75/0.94  --inst_sos_flag                         false
% 3.75/0.94  --inst_sos_phase                        true
% 3.75/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/0.94  --inst_lit_sel_side                     num_symb
% 3.75/0.94  --inst_solver_per_active                1400
% 3.75/0.94  --inst_solver_calls_frac                1.
% 3.75/0.94  --inst_passive_queue_type               priority_queues
% 3.75/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/0.94  --inst_passive_queues_freq              [25;2]
% 3.75/0.94  --inst_dismatching                      true
% 3.75/0.94  --inst_eager_unprocessed_to_passive     true
% 3.75/0.94  --inst_prop_sim_given                   true
% 3.75/0.94  --inst_prop_sim_new                     false
% 3.75/0.94  --inst_subs_new                         false
% 3.75/0.94  --inst_eq_res_simp                      false
% 3.75/0.94  --inst_subs_given                       false
% 3.75/0.94  --inst_orphan_elimination               true
% 3.75/0.94  --inst_learning_loop_flag               true
% 3.75/0.94  --inst_learning_start                   3000
% 3.75/0.94  --inst_learning_factor                  2
% 3.75/0.94  --inst_start_prop_sim_after_learn       3
% 3.75/0.94  --inst_sel_renew                        solver
% 3.75/0.94  --inst_lit_activity_flag                true
% 3.75/0.94  --inst_restr_to_given                   false
% 3.75/0.94  --inst_activity_threshold               500
% 3.75/0.94  --inst_out_proof                        true
% 3.75/0.94  
% 3.75/0.94  ------ Resolution Options
% 3.75/0.94  
% 3.75/0.94  --resolution_flag                       true
% 3.75/0.94  --res_lit_sel                           adaptive
% 3.75/0.94  --res_lit_sel_side                      none
% 3.75/0.94  --res_ordering                          kbo
% 3.75/0.94  --res_to_prop_solver                    active
% 3.75/0.94  --res_prop_simpl_new                    false
% 3.75/0.94  --res_prop_simpl_given                  true
% 3.75/0.94  --res_passive_queue_type                priority_queues
% 3.75/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/0.94  --res_passive_queues_freq               [15;5]
% 3.75/0.94  --res_forward_subs                      full
% 3.75/0.94  --res_backward_subs                     full
% 3.75/0.94  --res_forward_subs_resolution           true
% 3.75/0.94  --res_backward_subs_resolution          true
% 3.75/0.94  --res_orphan_elimination                true
% 3.75/0.94  --res_time_limit                        2.
% 3.75/0.94  --res_out_proof                         true
% 3.75/0.94  
% 3.75/0.94  ------ Superposition Options
% 3.75/0.94  
% 3.75/0.94  --superposition_flag                    true
% 3.75/0.94  --sup_passive_queue_type                priority_queues
% 3.75/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.75/0.94  --demod_completeness_check              fast
% 3.75/0.94  --demod_use_ground                      true
% 3.75/0.94  --sup_to_prop_solver                    passive
% 3.75/0.94  --sup_prop_simpl_new                    true
% 3.75/0.94  --sup_prop_simpl_given                  true
% 3.75/0.94  --sup_fun_splitting                     false
% 3.75/0.94  --sup_smt_interval                      50000
% 3.75/0.94  
% 3.75/0.94  ------ Superposition Simplification Setup
% 3.75/0.94  
% 3.75/0.94  --sup_indices_passive                   []
% 3.75/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.94  --sup_full_bw                           [BwDemod]
% 3.75/0.94  --sup_immed_triv                        [TrivRules]
% 3.75/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.94  --sup_immed_bw_main                     []
% 3.75/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.94  
% 3.75/0.94  ------ Combination Options
% 3.75/0.94  
% 3.75/0.94  --comb_res_mult                         3
% 3.75/0.94  --comb_sup_mult                         2
% 3.75/0.94  --comb_inst_mult                        10
% 3.75/0.94  
% 3.75/0.94  ------ Debug Options
% 3.75/0.94  
% 3.75/0.94  --dbg_backtrace                         false
% 3.75/0.94  --dbg_dump_prop_clauses                 false
% 3.75/0.94  --dbg_dump_prop_clauses_file            -
% 3.75/0.94  --dbg_out_stat                          false
% 3.75/0.94  ------ Parsing...
% 3.75/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/0.94  
% 3.75/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.75/0.94  
% 3.75/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/0.94  
% 3.75/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.94  ------ Proving...
% 3.75/0.94  ------ Problem Properties 
% 3.75/0.94  
% 3.75/0.94  
% 3.75/0.94  clauses                                 56
% 3.75/0.94  conjectures                             4
% 3.75/0.94  EPR                                     10
% 3.75/0.94  Horn                                    48
% 3.75/0.94  unary                                   10
% 3.75/0.94  binary                                  19
% 3.75/0.94  lits                                    155
% 3.75/0.94  lits eq                                 49
% 3.75/0.94  fd_pure                                 0
% 3.75/0.94  fd_pseudo                               0
% 3.75/0.94  fd_cond                                 3
% 3.75/0.94  fd_pseudo_cond                          1
% 3.75/0.94  AC symbols                              0
% 3.75/0.94  
% 3.75/0.94  ------ Schedule dynamic 5 is on 
% 3.75/0.94  
% 3.75/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.75/0.94  
% 3.75/0.94  
% 3.75/0.94  ------ 
% 3.75/0.94  Current options:
% 3.75/0.94  ------ 
% 3.75/0.94  
% 3.75/0.94  ------ Input Options
% 3.75/0.94  
% 3.75/0.94  --out_options                           all
% 3.75/0.94  --tptp_safe_out                         true
% 3.75/0.94  --problem_path                          ""
% 3.75/0.94  --include_path                          ""
% 3.75/0.94  --clausifier                            res/vclausify_rel
% 3.75/0.94  --clausifier_options                    --mode clausify
% 3.75/0.94  --stdin                                 false
% 3.75/0.94  --stats_out                             all
% 3.75/0.94  
% 3.75/0.94  ------ General Options
% 3.75/0.94  
% 3.75/0.94  --fof                                   false
% 3.75/0.94  --time_out_real                         305.
% 3.75/0.94  --time_out_virtual                      -1.
% 3.75/0.94  --symbol_type_check                     false
% 3.75/0.94  --clausify_out                          false
% 3.75/0.94  --sig_cnt_out                           false
% 3.75/0.94  --trig_cnt_out                          false
% 3.75/0.94  --trig_cnt_out_tolerance                1.
% 3.75/0.94  --trig_cnt_out_sk_spl                   false
% 3.75/0.94  --abstr_cl_out                          false
% 3.75/0.94  
% 3.75/0.94  ------ Global Options
% 3.75/0.94  
% 3.75/0.94  --schedule                              default
% 3.75/0.94  --add_important_lit                     false
% 3.75/0.94  --prop_solver_per_cl                    1000
% 3.75/0.94  --min_unsat_core                        false
% 3.75/0.94  --soft_assumptions                      false
% 3.75/0.94  --soft_lemma_size                       3
% 3.75/0.94  --prop_impl_unit_size                   0
% 3.75/0.94  --prop_impl_unit                        []
% 3.75/0.94  --share_sel_clauses                     true
% 3.75/0.94  --reset_solvers                         false
% 3.75/0.94  --bc_imp_inh                            [conj_cone]
% 3.75/0.94  --conj_cone_tolerance                   3.
% 3.75/0.94  --extra_neg_conj                        none
% 3.75/0.94  --large_theory_mode                     true
% 3.75/0.94  --prolific_symb_bound                   200
% 3.75/0.94  --lt_threshold                          2000
% 3.75/0.94  --clause_weak_htbl                      true
% 3.75/0.94  --gc_record_bc_elim                     false
% 3.75/0.94  
% 3.75/0.94  ------ Preprocessing Options
% 3.75/0.94  
% 3.75/0.94  --preprocessing_flag                    true
% 3.75/0.94  --time_out_prep_mult                    0.1
% 3.75/0.94  --splitting_mode                        input
% 3.75/0.94  --splitting_grd                         true
% 3.75/0.94  --splitting_cvd                         false
% 3.75/0.94  --splitting_cvd_svl                     false
% 3.75/0.94  --splitting_nvd                         32
% 3.75/0.94  --sub_typing                            true
% 3.75/0.94  --prep_gs_sim                           true
% 3.75/0.94  --prep_unflatten                        true
% 3.75/0.94  --prep_res_sim                          true
% 3.75/0.94  --prep_upred                            true
% 3.75/0.94  --prep_sem_filter                       exhaustive
% 3.75/0.94  --prep_sem_filter_out                   false
% 3.75/0.94  --pred_elim                             true
% 3.75/0.94  --res_sim_input                         true
% 3.75/0.94  --eq_ax_congr_red                       true
% 3.75/0.94  --pure_diseq_elim                       true
% 3.75/0.94  --brand_transform                       false
% 3.75/0.94  --non_eq_to_eq                          false
% 3.75/0.94  --prep_def_merge                        true
% 3.75/0.94  --prep_def_merge_prop_impl              false
% 3.75/0.94  --prep_def_merge_mbd                    true
% 3.75/0.94  --prep_def_merge_tr_red                 false
% 3.75/0.94  --prep_def_merge_tr_cl                  false
% 3.75/0.94  --smt_preprocessing                     true
% 3.75/0.94  --smt_ac_axioms                         fast
% 3.75/0.94  --preprocessed_out                      false
% 3.75/0.94  --preprocessed_stats                    false
% 3.75/0.94  
% 3.75/0.94  ------ Abstraction refinement Options
% 3.75/0.94  
% 3.75/0.94  --abstr_ref                             []
% 3.75/0.94  --abstr_ref_prep                        false
% 3.75/0.94  --abstr_ref_until_sat                   false
% 3.75/0.94  --abstr_ref_sig_restrict                funpre
% 3.75/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/0.94  --abstr_ref_under                       []
% 3.75/0.94  
% 3.75/0.94  ------ SAT Options
% 3.75/0.94  
% 3.75/0.94  --sat_mode                              false
% 3.75/0.94  --sat_fm_restart_options                ""
% 3.75/0.94  --sat_gr_def                            false
% 3.75/0.94  --sat_epr_types                         true
% 3.75/0.94  --sat_non_cyclic_types                  false
% 3.75/0.94  --sat_finite_models                     false
% 3.75/0.94  --sat_fm_lemmas                         false
% 3.75/0.94  --sat_fm_prep                           false
% 3.75/0.94  --sat_fm_uc_incr                        true
% 3.75/0.94  --sat_out_model                         small
% 3.75/0.94  --sat_out_clauses                       false
% 3.75/0.94  
% 3.75/0.94  ------ QBF Options
% 3.75/0.94  
% 3.75/0.94  --qbf_mode                              false
% 3.75/0.94  --qbf_elim_univ                         false
% 3.75/0.94  --qbf_dom_inst                          none
% 3.75/0.94  --qbf_dom_pre_inst                      false
% 3.75/0.94  --qbf_sk_in                             false
% 3.75/0.94  --qbf_pred_elim                         true
% 3.75/0.94  --qbf_split                             512
% 3.75/0.94  
% 3.75/0.94  ------ BMC1 Options
% 3.75/0.94  
% 3.75/0.94  --bmc1_incremental                      false
% 3.75/0.94  --bmc1_axioms                           reachable_all
% 3.75/0.94  --bmc1_min_bound                        0
% 3.75/0.94  --bmc1_max_bound                        -1
% 3.75/0.94  --bmc1_max_bound_default                -1
% 3.75/0.94  --bmc1_symbol_reachability              true
% 3.75/0.94  --bmc1_property_lemmas                  false
% 3.75/0.94  --bmc1_k_induction                      false
% 3.75/0.94  --bmc1_non_equiv_states                 false
% 3.75/0.94  --bmc1_deadlock                         false
% 3.75/0.94  --bmc1_ucm                              false
% 3.75/0.94  --bmc1_add_unsat_core                   none
% 3.75/0.94  --bmc1_unsat_core_children              false
% 3.75/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/0.94  --bmc1_out_stat                         full
% 3.75/0.94  --bmc1_ground_init                      false
% 3.75/0.94  --bmc1_pre_inst_next_state              false
% 3.75/0.94  --bmc1_pre_inst_state                   false
% 3.75/0.94  --bmc1_pre_inst_reach_state             false
% 3.75/0.94  --bmc1_out_unsat_core                   false
% 3.75/0.94  --bmc1_aig_witness_out                  false
% 3.75/0.94  --bmc1_verbose                          false
% 3.75/0.94  --bmc1_dump_clauses_tptp                false
% 3.75/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.75/0.94  --bmc1_dump_file                        -
% 3.75/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.75/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.75/0.94  --bmc1_ucm_extend_mode                  1
% 3.75/0.94  --bmc1_ucm_init_mode                    2
% 3.75/0.94  --bmc1_ucm_cone_mode                    none
% 3.75/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.75/0.94  --bmc1_ucm_relax_model                  4
% 3.75/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.75/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/0.94  --bmc1_ucm_layered_model                none
% 3.75/0.94  --bmc1_ucm_max_lemma_size               10
% 3.75/0.94  
% 3.75/0.94  ------ AIG Options
% 3.75/0.94  
% 3.75/0.94  --aig_mode                              false
% 3.75/0.94  
% 3.75/0.94  ------ Instantiation Options
% 3.75/0.94  
% 3.75/0.94  --instantiation_flag                    true
% 3.75/0.94  --inst_sos_flag                         false
% 3.75/0.94  --inst_sos_phase                        true
% 3.75/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/0.94  --inst_lit_sel_side                     none
% 3.75/0.94  --inst_solver_per_active                1400
% 3.75/0.94  --inst_solver_calls_frac                1.
% 3.75/0.94  --inst_passive_queue_type               priority_queues
% 3.75/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/0.94  --inst_passive_queues_freq              [25;2]
% 3.75/0.94  --inst_dismatching                      true
% 3.75/0.94  --inst_eager_unprocessed_to_passive     true
% 3.75/0.94  --inst_prop_sim_given                   true
% 3.75/0.94  --inst_prop_sim_new                     false
% 3.75/0.94  --inst_subs_new                         false
% 3.75/0.94  --inst_eq_res_simp                      false
% 3.75/0.94  --inst_subs_given                       false
% 3.75/0.94  --inst_orphan_elimination               true
% 3.75/0.94  --inst_learning_loop_flag               true
% 3.75/0.94  --inst_learning_start                   3000
% 3.75/0.94  --inst_learning_factor                  2
% 3.75/0.94  --inst_start_prop_sim_after_learn       3
% 3.75/0.94  --inst_sel_renew                        solver
% 3.75/0.94  --inst_lit_activity_flag                true
% 3.75/0.94  --inst_restr_to_given                   false
% 3.75/0.94  --inst_activity_threshold               500
% 3.75/0.94  --inst_out_proof                        true
% 3.75/0.94  
% 3.75/0.94  ------ Resolution Options
% 3.75/0.94  
% 3.75/0.94  --resolution_flag                       false
% 3.75/0.94  --res_lit_sel                           adaptive
% 3.75/0.94  --res_lit_sel_side                      none
% 3.75/0.94  --res_ordering                          kbo
% 3.75/0.94  --res_to_prop_solver                    active
% 3.75/0.94  --res_prop_simpl_new                    false
% 3.75/0.94  --res_prop_simpl_given                  true
% 3.75/0.94  --res_passive_queue_type                priority_queues
% 3.75/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/0.94  --res_passive_queues_freq               [15;5]
% 3.75/0.94  --res_forward_subs                      full
% 3.75/0.94  --res_backward_subs                     full
% 3.75/0.94  --res_forward_subs_resolution           true
% 3.75/0.94  --res_backward_subs_resolution          true
% 3.75/0.94  --res_orphan_elimination                true
% 3.75/0.94  --res_time_limit                        2.
% 3.75/0.94  --res_out_proof                         true
% 3.75/0.94  
% 3.75/0.94  ------ Superposition Options
% 3.75/0.94  
% 3.75/0.94  --superposition_flag                    true
% 3.75/0.94  --sup_passive_queue_type                priority_queues
% 3.75/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.75/0.94  --demod_completeness_check              fast
% 3.75/0.94  --demod_use_ground                      true
% 3.75/0.94  --sup_to_prop_solver                    passive
% 3.75/0.94  --sup_prop_simpl_new                    true
% 3.75/0.94  --sup_prop_simpl_given                  true
% 3.75/0.94  --sup_fun_splitting                     false
% 3.75/0.94  --sup_smt_interval                      50000
% 3.75/0.94  
% 3.75/0.94  ------ Superposition Simplification Setup
% 3.75/0.94  
% 3.75/0.94  --sup_indices_passive                   []
% 3.75/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.94  --sup_full_bw                           [BwDemod]
% 3.75/0.94  --sup_immed_triv                        [TrivRules]
% 3.75/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.94  --sup_immed_bw_main                     []
% 3.75/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.94  
% 3.75/0.94  ------ Combination Options
% 3.75/0.94  
% 3.75/0.94  --comb_res_mult                         3
% 3.75/0.94  --comb_sup_mult                         2
% 3.75/0.94  --comb_inst_mult                        10
% 3.75/0.94  
% 3.75/0.94  ------ Debug Options
% 3.75/0.94  
% 3.75/0.94  --dbg_backtrace                         false
% 3.75/0.94  --dbg_dump_prop_clauses                 false
% 3.75/0.94  --dbg_dump_prop_clauses_file            -
% 3.75/0.94  --dbg_out_stat                          false
% 3.75/0.94  
% 3.75/0.94  
% 3.75/0.94  
% 3.75/0.94  
% 3.75/0.94  ------ Proving...
% 3.75/0.94  
% 3.75/0.94  
% 3.75/0.94  % SZS status Theorem for theBenchmark.p
% 3.75/0.94  
% 3.75/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/0.94  
% 3.75/0.94  fof(f2,axiom,(
% 3.75/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f32,plain,(
% 3.75/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.75/0.94    inference(ennf_transformation,[],[f2])).
% 3.75/0.94  
% 3.75/0.94  fof(f70,plain,(
% 3.75/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.75/0.94    inference(nnf_transformation,[],[f32])).
% 3.75/0.94  
% 3.75/0.94  fof(f71,plain,(
% 3.75/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.75/0.94    inference(rectify,[],[f70])).
% 3.75/0.94  
% 3.75/0.94  fof(f72,plain,(
% 3.75/0.94    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.75/0.94    introduced(choice_axiom,[])).
% 3.75/0.94  
% 3.75/0.94  fof(f73,plain,(
% 3.75/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.75/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f71,f72])).
% 3.75/0.94  
% 3.75/0.94  fof(f84,plain,(
% 3.75/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f73])).
% 3.75/0.94  
% 3.75/0.94  fof(f1,axiom,(
% 3.75/0.94    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f66,plain,(
% 3.75/0.94    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.75/0.94    inference(nnf_transformation,[],[f1])).
% 3.75/0.94  
% 3.75/0.94  fof(f67,plain,(
% 3.75/0.94    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.75/0.94    inference(rectify,[],[f66])).
% 3.75/0.94  
% 3.75/0.94  fof(f68,plain,(
% 3.75/0.94    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.75/0.94    introduced(choice_axiom,[])).
% 3.75/0.94  
% 3.75/0.94  fof(f69,plain,(
% 3.75/0.94    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.75/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f67,f68])).
% 3.75/0.94  
% 3.75/0.94  fof(f81,plain,(
% 3.75/0.94    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f69])).
% 3.75/0.94  
% 3.75/0.94  fof(f29,conjecture,(
% 3.75/0.94    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f30,negated_conjecture,(
% 3.75/0.94    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.75/0.94    inference(negated_conjecture,[],[f29])).
% 3.75/0.94  
% 3.75/0.94  fof(f64,plain,(
% 3.75/0.94    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.75/0.94    inference(ennf_transformation,[],[f30])).
% 3.75/0.94  
% 3.75/0.94  fof(f65,plain,(
% 3.75/0.94    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.75/0.94    inference(flattening,[],[f64])).
% 3.75/0.94  
% 3.75/0.94  fof(f79,plain,(
% 3.75/0.94    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.75/0.94    introduced(choice_axiom,[])).
% 3.75/0.94  
% 3.75/0.94  fof(f80,plain,(
% 3.75/0.94    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.75/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f65,f79])).
% 3.75/0.94  
% 3.75/0.94  fof(f135,plain,(
% 3.75/0.94    v2_funct_1(sK4)),
% 3.75/0.94    inference(cnf_transformation,[],[f80])).
% 3.75/0.94  
% 3.75/0.94  fof(f17,axiom,(
% 3.75/0.94    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f46,plain,(
% 3.75/0.94    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.75/0.94    inference(ennf_transformation,[],[f17])).
% 3.75/0.94  
% 3.75/0.94  fof(f47,plain,(
% 3.75/0.94    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.75/0.94    inference(flattening,[],[f46])).
% 3.75/0.94  
% 3.75/0.94  fof(f108,plain,(
% 3.75/0.94    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f47])).
% 3.75/0.94  
% 3.75/0.94  fof(f132,plain,(
% 3.75/0.94    v1_funct_1(sK4)),
% 3.75/0.94    inference(cnf_transformation,[],[f80])).
% 3.75/0.94  
% 3.75/0.94  fof(f134,plain,(
% 3.75/0.94    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.75/0.94    inference(cnf_transformation,[],[f80])).
% 3.75/0.94  
% 3.75/0.94  fof(f22,axiom,(
% 3.75/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f54,plain,(
% 3.75/0.94    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.94    inference(ennf_transformation,[],[f22])).
% 3.75/0.94  
% 3.75/0.94  fof(f116,plain,(
% 3.75/0.94    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/0.94    inference(cnf_transformation,[],[f54])).
% 3.75/0.94  
% 3.75/0.94  fof(f28,axiom,(
% 3.75/0.94    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f62,plain,(
% 3.75/0.94    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.75/0.94    inference(ennf_transformation,[],[f28])).
% 3.75/0.94  
% 3.75/0.94  fof(f63,plain,(
% 3.75/0.94    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.75/0.94    inference(flattening,[],[f62])).
% 3.75/0.94  
% 3.75/0.94  fof(f130,plain,(
% 3.75/0.94    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f63])).
% 3.75/0.94  
% 3.75/0.94  fof(f137,plain,(
% 3.75/0.94    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 3.75/0.94    inference(cnf_transformation,[],[f80])).
% 3.75/0.94  
% 3.75/0.94  fof(f18,axiom,(
% 3.75/0.94    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f48,plain,(
% 3.75/0.94    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.75/0.94    inference(ennf_transformation,[],[f18])).
% 3.75/0.94  
% 3.75/0.94  fof(f49,plain,(
% 3.75/0.94    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.75/0.94    inference(flattening,[],[f48])).
% 3.75/0.94  
% 3.75/0.94  fof(f110,plain,(
% 3.75/0.94    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f49])).
% 3.75/0.94  
% 3.75/0.94  fof(f21,axiom,(
% 3.75/0.94    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f52,plain,(
% 3.75/0.94    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.75/0.94    inference(ennf_transformation,[],[f21])).
% 3.75/0.94  
% 3.75/0.94  fof(f53,plain,(
% 3.75/0.94    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.75/0.94    inference(flattening,[],[f52])).
% 3.75/0.94  
% 3.75/0.94  fof(f114,plain,(
% 3.75/0.94    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f53])).
% 3.75/0.94  
% 3.75/0.94  fof(f25,axiom,(
% 3.75/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f57,plain,(
% 3.75/0.94    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.94    inference(ennf_transformation,[],[f25])).
% 3.75/0.94  
% 3.75/0.94  fof(f119,plain,(
% 3.75/0.94    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/0.94    inference(cnf_transformation,[],[f57])).
% 3.75/0.94  
% 3.75/0.94  fof(f136,plain,(
% 3.75/0.94    k2_relset_1(sK2,sK3,sK4) = sK3),
% 3.75/0.94    inference(cnf_transformation,[],[f80])).
% 3.75/0.94  
% 3.75/0.94  fof(f115,plain,(
% 3.75/0.94    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f53])).
% 3.75/0.94  
% 3.75/0.94  fof(f26,axiom,(
% 3.75/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f58,plain,(
% 3.75/0.94    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.94    inference(ennf_transformation,[],[f26])).
% 3.75/0.94  
% 3.75/0.94  fof(f59,plain,(
% 3.75/0.94    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.94    inference(flattening,[],[f58])).
% 3.75/0.94  
% 3.75/0.94  fof(f78,plain,(
% 3.75/0.94    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.94    inference(nnf_transformation,[],[f59])).
% 3.75/0.94  
% 3.75/0.94  fof(f120,plain,(
% 3.75/0.94    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/0.94    inference(cnf_transformation,[],[f78])).
% 3.75/0.94  
% 3.75/0.94  fof(f133,plain,(
% 3.75/0.94    v1_funct_2(sK4,sK2,sK3)),
% 3.75/0.94    inference(cnf_transformation,[],[f80])).
% 3.75/0.94  
% 3.75/0.94  fof(f24,axiom,(
% 3.75/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f56,plain,(
% 3.75/0.94    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/0.94    inference(ennf_transformation,[],[f24])).
% 3.75/0.94  
% 3.75/0.94  fof(f118,plain,(
% 3.75/0.94    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/0.94    inference(cnf_transformation,[],[f56])).
% 3.75/0.94  
% 3.75/0.94  fof(f27,axiom,(
% 3.75/0.94    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f60,plain,(
% 3.75/0.94    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.75/0.94    inference(ennf_transformation,[],[f27])).
% 3.75/0.94  
% 3.75/0.94  fof(f61,plain,(
% 3.75/0.94    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.75/0.94    inference(flattening,[],[f60])).
% 3.75/0.94  
% 3.75/0.94  fof(f127,plain,(
% 3.75/0.94    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f61])).
% 3.75/0.94  
% 3.75/0.94  fof(f128,plain,(
% 3.75/0.94    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f61])).
% 3.75/0.94  
% 3.75/0.94  fof(f109,plain,(
% 3.75/0.94    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f49])).
% 3.75/0.94  
% 3.75/0.94  fof(f131,plain,(
% 3.75/0.94    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f63])).
% 3.75/0.94  
% 3.75/0.94  fof(f9,axiom,(
% 3.75/0.94    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f36,plain,(
% 3.75/0.94    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 3.75/0.94    inference(ennf_transformation,[],[f9])).
% 3.75/0.94  
% 3.75/0.94  fof(f37,plain,(
% 3.75/0.94    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 3.75/0.94    inference(flattening,[],[f36])).
% 3.75/0.94  
% 3.75/0.94  fof(f96,plain,(
% 3.75/0.94    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f37])).
% 3.75/0.94  
% 3.75/0.94  fof(f7,axiom,(
% 3.75/0.94    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f34,plain,(
% 3.75/0.94    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 3.75/0.94    inference(ennf_transformation,[],[f7])).
% 3.75/0.94  
% 3.75/0.94  fof(f93,plain,(
% 3.75/0.94    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.75/0.94    inference(cnf_transformation,[],[f34])).
% 3.75/0.94  
% 3.75/0.94  fof(f3,axiom,(
% 3.75/0.94    v1_xboole_0(k1_xboole_0)),
% 3.75/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.94  
% 3.75/0.94  fof(f86,plain,(
% 3.75/0.94    v1_xboole_0(k1_xboole_0)),
% 3.75/0.94    inference(cnf_transformation,[],[f3])).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3,plain,
% 3.75/0.94      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f84]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3156,plain,
% 3.75/0.94      ( r1_tarski(X0,X1) = iProver_top
% 3.75/0.94      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_1,plain,
% 3.75/0.94      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.75/0.94      inference(cnf_transformation,[],[f81]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3158,plain,
% 3.75/0.94      ( r2_hidden(X0,X1) != iProver_top
% 3.75/0.94      | v1_xboole_0(X1) != iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_5225,plain,
% 3.75/0.94      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_3156,c_3158]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_53,negated_conjecture,
% 3.75/0.94      ( v2_funct_1(sK4) ),
% 3.75/0.94      inference(cnf_transformation,[],[f135]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3126,plain,
% 3.75/0.94      ( v2_funct_1(sK4) = iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_27,plain,
% 3.75/0.94      ( ~ v2_funct_1(X0)
% 3.75/0.94      | ~ v1_funct_1(X0)
% 3.75/0.94      | ~ v1_relat_1(X0)
% 3.75/0.94      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f108]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3139,plain,
% 3.75/0.94      ( k2_funct_1(X0) = k4_relat_1(X0)
% 3.75/0.94      | v2_funct_1(X0) != iProver_top
% 3.75/0.94      | v1_funct_1(X0) != iProver_top
% 3.75/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_8811,plain,
% 3.75/0.94      ( k2_funct_1(sK4) = k4_relat_1(sK4)
% 3.75/0.94      | v1_funct_1(sK4) != iProver_top
% 3.75/0.94      | v1_relat_1(sK4) != iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_3126,c_3139]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_56,negated_conjecture,
% 3.75/0.94      ( v1_funct_1(sK4) ),
% 3.75/0.94      inference(cnf_transformation,[],[f132]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_54,negated_conjecture,
% 3.75/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.75/0.94      inference(cnf_transformation,[],[f134]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_851,plain,
% 3.75/0.94      ( ~ v1_funct_1(X0)
% 3.75/0.94      | ~ v1_relat_1(X0)
% 3.75/0.94      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.75/0.94      | sK4 != X0 ),
% 3.75/0.94      inference(resolution_lifted,[status(thm)],[c_27,c_53]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_852,plain,
% 3.75/0.94      ( ~ v1_funct_1(sK4)
% 3.75/0.94      | ~ v1_relat_1(sK4)
% 3.75/0.94      | k2_funct_1(sK4) = k4_relat_1(sK4) ),
% 3.75/0.94      inference(unflattening,[status(thm)],[c_851]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_35,plain,
% 3.75/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.94      | v1_relat_1(X0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f116]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3774,plain,
% 3.75/0.94      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.75/0.94      | v1_relat_1(sK4) ),
% 3.75/0.94      inference(instantiation,[status(thm)],[c_35]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_4092,plain,
% 3.75/0.94      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.75/0.94      | v1_relat_1(sK4) ),
% 3.75/0.94      inference(instantiation,[status(thm)],[c_3774]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_9440,plain,
% 3.75/0.94      ( k2_funct_1(sK4) = k4_relat_1(sK4) ),
% 3.75/0.94      inference(global_propositional_subsumption,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_8811,c_56,c_54,c_852,c_4092]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_49,plain,
% 3.75/0.94      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.75/0.94      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.75/0.94      | ~ v1_funct_1(X0)
% 3.75/0.94      | ~ v1_relat_1(X0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f130]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_51,negated_conjecture,
% 3.75/0.94      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 3.75/0.94      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.75/0.94      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 3.75/0.94      inference(cnf_transformation,[],[f137]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_1217,plain,
% 3.75/0.94      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.75/0.94      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.75/0.94      | ~ v1_funct_1(X0)
% 3.75/0.94      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.75/0.94      | ~ v1_relat_1(X0)
% 3.75/0.94      | k2_funct_1(sK4) != X0
% 3.75/0.94      | k1_relat_1(X0) != sK3
% 3.75/0.94      | sK2 != X1 ),
% 3.75/0.94      inference(resolution_lifted,[status(thm)],[c_49,c_51]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_1218,plain,
% 3.75/0.94      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.75/0.94      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK2)
% 3.75/0.94      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.75/0.94      | ~ v1_relat_1(k2_funct_1(sK4))
% 3.75/0.94      | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
% 3.75/0.94      inference(unflattening,[status(thm)],[c_1217]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_1230,plain,
% 3.75/0.94      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.75/0.94      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK2)
% 3.75/0.94      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.75/0.94      | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
% 3.75/0.94      inference(forward_subsumption_resolution,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_1218,c_35]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3109,plain,
% 3.75/0.94      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.75/0.94      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.75/0.94      | r1_tarski(k2_relat_1(k2_funct_1(sK4)),sK2) != iProver_top
% 3.75/0.94      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_9446,plain,
% 3.75/0.94      ( k1_relat_1(k4_relat_1(sK4)) != sK3
% 3.75/0.94      | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.75/0.94      | r1_tarski(k2_relat_1(k4_relat_1(sK4)),sK2) != iProver_top
% 3.75/0.94      | v1_funct_1(k4_relat_1(sK4)) != iProver_top ),
% 3.75/0.94      inference(demodulation,[status(thm)],[c_9440,c_3109]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_57,plain,
% 3.75/0.94      ( v1_funct_1(sK4) = iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_59,plain,
% 3.75/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_4093,plain,
% 3.75/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.75/0.94      | v1_relat_1(sK4) = iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_4092]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_28,plain,
% 3.75/0.94      ( ~ v1_funct_1(X0)
% 3.75/0.94      | v1_funct_1(k2_funct_1(X0))
% 3.75/0.94      | ~ v1_relat_1(X0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f110]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3138,plain,
% 3.75/0.94      ( v1_funct_1(X0) != iProver_top
% 3.75/0.94      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.75/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_9496,plain,
% 3.75/0.94      ( v1_funct_1(k4_relat_1(sK4)) = iProver_top
% 3.75/0.94      | v1_funct_1(sK4) != iProver_top
% 3.75/0.94      | v1_relat_1(sK4) != iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_9440,c_3138]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_34,plain,
% 3.75/0.94      ( ~ v2_funct_1(X0)
% 3.75/0.94      | ~ v1_funct_1(X0)
% 3.75/0.94      | ~ v1_relat_1(X0)
% 3.75/0.94      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f114]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3132,plain,
% 3.75/0.94      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.75/0.94      | v2_funct_1(X0) != iProver_top
% 3.75/0.94      | v1_funct_1(X0) != iProver_top
% 3.75/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_9894,plain,
% 3.75/0.94      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 3.75/0.94      | v1_funct_1(sK4) != iProver_top
% 3.75/0.94      | v1_relat_1(sK4) != iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_3126,c_3132]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3125,plain,
% 3.75/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_38,plain,
% 3.75/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.94      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f119]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3129,plain,
% 3.75/0.94      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.75/0.94      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_6194,plain,
% 3.75/0.94      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_3125,c_3129]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_52,negated_conjecture,
% 3.75/0.94      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 3.75/0.94      inference(cnf_transformation,[],[f136]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_6196,plain,
% 3.75/0.94      ( k2_relat_1(sK4) = sK3 ),
% 3.75/0.94      inference(light_normalisation,[status(thm)],[c_6194,c_52]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_9923,plain,
% 3.75/0.94      ( k1_relat_1(k4_relat_1(sK4)) = sK3
% 3.75/0.94      | v1_funct_1(sK4) != iProver_top
% 3.75/0.94      | v1_relat_1(sK4) != iProver_top ),
% 3.75/0.94      inference(light_normalisation,[status(thm)],[c_9894,c_6196,c_9440]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_13522,plain,
% 3.75/0.94      ( r1_tarski(k2_relat_1(k4_relat_1(sK4)),sK2) != iProver_top
% 3.75/0.94      | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.75/0.94      inference(global_propositional_subsumption,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_9446,c_57,c_59,c_4093,c_9496,c_9923]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_13523,plain,
% 3.75/0.94      ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.75/0.94      | r1_tarski(k2_relat_1(k4_relat_1(sK4)),sK2) != iProver_top ),
% 3.75/0.94      inference(renaming,[status(thm)],[c_13522]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_33,plain,
% 3.75/0.94      ( ~ v2_funct_1(X0)
% 3.75/0.94      | ~ v1_funct_1(X0)
% 3.75/0.94      | ~ v1_relat_1(X0)
% 3.75/0.94      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f115]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3133,plain,
% 3.75/0.94      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.75/0.94      | v2_funct_1(X0) != iProver_top
% 3.75/0.94      | v1_funct_1(X0) != iProver_top
% 3.75/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_10059,plain,
% 3.75/0.94      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 3.75/0.94      | v1_funct_1(sK4) != iProver_top
% 3.75/0.94      | v1_relat_1(sK4) != iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_3126,c_3133]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_10088,plain,
% 3.75/0.94      ( k2_relat_1(k4_relat_1(sK4)) = k1_relat_1(sK4)
% 3.75/0.94      | v1_funct_1(sK4) != iProver_top
% 3.75/0.94      | v1_relat_1(sK4) != iProver_top ),
% 3.75/0.94      inference(light_normalisation,[status(thm)],[c_10059,c_9440]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_10667,plain,
% 3.75/0.94      ( k2_relat_1(k4_relat_1(sK4)) = k1_relat_1(sK4) ),
% 3.75/0.94      inference(global_propositional_subsumption,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_10088,c_57,c_59,c_4093]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_44,plain,
% 3.75/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 3.75/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.94      | k1_relset_1(X1,X2,X0) = X1
% 3.75/0.94      | k1_xboole_0 = X2 ),
% 3.75/0.94      inference(cnf_transformation,[],[f120]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_55,negated_conjecture,
% 3.75/0.94      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.75/0.94      inference(cnf_transformation,[],[f133]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_1187,plain,
% 3.75/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.94      | k1_relset_1(X1,X2,X0) = X1
% 3.75/0.94      | sK2 != X1
% 3.75/0.94      | sK3 != X2
% 3.75/0.94      | sK4 != X0
% 3.75/0.94      | k1_xboole_0 = X2 ),
% 3.75/0.94      inference(resolution_lifted,[status(thm)],[c_44,c_55]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_1188,plain,
% 3.75/0.94      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.75/0.94      | k1_relset_1(sK2,sK3,sK4) = sK2
% 3.75/0.94      | k1_xboole_0 = sK3 ),
% 3.75/0.94      inference(unflattening,[status(thm)],[c_1187]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_1190,plain,
% 3.75/0.94      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 3.75/0.94      inference(global_propositional_subsumption,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_1188,c_54]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_37,plain,
% 3.75/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/0.94      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f118]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3130,plain,
% 3.75/0.94      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.75/0.94      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_6900,plain,
% 3.75/0.94      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_3125,c_3130]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_7062,plain,
% 3.75/0.94      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_1190,c_6900]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_46,plain,
% 3.75/0.94      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.75/0.94      | ~ v1_funct_1(X0)
% 3.75/0.94      | ~ v1_relat_1(X0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f127]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_1198,plain,
% 3.75/0.94      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.75/0.94      | ~ v1_funct_1(X0)
% 3.75/0.94      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.75/0.94      | ~ v1_relat_1(X0)
% 3.75/0.94      | k2_funct_1(sK4) != X0
% 3.75/0.94      | k1_relat_1(X0) != sK3
% 3.75/0.94      | k2_relat_1(X0) != sK2 ),
% 3.75/0.94      inference(resolution_lifted,[status(thm)],[c_46,c_51]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_1199,plain,
% 3.75/0.94      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.75/0.94      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.75/0.94      | ~ v1_relat_1(k2_funct_1(sK4))
% 3.75/0.94      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.75/0.94      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 3.75/0.94      inference(unflattening,[status(thm)],[c_1198]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_1211,plain,
% 3.75/0.94      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.75/0.94      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.75/0.94      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.75/0.94      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 3.75/0.94      inference(forward_subsumption_resolution,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_1199,c_35]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3110,plain,
% 3.75/0.94      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.75/0.94      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.75/0.94      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.75/0.94      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_1211]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_9443,plain,
% 3.75/0.94      ( k1_relat_1(k4_relat_1(sK4)) != sK3
% 3.75/0.94      | k2_relat_1(k4_relat_1(sK4)) != sK2
% 3.75/0.94      | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.75/0.94      | v1_funct_1(k4_relat_1(sK4)) != iProver_top ),
% 3.75/0.94      inference(demodulation,[status(thm)],[c_9440,c_3110]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_12432,plain,
% 3.75/0.94      ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.75/0.94      | k2_relat_1(k4_relat_1(sK4)) != sK2 ),
% 3.75/0.94      inference(global_propositional_subsumption,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_9443,c_57,c_59,c_4093,c_9496,c_9923]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_12433,plain,
% 3.75/0.94      ( k2_relat_1(k4_relat_1(sK4)) != sK2
% 3.75/0.94      | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.75/0.94      inference(renaming,[status(thm)],[c_12432]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_12436,plain,
% 3.75/0.94      ( k1_relat_1(sK4) != sK2
% 3.75/0.94      | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.75/0.94      inference(light_normalisation,[status(thm)],[c_12433,c_10667]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_12440,plain,
% 3.75/0.94      ( sK3 = k1_xboole_0
% 3.75/0.94      | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_7062,c_12436]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_45,plain,
% 3.75/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.75/0.94      | ~ v1_funct_1(X0)
% 3.75/0.94      | ~ v1_relat_1(X0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f128]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3128,plain,
% 3.75/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.75/0.94      | v1_funct_1(X0) != iProver_top
% 3.75/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_10671,plain,
% 3.75/0.94      ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK4)),k1_relat_1(sK4)))) = iProver_top
% 3.75/0.94      | v1_funct_1(k4_relat_1(sK4)) != iProver_top
% 3.75/0.94      | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_10667,c_3128]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_10269,plain,
% 3.75/0.94      ( k1_relat_1(k4_relat_1(sK4)) = sK3 ),
% 3.75/0.94      inference(global_propositional_subsumption,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_9923,c_57,c_59,c_4093]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_10740,plain,
% 3.75/0.94      ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
% 3.75/0.94      | v1_funct_1(k4_relat_1(sK4)) != iProver_top
% 3.75/0.94      | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
% 3.75/0.94      inference(light_normalisation,[status(thm)],[c_10671,c_10269]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_29,plain,
% 3.75/0.94      ( ~ v1_funct_1(X0)
% 3.75/0.94      | ~ v1_relat_1(X0)
% 3.75/0.94      | v1_relat_1(k2_funct_1(X0)) ),
% 3.75/0.94      inference(cnf_transformation,[],[f109]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3137,plain,
% 3.75/0.94      ( v1_funct_1(X0) != iProver_top
% 3.75/0.94      | v1_relat_1(X0) != iProver_top
% 3.75/0.94      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_9497,plain,
% 3.75/0.94      ( v1_funct_1(sK4) != iProver_top
% 3.75/0.94      | v1_relat_1(k4_relat_1(sK4)) = iProver_top
% 3.75/0.94      | v1_relat_1(sK4) != iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_9440,c_3137]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_11149,plain,
% 3.75/0.94      ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 3.75/0.94      inference(global_propositional_subsumption,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_10740,c_57,c_59,c_4093,c_9496,c_9497]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_11154,plain,
% 3.75/0.94      ( sK3 = k1_xboole_0
% 3.75/0.94      | m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_7062,c_11149]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_12443,plain,
% 3.75/0.94      ( sK3 = k1_xboole_0 ),
% 3.75/0.94      inference(global_propositional_subsumption,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_12440,c_11154]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_13526,plain,
% 3.75/0.94      ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.75/0.94      | r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 3.75/0.94      inference(light_normalisation,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_13523,c_10667,c_12443]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_48,plain,
% 3.75/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.75/0.94      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.75/0.94      | ~ v1_funct_1(X0)
% 3.75/0.94      | ~ v1_relat_1(X0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f131]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3127,plain,
% 3.75/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.75/0.94      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.75/0.94      | v1_funct_1(X0) != iProver_top
% 3.75/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_10272,plain,
% 3.75/0.94      ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.75/0.94      | r1_tarski(k2_relat_1(k4_relat_1(sK4)),X0) != iProver_top
% 3.75/0.94      | v1_funct_1(k4_relat_1(sK4)) != iProver_top
% 3.75/0.94      | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_10269,c_3127]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_13392,plain,
% 3.75/0.94      ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.75/0.94      | r1_tarski(k2_relat_1(k4_relat_1(sK4)),X0) != iProver_top ),
% 3.75/0.94      inference(global_propositional_subsumption,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_10272,c_57,c_59,c_4093,c_9496,c_9497]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_13398,plain,
% 3.75/0.94      ( m1_subset_1(k4_relat_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 3.75/0.94      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 3.75/0.94      inference(light_normalisation,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_13392,c_10667,c_12443]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_13529,plain,
% 3.75/0.94      ( r1_tarski(k1_relat_1(sK4),sK2) != iProver_top ),
% 3.75/0.94      inference(forward_subsumption_resolution,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_13526,c_13398]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_14859,plain,
% 3.75/0.94      ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_5225,c_13529]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_15,plain,
% 3.75/0.94      ( ~ v1_relat_1(X0)
% 3.75/0.94      | v1_xboole_0(X0)
% 3.75/0.94      | ~ v1_xboole_0(k1_relat_1(X0)) ),
% 3.75/0.94      inference(cnf_transformation,[],[f96]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3145,plain,
% 3.75/0.94      ( v1_relat_1(X0) != iProver_top
% 3.75/0.94      | v1_xboole_0(X0) = iProver_top
% 3.75/0.94      | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_10274,plain,
% 3.75/0.94      ( v1_relat_1(k4_relat_1(sK4)) != iProver_top
% 3.75/0.94      | v1_xboole_0(k4_relat_1(sK4)) = iProver_top
% 3.75/0.94      | v1_xboole_0(sK3) != iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_10269,c_3145]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_10968,plain,
% 3.75/0.94      ( v1_xboole_0(k4_relat_1(sK4)) = iProver_top
% 3.75/0.94      | v1_xboole_0(sK3) != iProver_top ),
% 3.75/0.94      inference(global_propositional_subsumption,
% 3.75/0.94                [status(thm)],
% 3.75/0.94                [c_10274,c_57,c_59,c_4093,c_9497]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_12450,plain,
% 3.75/0.94      ( v1_xboole_0(k4_relat_1(sK4)) = iProver_top
% 3.75/0.94      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.75/0.94      inference(demodulation,[status(thm)],[c_12443,c_10968]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_12,plain,
% 3.75/0.94      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0)) ),
% 3.75/0.94      inference(cnf_transformation,[],[f93]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_3148,plain,
% 3.75/0.94      ( v1_xboole_0(X0) != iProver_top
% 3.75/0.94      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_10678,plain,
% 3.75/0.94      ( v1_xboole_0(k1_relat_1(sK4)) = iProver_top
% 3.75/0.94      | v1_xboole_0(k4_relat_1(sK4)) != iProver_top ),
% 3.75/0.94      inference(superposition,[status(thm)],[c_10667,c_3148]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_5,plain,
% 3.75/0.94      ( v1_xboole_0(k1_xboole_0) ),
% 3.75/0.94      inference(cnf_transformation,[],[f86]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(c_183,plain,
% 3.75/0.94      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.75/0.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.75/0.94  
% 3.75/0.94  cnf(contradiction,plain,
% 3.75/0.94      ( $false ),
% 3.75/0.94      inference(minisat,[status(thm)],[c_14859,c_12450,c_10678,c_183]) ).
% 3.75/0.94  
% 3.75/0.94  
% 3.75/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/0.94  
% 3.75/0.94  ------                               Statistics
% 3.75/0.94  
% 3.75/0.94  ------ General
% 3.75/0.94  
% 3.75/0.94  abstr_ref_over_cycles:                  0
% 3.75/0.94  abstr_ref_under_cycles:                 0
% 3.75/0.94  gc_basic_clause_elim:                   0
% 3.75/0.94  forced_gc_time:                         0
% 3.75/0.94  parsing_time:                           0.011
% 3.75/0.94  unif_index_cands_time:                  0.
% 3.75/0.94  unif_index_add_time:                    0.
% 3.75/0.94  orderings_time:                         0.
% 3.75/0.94  out_proof_time:                         0.012
% 3.75/0.94  total_time:                             0.375
% 3.75/0.94  num_of_symbols:                         57
% 3.75/0.94  num_of_terms:                           11328
% 3.75/0.94  
% 3.75/0.94  ------ Preprocessing
% 3.75/0.94  
% 3.75/0.94  num_of_splits:                          0
% 3.75/0.94  num_of_split_atoms:                     0
% 3.75/0.94  num_of_reused_defs:                     0
% 3.75/0.94  num_eq_ax_congr_red:                    28
% 3.75/0.94  num_of_sem_filtered_clauses:            1
% 3.75/0.94  num_of_subtypes:                        0
% 3.75/0.94  monotx_restored_types:                  0
% 3.75/0.94  sat_num_of_epr_types:                   0
% 3.75/0.94  sat_num_of_non_cyclic_types:            0
% 3.75/0.94  sat_guarded_non_collapsed_types:        0
% 3.75/0.94  num_pure_diseq_elim:                    0
% 3.75/0.94  simp_replaced_by:                       0
% 3.75/0.94  res_preprocessed:                       255
% 3.75/0.94  prep_upred:                             0
% 3.75/0.94  prep_unflattend:                        69
% 3.75/0.94  smt_new_axioms:                         0
% 3.75/0.94  pred_elim_cands:                        7
% 3.75/0.94  pred_elim:                              2
% 3.75/0.94  pred_elim_cl:                           -4
% 3.75/0.94  pred_elim_cycles:                       5
% 3.75/0.94  merged_defs:                            8
% 3.75/0.94  merged_defs_ncl:                        0
% 3.75/0.94  bin_hyper_res:                          8
% 3.75/0.94  prep_cycles:                            4
% 3.75/0.94  pred_elim_time:                         0.02
% 3.75/0.94  splitting_time:                         0.
% 3.75/0.94  sem_filter_time:                        0.
% 3.75/0.94  monotx_time:                            0.001
% 3.75/0.94  subtype_inf_time:                       0.
% 3.75/0.94  
% 3.75/0.94  ------ Problem properties
% 3.75/0.94  
% 3.75/0.94  clauses:                                56
% 3.75/0.94  conjectures:                            4
% 3.75/0.94  epr:                                    10
% 3.75/0.94  horn:                                   48
% 3.75/0.94  ground:                                 14
% 3.75/0.94  unary:                                  10
% 3.75/0.94  binary:                                 19
% 3.75/0.94  lits:                                   155
% 3.75/0.94  lits_eq:                                49
% 3.75/0.94  fd_pure:                                0
% 3.75/0.94  fd_pseudo:                              0
% 3.75/0.94  fd_cond:                                3
% 3.75/0.94  fd_pseudo_cond:                         1
% 3.75/0.94  ac_symbols:                             0
% 3.75/0.94  
% 3.75/0.94  ------ Propositional Solver
% 3.75/0.94  
% 3.75/0.94  prop_solver_calls:                      28
% 3.75/0.94  prop_fast_solver_calls:                 2136
% 3.75/0.94  smt_solver_calls:                       0
% 3.75/0.94  smt_fast_solver_calls:                  0
% 3.75/0.94  prop_num_of_clauses:                    5269
% 3.75/0.94  prop_preprocess_simplified:             15501
% 3.75/0.94  prop_fo_subsumed:                       107
% 3.75/0.94  prop_solver_time:                       0.
% 3.75/0.94  smt_solver_time:                        0.
% 3.75/0.94  smt_fast_solver_time:                   0.
% 3.75/0.94  prop_fast_solver_time:                  0.
% 3.75/0.94  prop_unsat_core_time:                   0.
% 3.75/0.94  
% 3.75/0.94  ------ QBF
% 3.75/0.94  
% 3.75/0.94  qbf_q_res:                              0
% 3.75/0.94  qbf_num_tautologies:                    0
% 3.75/0.94  qbf_prep_cycles:                        0
% 3.75/0.94  
% 3.75/0.94  ------ BMC1
% 3.75/0.94  
% 3.75/0.94  bmc1_current_bound:                     -1
% 3.75/0.94  bmc1_last_solved_bound:                 -1
% 3.75/0.94  bmc1_unsat_core_size:                   -1
% 3.75/0.94  bmc1_unsat_core_parents_size:           -1
% 3.75/0.94  bmc1_merge_next_fun:                    0
% 3.75/0.94  bmc1_unsat_core_clauses_time:           0.
% 3.75/0.94  
% 3.75/0.94  ------ Instantiation
% 3.75/0.94  
% 3.75/0.94  inst_num_of_clauses:                    1633
% 3.75/0.94  inst_num_in_passive:                    663
% 3.75/0.94  inst_num_in_active:                     567
% 3.75/0.94  inst_num_in_unprocessed:                404
% 3.75/0.94  inst_num_of_loops:                      780
% 3.75/0.94  inst_num_of_learning_restarts:          0
% 3.75/0.94  inst_num_moves_active_passive:          211
% 3.75/0.94  inst_lit_activity:                      0
% 3.75/0.94  inst_lit_activity_moves:                0
% 3.75/0.94  inst_num_tautologies:                   0
% 3.75/0.94  inst_num_prop_implied:                  0
% 3.75/0.94  inst_num_existing_simplified:           0
% 3.75/0.94  inst_num_eq_res_simplified:             0
% 3.75/0.94  inst_num_child_elim:                    0
% 3.75/0.94  inst_num_of_dismatching_blockings:      730
% 3.75/0.94  inst_num_of_non_proper_insts:           1632
% 3.75/0.94  inst_num_of_duplicates:                 0
% 3.75/0.94  inst_inst_num_from_inst_to_res:         0
% 3.75/0.94  inst_dismatching_checking_time:         0.
% 3.75/0.94  
% 3.75/0.94  ------ Resolution
% 3.75/0.94  
% 3.75/0.94  res_num_of_clauses:                     0
% 3.75/0.94  res_num_in_passive:                     0
% 3.75/0.94  res_num_in_active:                      0
% 3.75/0.94  res_num_of_loops:                       259
% 3.75/0.94  res_forward_subset_subsumed:            93
% 3.75/0.94  res_backward_subset_subsumed:           4
% 3.75/0.94  res_forward_subsumed:                   0
% 3.75/0.94  res_backward_subsumed:                  0
% 3.75/0.94  res_forward_subsumption_resolution:     9
% 3.75/0.94  res_backward_subsumption_resolution:    0
% 3.75/0.94  res_clause_to_clause_subsumption:       650
% 3.75/0.94  res_orphan_elimination:                 0
% 3.75/0.94  res_tautology_del:                      128
% 3.75/0.94  res_num_eq_res_simplified:              0
% 3.75/0.94  res_num_sel_changes:                    0
% 3.75/0.94  res_moves_from_active_to_pass:          0
% 3.75/0.94  
% 3.75/0.94  ------ Superposition
% 3.75/0.94  
% 3.75/0.94  sup_time_total:                         0.
% 3.75/0.94  sup_time_generating:                    0.
% 3.75/0.94  sup_time_sim_full:                      0.
% 3.75/0.94  sup_time_sim_immed:                     0.
% 3.75/0.94  
% 3.75/0.94  sup_num_of_clauses:                     248
% 3.75/0.94  sup_num_in_active:                      107
% 3.75/0.94  sup_num_in_passive:                     141
% 3.75/0.94  sup_num_of_loops:                       155
% 3.75/0.94  sup_fw_superposition:                   103
% 3.75/0.94  sup_bw_superposition:                   200
% 3.75/0.94  sup_immediate_simplified:               113
% 3.75/0.94  sup_given_eliminated:                   0
% 3.75/0.94  comparisons_done:                       0
% 3.75/0.94  comparisons_avoided:                    8
% 3.75/0.94  
% 3.75/0.94  ------ Simplifications
% 3.75/0.94  
% 3.75/0.94  
% 3.75/0.94  sim_fw_subset_subsumed:                 35
% 3.75/0.94  sim_bw_subset_subsumed:                 8
% 3.75/0.94  sim_fw_subsumed:                        9
% 3.75/0.94  sim_bw_subsumed:                        1
% 3.75/0.94  sim_fw_subsumption_res:                 3
% 3.75/0.94  sim_bw_subsumption_res:                 1
% 3.75/0.94  sim_tautology_del:                      7
% 3.75/0.94  sim_eq_tautology_del:                   6
% 3.75/0.94  sim_eq_res_simp:                        2
% 3.75/0.94  sim_fw_demodulated:                     10
% 3.75/0.94  sim_bw_demodulated:                     48
% 3.75/0.94  sim_light_normalised:                   67
% 3.75/0.94  sim_joinable_taut:                      0
% 3.75/0.94  sim_joinable_simp:                      0
% 3.75/0.94  sim_ac_normalised:                      0
% 3.75/0.94  sim_smt_subsumption:                    0
% 3.75/0.94  
%------------------------------------------------------------------------------

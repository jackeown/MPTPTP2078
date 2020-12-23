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
% DateTime   : Thu Dec  3 12:00:36 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  279 (13819 expanded)
%              Number of clauses        :  198 (5356 expanded)
%              Number of leaves         :   24 (2577 expanded)
%              Depth                    :   31
%              Number of atoms          :  800 (63103 expanded)
%              Number of equality atoms :  486 (20571 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
        | ~ v1_funct_2(sK6,sK3,sK5)
        | ~ v1_funct_1(sK6) )
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 != sK4 )
      & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
      | ~ v1_funct_2(sK6,sK3,sK5)
      | ~ v1_funct_1(sK6) )
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f32,f50])).

fof(f83,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_2(sK6,sK3,sK5)
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f95,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f41])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f86,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f96,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK3 != X1
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_34])).

cnf(c_520,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_522,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_33])).

cnf(c_1510,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1514,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3436,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1510,c_1514])).

cnf(c_3702,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_522,c_3436])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1512,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1521,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1513,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3281,plain,
    ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1510,c_1513])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1511,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3615,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3281,c_1511])).

cnf(c_3435,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1514])).

cnf(c_7485,plain,
    ( k1_relset_1(X0,sK5,sK6) = k1_relat_1(sK6)
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3615,c_3435])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1519,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2633,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_1519])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_254,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_255,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_254])).

cnf(c_319,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_255])).

cnf(c_1508,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_2646,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2633,c_1508])).

cnf(c_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1517,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2651,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2646,c_1517])).

cnf(c_7742,plain,
    ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | k1_relset_1(X0,sK5,sK6) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7485,c_2651])).

cnf(c_7743,plain,
    ( k1_relset_1(X0,sK5,sK6) = k1_relat_1(sK6)
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7742])).

cnf(c_7753,plain,
    ( k1_relset_1(X0,sK5,sK6) = k1_relat_1(sK6)
    | sK4 = k1_xboole_0
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_7743])).

cnf(c_7788,plain,
    ( k1_relset_1(sK3,sK5,sK6) = k1_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1521,c_7753])).

cnf(c_27,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(sK6,sK3,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_179,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_2(sK6,sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_35])).

cnf(c_180,negated_conjecture,
    ( ~ v1_funct_2(sK6,sK3,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK5 != X2
    | sK3 != X1
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_180])).

cnf(c_507,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | k1_relset_1(sK3,sK5,sK6) != sK3
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_1503,plain,
    ( k1_relset_1(sK3,sK5,sK6) != sK3
    | k1_xboole_0 = sK5
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_8232,plain,
    ( k1_relat_1(sK6) != sK3
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7788,c_1503])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_102,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1526,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_318,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_15,c_255])).

cnf(c_1509,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_2890,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_1509])).

cnf(c_5864,plain,
    ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3615,c_2890])).

cnf(c_3280,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1513])).

cnf(c_6567,plain,
    ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5864,c_3280])).

cnf(c_7299,plain,
    ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
    | v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6567,c_2651])).

cnf(c_7300,plain,
    ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_7299])).

cnf(c_7311,plain,
    ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
    | sK4 = k1_xboole_0
    | r1_tarski(sK3,X0) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_7300])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_90,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_91,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK5 != X1
    | sK3 != k1_xboole_0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_180])).

cnf(c_478,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
    | k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_1505,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_1668,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1505,c_11])).

cnf(c_1767,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ r1_tarski(sK6,k2_zfmisc_1(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1768,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) = iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1767])).

cnf(c_1828,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK5))
    | r2_hidden(sK1(sK6,k2_zfmisc_1(sK3,sK5)),sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1835,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK5)) = iProver_top
    | r2_hidden(sK1(sK6,k2_zfmisc_1(sK3,sK5)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1828])).

cnf(c_835,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1793,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_1860,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_834,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1861,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_1973,plain,
    ( k1_relset_1(sK3,sK5,sK6) != X0
    | k1_relset_1(sK3,sK5,sK6) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_2270,plain,
    ( k1_relset_1(sK3,sK5,sK6) != k1_relat_1(sK6)
    | k1_relset_1(sK3,sK5,sK6) = sK3
    | sK3 != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_2271,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | k1_relset_1(sK3,sK5,sK6) = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2272,plain,
    ( k1_relset_1(sK3,sK5,sK6) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2271])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2589,plain,
    ( r2_hidden(sK2(sK3),sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2590,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(sK2(sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2589])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2662,plain,
    ( ~ r2_hidden(sK1(sK6,k2_zfmisc_1(sK3,sK5)),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2670,plain,
    ( ~ r1_tarski(sK6,X0)
    | ~ r2_hidden(sK1(sK6,k2_zfmisc_1(sK3,sK5)),sK6)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_2671,plain,
    ( r1_tarski(sK6,X0) != iProver_top
    | r2_hidden(sK1(sK6,k2_zfmisc_1(sK3,sK5)),sK6) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2670])).

cnf(c_2673,plain,
    ( r1_tarski(sK6,k1_xboole_0) != iProver_top
    | r2_hidden(sK1(sK6,k2_zfmisc_1(sK3,sK5)),sK6) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_2918,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1518,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3732,plain,
    ( sK4 = k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_1518])).

cnf(c_3723,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) != X0
    | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_3901,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_relset_1(X0,X1,X2)
    | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
    | k1_xboole_0 != k1_relset_1(X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_3723])).

cnf(c_3903,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3901])).

cnf(c_843,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k1_relset_1(X0,X2,X4) = k1_relset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_3902,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) = k1_relset_1(X0,X1,X2)
    | sK5 != X1
    | sK6 != X2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_3904,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | sK5 != k1_xboole_0
    | sK6 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3902])).

cnf(c_836,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4167,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_4169,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4167])).

cnf(c_2610,plain,
    ( sK5 != X0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_4202,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2610])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1529,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2313,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_1509])).

cnf(c_4279,plain,
    ( v1_xboole_0(k2_relat_1(sK6)) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3615,c_2313])).

cnf(c_1856,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_2826,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1856])).

cnf(c_4312,plain,
    ( k1_relat_1(sK6) != sK3
    | sK3 = k1_relat_1(sK6)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2826])).

cnf(c_1520,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3437,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1514])).

cnf(c_3609,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1520,c_3437])).

cnf(c_4481,plain,
    ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1521,c_3609])).

cnf(c_1524,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1523,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1528,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2319,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_1528])).

cnf(c_2412,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_2319])).

cnf(c_2423,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1524,c_2412])).

cnf(c_4483,plain,
    ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4481,c_2423])).

cnf(c_4492,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4483])).

cnf(c_2889,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_1528])).

cnf(c_2727,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1512])).

cnf(c_3963,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_2727])).

cnf(c_4185,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3963,c_2651])).

cnf(c_4186,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4185])).

cnf(c_4195,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2889,c_4186])).

cnf(c_5678,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_4195])).

cnf(c_2729,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_1519])).

cnf(c_4931,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_2729])).

cnf(c_4997,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK6,k1_xboole_0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_4931])).

cnf(c_5252,plain,
    ( r1_tarski(sK6,k1_xboole_0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4997,c_2651])).

cnf(c_5253,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5252])).

cnf(c_5262,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK6,k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2889,c_5253])).

cnf(c_5645,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_5262])).

cnf(c_5835,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4279,c_5645])).

cnf(c_2188,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_1509])).

cnf(c_6432,plain,
    ( sK4 = k1_xboole_0
    | sK6 = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5835,c_2188])).

cnf(c_6430,plain,
    ( sK4 = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5835,c_2313])).

cnf(c_7401,plain,
    ( k1_relset_1(X0,X1,X2) != X3
    | k1_xboole_0 != X3
    | k1_xboole_0 = k1_relset_1(X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_7402,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7401])).

cnf(c_7453,plain,
    ( ~ r2_hidden(sK2(sK3),sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7454,plain,
    ( r2_hidden(sK2(sK3),sK3) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7453])).

cnf(c_7471,plain,
    ( sK4 = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7311,c_90,c_91,c_5,c_102,c_507,c_1668,c_1767,c_1768,c_1828,c_1835,c_1860,c_1861,c_2270,c_2272,c_2590,c_2662,c_2673,c_2918,c_3702,c_3732,c_3903,c_3904,c_4169,c_4202,c_4279,c_4312,c_4492,c_5678,c_5835,c_6432,c_6430,c_7402,c_7454])).

cnf(c_8061,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_8062,plain,
    ( sK5 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8061])).

cnf(c_8064,plain,
    ( sK5 != k1_xboole_0
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8062])).

cnf(c_8376,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8232,c_102,c_3702,c_7471,c_8064])).

cnf(c_8383,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
    | r1_tarski(k1_relat_1(sK6),sK3) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1512,c_8376])).

cnf(c_8490,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8383,c_2651,c_3615])).

cnf(c_8491,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK6),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_8490])).

cnf(c_8497,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_8491])).

cnf(c_8605,plain,
    ( sK4 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8497,c_1521])).

cnf(c_8616,plain,
    ( k1_relset_1(sK3,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_8605,c_3436])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_8624,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8605,c_31])).

cnf(c_8625,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8624])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK4 != X1
    | sK3 != k1_xboole_0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_34])).

cnf(c_494,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
    | k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_1504,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_1644,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1504,c_11])).

cnf(c_8620,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8605,c_1644])).

cnf(c_8638,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8620,c_8625])).

cnf(c_8639,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8638])).

cnf(c_8623,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8605,c_1510])).

cnf(c_8628,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8623,c_8625])).

cnf(c_8630,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8628,c_11])).

cnf(c_8642,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8639,c_8630])).

cnf(c_8652,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8616,c_8625,c_8642])).

cnf(c_6384,plain,
    ( ~ r1_tarski(sK6,X0)
    | ~ r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_6385,plain,
    ( r1_tarski(sK6,X0) != iProver_top
    | r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6384])).

cnf(c_6387,plain,
    ( r1_tarski(sK6,k1_xboole_0) != iProver_top
    | r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6385])).

cnf(c_4448,plain,
    ( X0 != X1
    | X0 = k1_relat_1(sK6)
    | k1_relat_1(sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_4449,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4448])).

cnf(c_3896,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
    | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3897,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) = k1_relat_1(sK6)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3896])).

cnf(c_3895,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_relat_1(sK6)
    | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3723])).

cnf(c_2690,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | r1_tarski(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2691,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2690])).

cnf(c_2693,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2691])).

cnf(c_2603,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_2604,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2603])).

cnf(c_1897,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2208,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK5))
    | r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6) ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_2212,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK5)) = iProver_top
    | r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2208])).

cnf(c_1796,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2076,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
    | ~ r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK5)) ),
    inference(instantiation,[status(thm)],[c_1796])).

cnf(c_2077,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) = iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2076])).

cnf(c_479,plain,
    ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8652,c_8630,c_8605,c_6387,c_4449,c_3897,c_3895,c_2693,c_2673,c_2604,c_2212,c_2077,c_1861,c_1860,c_1835,c_1768,c_479,c_102,c_91,c_90,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.26/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/0.99  
% 3.26/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.26/0.99  
% 3.26/0.99  ------  iProver source info
% 3.26/0.99  
% 3.26/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.26/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.26/0.99  git: non_committed_changes: false
% 3.26/0.99  git: last_make_outside_of_git: false
% 3.26/0.99  
% 3.26/0.99  ------ 
% 3.26/0.99  
% 3.26/0.99  ------ Input Options
% 3.26/0.99  
% 3.26/0.99  --out_options                           all
% 3.26/0.99  --tptp_safe_out                         true
% 3.26/0.99  --problem_path                          ""
% 3.26/0.99  --include_path                          ""
% 3.26/0.99  --clausifier                            res/vclausify_rel
% 3.26/0.99  --clausifier_options                    --mode clausify
% 3.26/0.99  --stdin                                 false
% 3.26/0.99  --stats_out                             all
% 3.26/0.99  
% 3.26/0.99  ------ General Options
% 3.26/0.99  
% 3.26/0.99  --fof                                   false
% 3.26/0.99  --time_out_real                         305.
% 3.26/0.99  --time_out_virtual                      -1.
% 3.26/0.99  --symbol_type_check                     false
% 3.26/0.99  --clausify_out                          false
% 3.26/0.99  --sig_cnt_out                           false
% 3.26/0.99  --trig_cnt_out                          false
% 3.26/0.99  --trig_cnt_out_tolerance                1.
% 3.26/0.99  --trig_cnt_out_sk_spl                   false
% 3.26/0.99  --abstr_cl_out                          false
% 3.26/0.99  
% 3.26/0.99  ------ Global Options
% 3.26/0.99  
% 3.26/0.99  --schedule                              default
% 3.26/0.99  --add_important_lit                     false
% 3.26/0.99  --prop_solver_per_cl                    1000
% 3.26/0.99  --min_unsat_core                        false
% 3.26/0.99  --soft_assumptions                      false
% 3.26/0.99  --soft_lemma_size                       3
% 3.26/0.99  --prop_impl_unit_size                   0
% 3.26/0.99  --prop_impl_unit                        []
% 3.26/0.99  --share_sel_clauses                     true
% 3.26/0.99  --reset_solvers                         false
% 3.26/0.99  --bc_imp_inh                            [conj_cone]
% 3.26/0.99  --conj_cone_tolerance                   3.
% 3.26/0.99  --extra_neg_conj                        none
% 3.26/0.99  --large_theory_mode                     true
% 3.26/0.99  --prolific_symb_bound                   200
% 3.26/0.99  --lt_threshold                          2000
% 3.26/0.99  --clause_weak_htbl                      true
% 3.26/0.99  --gc_record_bc_elim                     false
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing Options
% 3.26/0.99  
% 3.26/0.99  --preprocessing_flag                    true
% 3.26/0.99  --time_out_prep_mult                    0.1
% 3.26/0.99  --splitting_mode                        input
% 3.26/0.99  --splitting_grd                         true
% 3.26/0.99  --splitting_cvd                         false
% 3.26/0.99  --splitting_cvd_svl                     false
% 3.26/0.99  --splitting_nvd                         32
% 3.26/0.99  --sub_typing                            true
% 3.26/0.99  --prep_gs_sim                           true
% 3.26/0.99  --prep_unflatten                        true
% 3.26/0.99  --prep_res_sim                          true
% 3.26/0.99  --prep_upred                            true
% 3.26/0.99  --prep_sem_filter                       exhaustive
% 3.26/0.99  --prep_sem_filter_out                   false
% 3.26/0.99  --pred_elim                             true
% 3.26/0.99  --res_sim_input                         true
% 3.26/0.99  --eq_ax_congr_red                       true
% 3.26/0.99  --pure_diseq_elim                       true
% 3.26/0.99  --brand_transform                       false
% 3.26/0.99  --non_eq_to_eq                          false
% 3.26/0.99  --prep_def_merge                        true
% 3.26/0.99  --prep_def_merge_prop_impl              false
% 3.26/0.99  --prep_def_merge_mbd                    true
% 3.26/0.99  --prep_def_merge_tr_red                 false
% 3.26/0.99  --prep_def_merge_tr_cl                  false
% 3.26/0.99  --smt_preprocessing                     true
% 3.26/0.99  --smt_ac_axioms                         fast
% 3.26/0.99  --preprocessed_out                      false
% 3.26/0.99  --preprocessed_stats                    false
% 3.26/0.99  
% 3.26/0.99  ------ Abstraction refinement Options
% 3.26/0.99  
% 3.26/0.99  --abstr_ref                             []
% 3.26/0.99  --abstr_ref_prep                        false
% 3.26/0.99  --abstr_ref_until_sat                   false
% 3.26/0.99  --abstr_ref_sig_restrict                funpre
% 3.26/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.99  --abstr_ref_under                       []
% 3.26/0.99  
% 3.26/0.99  ------ SAT Options
% 3.26/0.99  
% 3.26/0.99  --sat_mode                              false
% 3.26/0.99  --sat_fm_restart_options                ""
% 3.26/0.99  --sat_gr_def                            false
% 3.26/0.99  --sat_epr_types                         true
% 3.26/0.99  --sat_non_cyclic_types                  false
% 3.26/0.99  --sat_finite_models                     false
% 3.26/0.99  --sat_fm_lemmas                         false
% 3.26/0.99  --sat_fm_prep                           false
% 3.26/0.99  --sat_fm_uc_incr                        true
% 3.26/0.99  --sat_out_model                         small
% 3.26/0.99  --sat_out_clauses                       false
% 3.26/0.99  
% 3.26/0.99  ------ QBF Options
% 3.26/0.99  
% 3.26/0.99  --qbf_mode                              false
% 3.26/0.99  --qbf_elim_univ                         false
% 3.26/0.99  --qbf_dom_inst                          none
% 3.26/0.99  --qbf_dom_pre_inst                      false
% 3.26/0.99  --qbf_sk_in                             false
% 3.26/0.99  --qbf_pred_elim                         true
% 3.26/0.99  --qbf_split                             512
% 3.26/0.99  
% 3.26/0.99  ------ BMC1 Options
% 3.26/0.99  
% 3.26/0.99  --bmc1_incremental                      false
% 3.26/0.99  --bmc1_axioms                           reachable_all
% 3.26/0.99  --bmc1_min_bound                        0
% 3.26/0.99  --bmc1_max_bound                        -1
% 3.26/0.99  --bmc1_max_bound_default                -1
% 3.26/0.99  --bmc1_symbol_reachability              true
% 3.26/0.99  --bmc1_property_lemmas                  false
% 3.26/0.99  --bmc1_k_induction                      false
% 3.26/0.99  --bmc1_non_equiv_states                 false
% 3.26/0.99  --bmc1_deadlock                         false
% 3.26/0.99  --bmc1_ucm                              false
% 3.26/0.99  --bmc1_add_unsat_core                   none
% 3.26/0.99  --bmc1_unsat_core_children              false
% 3.26/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.99  --bmc1_out_stat                         full
% 3.26/0.99  --bmc1_ground_init                      false
% 3.26/0.99  --bmc1_pre_inst_next_state              false
% 3.26/0.99  --bmc1_pre_inst_state                   false
% 3.26/0.99  --bmc1_pre_inst_reach_state             false
% 3.26/0.99  --bmc1_out_unsat_core                   false
% 3.26/0.99  --bmc1_aig_witness_out                  false
% 3.26/0.99  --bmc1_verbose                          false
% 3.26/0.99  --bmc1_dump_clauses_tptp                false
% 3.26/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.99  --bmc1_dump_file                        -
% 3.26/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.99  --bmc1_ucm_extend_mode                  1
% 3.26/0.99  --bmc1_ucm_init_mode                    2
% 3.26/0.99  --bmc1_ucm_cone_mode                    none
% 3.26/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.99  --bmc1_ucm_relax_model                  4
% 3.26/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.99  --bmc1_ucm_layered_model                none
% 3.26/0.99  --bmc1_ucm_max_lemma_size               10
% 3.26/0.99  
% 3.26/0.99  ------ AIG Options
% 3.26/0.99  
% 3.26/0.99  --aig_mode                              false
% 3.26/0.99  
% 3.26/0.99  ------ Instantiation Options
% 3.26/0.99  
% 3.26/0.99  --instantiation_flag                    true
% 3.26/0.99  --inst_sos_flag                         false
% 3.26/0.99  --inst_sos_phase                        true
% 3.26/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel_side                     num_symb
% 3.26/0.99  --inst_solver_per_active                1400
% 3.26/0.99  --inst_solver_calls_frac                1.
% 3.26/0.99  --inst_passive_queue_type               priority_queues
% 3.26/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.99  --inst_passive_queues_freq              [25;2]
% 3.26/0.99  --inst_dismatching                      true
% 3.26/0.99  --inst_eager_unprocessed_to_passive     true
% 3.26/0.99  --inst_prop_sim_given                   true
% 3.26/0.99  --inst_prop_sim_new                     false
% 3.26/0.99  --inst_subs_new                         false
% 3.26/0.99  --inst_eq_res_simp                      false
% 3.26/0.99  --inst_subs_given                       false
% 3.26/0.99  --inst_orphan_elimination               true
% 3.26/0.99  --inst_learning_loop_flag               true
% 3.26/0.99  --inst_learning_start                   3000
% 3.26/0.99  --inst_learning_factor                  2
% 3.26/0.99  --inst_start_prop_sim_after_learn       3
% 3.26/0.99  --inst_sel_renew                        solver
% 3.26/0.99  --inst_lit_activity_flag                true
% 3.26/0.99  --inst_restr_to_given                   false
% 3.26/0.99  --inst_activity_threshold               500
% 3.26/0.99  --inst_out_proof                        true
% 3.26/0.99  
% 3.26/0.99  ------ Resolution Options
% 3.26/0.99  
% 3.26/0.99  --resolution_flag                       true
% 3.26/0.99  --res_lit_sel                           adaptive
% 3.26/0.99  --res_lit_sel_side                      none
% 3.26/0.99  --res_ordering                          kbo
% 3.26/0.99  --res_to_prop_solver                    active
% 3.26/0.99  --res_prop_simpl_new                    false
% 3.26/0.99  --res_prop_simpl_given                  true
% 3.26/0.99  --res_passive_queue_type                priority_queues
% 3.26/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.99  --res_passive_queues_freq               [15;5]
% 3.26/0.99  --res_forward_subs                      full
% 3.26/0.99  --res_backward_subs                     full
% 3.26/0.99  --res_forward_subs_resolution           true
% 3.26/0.99  --res_backward_subs_resolution          true
% 3.26/0.99  --res_orphan_elimination                true
% 3.26/0.99  --res_time_limit                        2.
% 3.26/0.99  --res_out_proof                         true
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Options
% 3.26/0.99  
% 3.26/0.99  --superposition_flag                    true
% 3.26/0.99  --sup_passive_queue_type                priority_queues
% 3.26/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.99  --demod_completeness_check              fast
% 3.26/0.99  --demod_use_ground                      true
% 3.26/0.99  --sup_to_prop_solver                    passive
% 3.26/0.99  --sup_prop_simpl_new                    true
% 3.26/0.99  --sup_prop_simpl_given                  true
% 3.26/0.99  --sup_fun_splitting                     false
% 3.26/0.99  --sup_smt_interval                      50000
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Simplification Setup
% 3.26/0.99  
% 3.26/0.99  --sup_indices_passive                   []
% 3.26/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_full_bw                           [BwDemod]
% 3.26/0.99  --sup_immed_triv                        [TrivRules]
% 3.26/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_immed_bw_main                     []
% 3.26/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  
% 3.26/0.99  ------ Combination Options
% 3.26/0.99  
% 3.26/0.99  --comb_res_mult                         3
% 3.26/0.99  --comb_sup_mult                         2
% 3.26/0.99  --comb_inst_mult                        10
% 3.26/0.99  
% 3.26/0.99  ------ Debug Options
% 3.26/0.99  
% 3.26/0.99  --dbg_backtrace                         false
% 3.26/0.99  --dbg_dump_prop_clauses                 false
% 3.26/0.99  --dbg_dump_prop_clauses_file            -
% 3.26/0.99  --dbg_out_stat                          false
% 3.26/0.99  ------ Parsing...
% 3.26/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.26/0.99  ------ Proving...
% 3.26/0.99  ------ Problem Properties 
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  clauses                                 33
% 3.26/0.99  conjectures                             3
% 3.26/0.99  EPR                                     8
% 3.26/0.99  Horn                                    27
% 3.26/0.99  unary                                   7
% 3.26/0.99  binary                                  13
% 3.26/0.99  lits                                    77
% 3.26/0.99  lits eq                                 30
% 3.26/0.99  fd_pure                                 0
% 3.26/0.99  fd_pseudo                               0
% 3.26/0.99  fd_cond                                 2
% 3.26/0.99  fd_pseudo_cond                          1
% 3.26/0.99  AC symbols                              0
% 3.26/0.99  
% 3.26/0.99  ------ Schedule dynamic 5 is on 
% 3.26/0.99  
% 3.26/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  ------ 
% 3.26/0.99  Current options:
% 3.26/0.99  ------ 
% 3.26/0.99  
% 3.26/0.99  ------ Input Options
% 3.26/0.99  
% 3.26/0.99  --out_options                           all
% 3.26/0.99  --tptp_safe_out                         true
% 3.26/0.99  --problem_path                          ""
% 3.26/0.99  --include_path                          ""
% 3.26/0.99  --clausifier                            res/vclausify_rel
% 3.26/0.99  --clausifier_options                    --mode clausify
% 3.26/0.99  --stdin                                 false
% 3.26/0.99  --stats_out                             all
% 3.26/1.00  
% 3.26/1.00  ------ General Options
% 3.26/1.00  
% 3.26/1.00  --fof                                   false
% 3.26/1.00  --time_out_real                         305.
% 3.26/1.00  --time_out_virtual                      -1.
% 3.26/1.00  --symbol_type_check                     false
% 3.26/1.00  --clausify_out                          false
% 3.26/1.00  --sig_cnt_out                           false
% 3.26/1.00  --trig_cnt_out                          false
% 3.26/1.00  --trig_cnt_out_tolerance                1.
% 3.26/1.00  --trig_cnt_out_sk_spl                   false
% 3.26/1.00  --abstr_cl_out                          false
% 3.26/1.00  
% 3.26/1.00  ------ Global Options
% 3.26/1.00  
% 3.26/1.00  --schedule                              default
% 3.26/1.00  --add_important_lit                     false
% 3.26/1.00  --prop_solver_per_cl                    1000
% 3.26/1.00  --min_unsat_core                        false
% 3.26/1.00  --soft_assumptions                      false
% 3.26/1.00  --soft_lemma_size                       3
% 3.26/1.00  --prop_impl_unit_size                   0
% 3.26/1.00  --prop_impl_unit                        []
% 3.26/1.00  --share_sel_clauses                     true
% 3.26/1.00  --reset_solvers                         false
% 3.26/1.00  --bc_imp_inh                            [conj_cone]
% 3.26/1.00  --conj_cone_tolerance                   3.
% 3.26/1.00  --extra_neg_conj                        none
% 3.26/1.00  --large_theory_mode                     true
% 3.26/1.00  --prolific_symb_bound                   200
% 3.26/1.00  --lt_threshold                          2000
% 3.26/1.00  --clause_weak_htbl                      true
% 3.26/1.00  --gc_record_bc_elim                     false
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing Options
% 3.26/1.00  
% 3.26/1.00  --preprocessing_flag                    true
% 3.26/1.00  --time_out_prep_mult                    0.1
% 3.26/1.00  --splitting_mode                        input
% 3.26/1.00  --splitting_grd                         true
% 3.26/1.00  --splitting_cvd                         false
% 3.26/1.00  --splitting_cvd_svl                     false
% 3.26/1.00  --splitting_nvd                         32
% 3.26/1.00  --sub_typing                            true
% 3.26/1.00  --prep_gs_sim                           true
% 3.26/1.00  --prep_unflatten                        true
% 3.26/1.00  --prep_res_sim                          true
% 3.26/1.00  --prep_upred                            true
% 3.26/1.00  --prep_sem_filter                       exhaustive
% 3.26/1.00  --prep_sem_filter_out                   false
% 3.26/1.00  --pred_elim                             true
% 3.26/1.00  --res_sim_input                         true
% 3.26/1.00  --eq_ax_congr_red                       true
% 3.26/1.00  --pure_diseq_elim                       true
% 3.26/1.00  --brand_transform                       false
% 3.26/1.00  --non_eq_to_eq                          false
% 3.26/1.00  --prep_def_merge                        true
% 3.26/1.00  --prep_def_merge_prop_impl              false
% 3.26/1.00  --prep_def_merge_mbd                    true
% 3.26/1.00  --prep_def_merge_tr_red                 false
% 3.26/1.00  --prep_def_merge_tr_cl                  false
% 3.26/1.00  --smt_preprocessing                     true
% 3.26/1.00  --smt_ac_axioms                         fast
% 3.26/1.00  --preprocessed_out                      false
% 3.26/1.00  --preprocessed_stats                    false
% 3.26/1.00  
% 3.26/1.00  ------ Abstraction refinement Options
% 3.26/1.00  
% 3.26/1.00  --abstr_ref                             []
% 3.26/1.00  --abstr_ref_prep                        false
% 3.26/1.00  --abstr_ref_until_sat                   false
% 3.26/1.00  --abstr_ref_sig_restrict                funpre
% 3.26/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/1.00  --abstr_ref_under                       []
% 3.26/1.00  
% 3.26/1.00  ------ SAT Options
% 3.26/1.00  
% 3.26/1.00  --sat_mode                              false
% 3.26/1.00  --sat_fm_restart_options                ""
% 3.26/1.00  --sat_gr_def                            false
% 3.26/1.00  --sat_epr_types                         true
% 3.26/1.00  --sat_non_cyclic_types                  false
% 3.26/1.00  --sat_finite_models                     false
% 3.26/1.00  --sat_fm_lemmas                         false
% 3.26/1.00  --sat_fm_prep                           false
% 3.26/1.00  --sat_fm_uc_incr                        true
% 3.26/1.00  --sat_out_model                         small
% 3.26/1.00  --sat_out_clauses                       false
% 3.26/1.00  
% 3.26/1.00  ------ QBF Options
% 3.26/1.00  
% 3.26/1.00  --qbf_mode                              false
% 3.26/1.00  --qbf_elim_univ                         false
% 3.26/1.00  --qbf_dom_inst                          none
% 3.26/1.00  --qbf_dom_pre_inst                      false
% 3.26/1.00  --qbf_sk_in                             false
% 3.26/1.00  --qbf_pred_elim                         true
% 3.26/1.00  --qbf_split                             512
% 3.26/1.00  
% 3.26/1.00  ------ BMC1 Options
% 3.26/1.00  
% 3.26/1.00  --bmc1_incremental                      false
% 3.26/1.00  --bmc1_axioms                           reachable_all
% 3.26/1.00  --bmc1_min_bound                        0
% 3.26/1.00  --bmc1_max_bound                        -1
% 3.26/1.00  --bmc1_max_bound_default                -1
% 3.26/1.00  --bmc1_symbol_reachability              true
% 3.26/1.00  --bmc1_property_lemmas                  false
% 3.26/1.00  --bmc1_k_induction                      false
% 3.26/1.00  --bmc1_non_equiv_states                 false
% 3.26/1.00  --bmc1_deadlock                         false
% 3.26/1.00  --bmc1_ucm                              false
% 3.26/1.00  --bmc1_add_unsat_core                   none
% 3.26/1.00  --bmc1_unsat_core_children              false
% 3.26/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/1.00  --bmc1_out_stat                         full
% 3.26/1.00  --bmc1_ground_init                      false
% 3.26/1.00  --bmc1_pre_inst_next_state              false
% 3.26/1.00  --bmc1_pre_inst_state                   false
% 3.26/1.00  --bmc1_pre_inst_reach_state             false
% 3.26/1.00  --bmc1_out_unsat_core                   false
% 3.26/1.00  --bmc1_aig_witness_out                  false
% 3.26/1.00  --bmc1_verbose                          false
% 3.26/1.00  --bmc1_dump_clauses_tptp                false
% 3.26/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.26/1.00  --bmc1_dump_file                        -
% 3.26/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.26/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.26/1.00  --bmc1_ucm_extend_mode                  1
% 3.26/1.00  --bmc1_ucm_init_mode                    2
% 3.26/1.00  --bmc1_ucm_cone_mode                    none
% 3.26/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.26/1.00  --bmc1_ucm_relax_model                  4
% 3.26/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.26/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/1.00  --bmc1_ucm_layered_model                none
% 3.26/1.00  --bmc1_ucm_max_lemma_size               10
% 3.26/1.00  
% 3.26/1.00  ------ AIG Options
% 3.26/1.00  
% 3.26/1.00  --aig_mode                              false
% 3.26/1.00  
% 3.26/1.00  ------ Instantiation Options
% 3.26/1.00  
% 3.26/1.00  --instantiation_flag                    true
% 3.26/1.00  --inst_sos_flag                         false
% 3.26/1.00  --inst_sos_phase                        true
% 3.26/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/1.00  --inst_lit_sel_side                     none
% 3.26/1.00  --inst_solver_per_active                1400
% 3.26/1.00  --inst_solver_calls_frac                1.
% 3.26/1.00  --inst_passive_queue_type               priority_queues
% 3.26/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/1.00  --inst_passive_queues_freq              [25;2]
% 3.26/1.00  --inst_dismatching                      true
% 3.26/1.00  --inst_eager_unprocessed_to_passive     true
% 3.26/1.00  --inst_prop_sim_given                   true
% 3.26/1.00  --inst_prop_sim_new                     false
% 3.26/1.00  --inst_subs_new                         false
% 3.26/1.00  --inst_eq_res_simp                      false
% 3.26/1.00  --inst_subs_given                       false
% 3.26/1.00  --inst_orphan_elimination               true
% 3.26/1.00  --inst_learning_loop_flag               true
% 3.26/1.00  --inst_learning_start                   3000
% 3.26/1.00  --inst_learning_factor                  2
% 3.26/1.00  --inst_start_prop_sim_after_learn       3
% 3.26/1.00  --inst_sel_renew                        solver
% 3.26/1.00  --inst_lit_activity_flag                true
% 3.26/1.00  --inst_restr_to_given                   false
% 3.26/1.00  --inst_activity_threshold               500
% 3.26/1.00  --inst_out_proof                        true
% 3.26/1.00  
% 3.26/1.00  ------ Resolution Options
% 3.26/1.00  
% 3.26/1.00  --resolution_flag                       false
% 3.26/1.00  --res_lit_sel                           adaptive
% 3.26/1.00  --res_lit_sel_side                      none
% 3.26/1.00  --res_ordering                          kbo
% 3.26/1.00  --res_to_prop_solver                    active
% 3.26/1.00  --res_prop_simpl_new                    false
% 3.26/1.00  --res_prop_simpl_given                  true
% 3.26/1.00  --res_passive_queue_type                priority_queues
% 3.26/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/1.00  --res_passive_queues_freq               [15;5]
% 3.26/1.00  --res_forward_subs                      full
% 3.26/1.00  --res_backward_subs                     full
% 3.26/1.00  --res_forward_subs_resolution           true
% 3.26/1.00  --res_backward_subs_resolution          true
% 3.26/1.00  --res_orphan_elimination                true
% 3.26/1.00  --res_time_limit                        2.
% 3.26/1.00  --res_out_proof                         true
% 3.26/1.00  
% 3.26/1.00  ------ Superposition Options
% 3.26/1.00  
% 3.26/1.00  --superposition_flag                    true
% 3.26/1.00  --sup_passive_queue_type                priority_queues
% 3.26/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.26/1.00  --demod_completeness_check              fast
% 3.26/1.00  --demod_use_ground                      true
% 3.26/1.00  --sup_to_prop_solver                    passive
% 3.26/1.00  --sup_prop_simpl_new                    true
% 3.26/1.00  --sup_prop_simpl_given                  true
% 3.26/1.00  --sup_fun_splitting                     false
% 3.26/1.00  --sup_smt_interval                      50000
% 3.26/1.00  
% 3.26/1.00  ------ Superposition Simplification Setup
% 3.26/1.00  
% 3.26/1.00  --sup_indices_passive                   []
% 3.26/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_full_bw                           [BwDemod]
% 3.26/1.00  --sup_immed_triv                        [TrivRules]
% 3.26/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_immed_bw_main                     []
% 3.26/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/1.00  
% 3.26/1.00  ------ Combination Options
% 3.26/1.00  
% 3.26/1.00  --comb_res_mult                         3
% 3.26/1.00  --comb_sup_mult                         2
% 3.26/1.00  --comb_inst_mult                        10
% 3.26/1.00  
% 3.26/1.00  ------ Debug Options
% 3.26/1.00  
% 3.26/1.00  --dbg_backtrace                         false
% 3.26/1.00  --dbg_dump_prop_clauses                 false
% 3.26/1.00  --dbg_dump_prop_clauses_file            -
% 3.26/1.00  --dbg_out_stat                          false
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  ------ Proving...
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  % SZS status Theorem for theBenchmark.p
% 3.26/1.00  
% 3.26/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.26/1.00  
% 3.26/1.00  fof(f16,axiom,(
% 3.26/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f29,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/1.00    inference(ennf_transformation,[],[f16])).
% 3.26/1.00  
% 3.26/1.00  fof(f30,plain,(
% 3.26/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/1.00    inference(flattening,[],[f29])).
% 3.26/1.00  
% 3.26/1.00  fof(f49,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/1.00    inference(nnf_transformation,[],[f30])).
% 3.26/1.00  
% 3.26/1.00  fof(f76,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f49])).
% 3.26/1.00  
% 3.26/1.00  fof(f17,conjecture,(
% 3.26/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f18,negated_conjecture,(
% 3.26/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.26/1.00    inference(negated_conjecture,[],[f17])).
% 3.26/1.00  
% 3.26/1.00  fof(f31,plain,(
% 3.26/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.26/1.00    inference(ennf_transformation,[],[f18])).
% 3.26/1.00  
% 3.26/1.00  fof(f32,plain,(
% 3.26/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.26/1.00    inference(flattening,[],[f31])).
% 3.26/1.00  
% 3.26/1.00  fof(f50,plain,(
% 3.26/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_2(sK6,sK3,sK5) | ~v1_funct_1(sK6)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f51,plain,(
% 3.26/1.00    (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_2(sK6,sK3,sK5) | ~v1_funct_1(sK6)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f32,f50])).
% 3.26/1.00  
% 3.26/1.00  fof(f83,plain,(
% 3.26/1.00    v1_funct_2(sK6,sK3,sK4)),
% 3.26/1.00    inference(cnf_transformation,[],[f51])).
% 3.26/1.00  
% 3.26/1.00  fof(f84,plain,(
% 3.26/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.26/1.00    inference(cnf_transformation,[],[f51])).
% 3.26/1.00  
% 3.26/1.00  fof(f13,axiom,(
% 3.26/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f25,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/1.00    inference(ennf_transformation,[],[f13])).
% 3.26/1.00  
% 3.26/1.00  fof(f73,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f25])).
% 3.26/1.00  
% 3.26/1.00  fof(f15,axiom,(
% 3.26/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f27,plain,(
% 3.26/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.26/1.00    inference(ennf_transformation,[],[f15])).
% 3.26/1.00  
% 3.26/1.00  fof(f28,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.26/1.00    inference(flattening,[],[f27])).
% 3.26/1.00  
% 3.26/1.00  fof(f75,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f28])).
% 3.26/1.00  
% 3.26/1.00  fof(f5,axiom,(
% 3.26/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f43,plain,(
% 3.26/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.26/1.00    inference(nnf_transformation,[],[f5])).
% 3.26/1.00  
% 3.26/1.00  fof(f44,plain,(
% 3.26/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.26/1.00    inference(flattening,[],[f43])).
% 3.26/1.00  
% 3.26/1.00  fof(f59,plain,(
% 3.26/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.26/1.00    inference(cnf_transformation,[],[f44])).
% 3.26/1.00  
% 3.26/1.00  fof(f89,plain,(
% 3.26/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.26/1.00    inference(equality_resolution,[],[f59])).
% 3.26/1.00  
% 3.26/1.00  fof(f14,axiom,(
% 3.26/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f26,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/1.00    inference(ennf_transformation,[],[f14])).
% 3.26/1.00  
% 3.26/1.00  fof(f74,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f26])).
% 3.26/1.00  
% 3.26/1.00  fof(f85,plain,(
% 3.26/1.00    r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5)),
% 3.26/1.00    inference(cnf_transformation,[],[f51])).
% 3.26/1.00  
% 3.26/1.00  fof(f7,axiom,(
% 3.26/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f47,plain,(
% 3.26/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.26/1.00    inference(nnf_transformation,[],[f7])).
% 3.26/1.00  
% 3.26/1.00  fof(f65,plain,(
% 3.26/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f47])).
% 3.26/1.00  
% 3.26/1.00  fof(f9,axiom,(
% 3.26/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f22,plain,(
% 3.26/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.26/1.00    inference(ennf_transformation,[],[f9])).
% 3.26/1.00  
% 3.26/1.00  fof(f68,plain,(
% 3.26/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f22])).
% 3.26/1.00  
% 3.26/1.00  fof(f66,plain,(
% 3.26/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f47])).
% 3.26/1.00  
% 3.26/1.00  fof(f11,axiom,(
% 3.26/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f70,plain,(
% 3.26/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f11])).
% 3.26/1.00  
% 3.26/1.00  fof(f78,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f49])).
% 3.26/1.00  
% 3.26/1.00  fof(f87,plain,(
% 3.26/1.00    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_2(sK6,sK3,sK5) | ~v1_funct_1(sK6)),
% 3.26/1.00    inference(cnf_transformation,[],[f51])).
% 3.26/1.00  
% 3.26/1.00  fof(f82,plain,(
% 3.26/1.00    v1_funct_1(sK6)),
% 3.26/1.00    inference(cnf_transformation,[],[f51])).
% 3.26/1.00  
% 3.26/1.00  fof(f3,axiom,(
% 3.26/1.00    v1_xboole_0(k1_xboole_0)),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f57,plain,(
% 3.26/1.00    v1_xboole_0(k1_xboole_0)),
% 3.26/1.00    inference(cnf_transformation,[],[f3])).
% 3.26/1.00  
% 3.26/1.00  fof(f2,axiom,(
% 3.26/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f19,plain,(
% 3.26/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.26/1.00    inference(ennf_transformation,[],[f2])).
% 3.26/1.00  
% 3.26/1.00  fof(f37,plain,(
% 3.26/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.26/1.00    inference(nnf_transformation,[],[f19])).
% 3.26/1.00  
% 3.26/1.00  fof(f38,plain,(
% 3.26/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.26/1.00    inference(rectify,[],[f37])).
% 3.26/1.00  
% 3.26/1.00  fof(f39,plain,(
% 3.26/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f40,plain,(
% 3.26/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 3.26/1.00  
% 3.26/1.00  fof(f55,plain,(
% 3.26/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f40])).
% 3.26/1.00  
% 3.26/1.00  fof(f8,axiom,(
% 3.26/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f21,plain,(
% 3.26/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.26/1.00    inference(ennf_transformation,[],[f8])).
% 3.26/1.00  
% 3.26/1.00  fof(f67,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f21])).
% 3.26/1.00  
% 3.26/1.00  fof(f6,axiom,(
% 3.26/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f45,plain,(
% 3.26/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.26/1.00    inference(nnf_transformation,[],[f6])).
% 3.26/1.00  
% 3.26/1.00  fof(f46,plain,(
% 3.26/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.26/1.00    inference(flattening,[],[f45])).
% 3.26/1.00  
% 3.26/1.00  fof(f62,plain,(
% 3.26/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f46])).
% 3.26/1.00  
% 3.26/1.00  fof(f63,plain,(
% 3.26/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.26/1.00    inference(cnf_transformation,[],[f46])).
% 3.26/1.00  
% 3.26/1.00  fof(f91,plain,(
% 3.26/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.26/1.00    inference(equality_resolution,[],[f63])).
% 3.26/1.00  
% 3.26/1.00  fof(f79,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f49])).
% 3.26/1.00  
% 3.26/1.00  fof(f95,plain,(
% 3.26/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.26/1.00    inference(equality_resolution,[],[f79])).
% 3.26/1.00  
% 3.26/1.00  fof(f4,axiom,(
% 3.26/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f20,plain,(
% 3.26/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.26/1.00    inference(ennf_transformation,[],[f4])).
% 3.26/1.00  
% 3.26/1.00  fof(f41,plain,(
% 3.26/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f42,plain,(
% 3.26/1.00    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f41])).
% 3.26/1.00  
% 3.26/1.00  fof(f58,plain,(
% 3.26/1.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.26/1.00    inference(cnf_transformation,[],[f42])).
% 3.26/1.00  
% 3.26/1.00  fof(f1,axiom,(
% 3.26/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f33,plain,(
% 3.26/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.26/1.00    inference(nnf_transformation,[],[f1])).
% 3.26/1.00  
% 3.26/1.00  fof(f34,plain,(
% 3.26/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.26/1.00    inference(rectify,[],[f33])).
% 3.26/1.00  
% 3.26/1.00  fof(f35,plain,(
% 3.26/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f36,plain,(
% 3.26/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.26/1.00  
% 3.26/1.00  fof(f52,plain,(
% 3.26/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f36])).
% 3.26/1.00  
% 3.26/1.00  fof(f10,axiom,(
% 3.26/1.00    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f23,plain,(
% 3.26/1.00    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 3.26/1.00    inference(ennf_transformation,[],[f10])).
% 3.26/1.00  
% 3.26/1.00  fof(f69,plain,(
% 3.26/1.00    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f23])).
% 3.26/1.00  
% 3.26/1.00  fof(f53,plain,(
% 3.26/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f36])).
% 3.26/1.00  
% 3.26/1.00  fof(f64,plain,(
% 3.26/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.26/1.00    inference(cnf_transformation,[],[f46])).
% 3.26/1.00  
% 3.26/1.00  fof(f90,plain,(
% 3.26/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.26/1.00    inference(equality_resolution,[],[f64])).
% 3.26/1.00  
% 3.26/1.00  fof(f86,plain,(
% 3.26/1.00    k1_xboole_0 = sK3 | k1_xboole_0 != sK4),
% 3.26/1.00    inference(cnf_transformation,[],[f51])).
% 3.26/1.00  
% 3.26/1.00  fof(f77,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/1.00    inference(cnf_transformation,[],[f49])).
% 3.26/1.00  
% 3.26/1.00  fof(f96,plain,(
% 3.26/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.26/1.00    inference(equality_resolution,[],[f77])).
% 3.26/1.00  
% 3.26/1.00  cnf(c_29,plain,
% 3.26/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.26/1.00      | k1_xboole_0 = X2 ),
% 3.26/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_34,negated_conjecture,
% 3.26/1.00      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.26/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_519,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.26/1.00      | sK4 != X2
% 3.26/1.00      | sK3 != X1
% 3.26/1.00      | sK6 != X0
% 3.26/1.00      | k1_xboole_0 = X2 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_34]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_520,plain,
% 3.26/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.26/1.00      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.26/1.00      | k1_xboole_0 = sK4 ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_519]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_33,negated_conjecture,
% 3.26/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.26/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_522,plain,
% 3.26/1.00      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_520,c_33]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1510,plain,
% 3.26/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_21,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1514,plain,
% 3.26/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.26/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3436,plain,
% 3.26/1.00      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1510,c_1514]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3702,plain,
% 3.26/1.00      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_522,c_3436]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_23,plain,
% 3.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.26/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.26/1.00      | ~ v1_relat_1(X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1512,plain,
% 3.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.26/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.26/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_9,plain,
% 3.26/1.00      ( r1_tarski(X0,X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1521,plain,
% 3.26/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_22,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1513,plain,
% 3.26/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.26/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3281,plain,
% 3.26/1.00      ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1510,c_1513]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_32,negated_conjecture,
% 3.26/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) ),
% 3.26/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1511,plain,
% 3.26/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3615,plain,
% 3.26/1.00      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_3281,c_1511]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3435,plain,
% 3.26/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.26/1.00      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.26/1.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.26/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1512,c_1514]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7485,plain,
% 3.26/1.00      ( k1_relset_1(X0,sK5,sK6) = k1_relat_1(sK6)
% 3.26/1.00      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 3.26/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_3615,c_3435]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_14,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1519,plain,
% 3.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.26/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2633,plain,
% 3.26/1.00      ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1510,c_1519]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_16,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.26/1.00      | ~ v1_relat_1(X1)
% 3.26/1.00      | v1_relat_1(X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_13,plain,
% 3.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_254,plain,
% 3.26/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.26/1.00      inference(prop_impl,[status(thm)],[c_13]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_255,plain,
% 3.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_254]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_319,plain,
% 3.26/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.26/1.00      inference(bin_hyper_res,[status(thm)],[c_16,c_255]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1508,plain,
% 3.26/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.26/1.00      | v1_relat_1(X1) != iProver_top
% 3.26/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2646,plain,
% 3.26/1.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.26/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_2633,c_1508]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_18,plain,
% 3.26/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.26/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1517,plain,
% 3.26/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2651,plain,
% 3.26/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.26/1.00      inference(forward_subsumption_resolution,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_2646,c_1517]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7742,plain,
% 3.26/1.00      ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 3.26/1.00      | k1_relset_1(X0,sK5,sK6) = k1_relat_1(sK6) ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_7485,c_2651]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7743,plain,
% 3.26/1.00      ( k1_relset_1(X0,sK5,sK6) = k1_relat_1(sK6)
% 3.26/1.00      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_7742]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7753,plain,
% 3.26/1.00      ( k1_relset_1(X0,sK5,sK6) = k1_relat_1(sK6)
% 3.26/1.00      | sK4 = k1_xboole_0
% 3.26/1.00      | r1_tarski(sK3,X0) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_3702,c_7743]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7788,plain,
% 3.26/1.00      ( k1_relset_1(sK3,sK5,sK6) = k1_relat_1(sK6) | sK4 = k1_xboole_0 ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1521,c_7753]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_27,plain,
% 3.26/1.00      ( v1_funct_2(X0,X1,X2)
% 3.26/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.26/1.00      | k1_xboole_0 = X2 ),
% 3.26/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_30,negated_conjecture,
% 3.26/1.00      ( ~ v1_funct_2(sK6,sK3,sK5)
% 3.26/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.26/1.00      | ~ v1_funct_1(sK6) ),
% 3.26/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_35,negated_conjecture,
% 3.26/1.00      ( v1_funct_1(sK6) ),
% 3.26/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_179,plain,
% 3.26/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.26/1.00      | ~ v1_funct_2(sK6,sK3,sK5) ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_30,c_35]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_180,negated_conjecture,
% 3.26/1.00      ( ~ v1_funct_2(sK6,sK3,sK5)
% 3.26/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_179]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_506,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.26/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.26/1.00      | sK5 != X2
% 3.26/1.00      | sK3 != X1
% 3.26/1.00      | sK6 != X0
% 3.26/1.00      | k1_xboole_0 = X2 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_180]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_507,plain,
% 3.26/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.26/1.00      | k1_relset_1(sK3,sK5,sK6) != sK3
% 3.26/1.00      | k1_xboole_0 = sK5 ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_506]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1503,plain,
% 3.26/1.00      ( k1_relset_1(sK3,sK5,sK6) != sK3
% 3.26/1.00      | k1_xboole_0 = sK5
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8232,plain,
% 3.26/1.00      ( k1_relat_1(sK6) != sK3
% 3.26/1.00      | sK4 = k1_xboole_0
% 3.26/1.00      | sK5 = k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_7788,c_1503]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_5,plain,
% 3.26/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_102,plain,
% 3.26/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3,plain,
% 3.26/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1526,plain,
% 3.26/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.26/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_15,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.26/1.00      | ~ r2_hidden(X2,X0)
% 3.26/1.00      | ~ v1_xboole_0(X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_318,plain,
% 3.26/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 3.26/1.00      inference(bin_hyper_res,[status(thm)],[c_15,c_255]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1509,plain,
% 3.26/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.26/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.26/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2890,plain,
% 3.26/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.26/1.00      | r1_tarski(X0,X2) = iProver_top
% 3.26/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1526,c_1509]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_5864,plain,
% 3.26/1.00      ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
% 3.26/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_3615,c_2890]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3280,plain,
% 3.26/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.26/1.00      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.26/1.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.26/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1512,c_1513]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_6567,plain,
% 3.26/1.00      ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
% 3.26/1.00      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 3.26/1.00      | v1_relat_1(sK6) != iProver_top
% 3.26/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_5864,c_3280]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7299,plain,
% 3.26/1.00      ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 3.26/1.00      | k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
% 3.26/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_6567,c_2651]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7300,plain,
% 3.26/1.00      ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
% 3.26/1.00      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 3.26/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_7299]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7311,plain,
% 3.26/1.00      ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
% 3.26/1.00      | sK4 = k1_xboole_0
% 3.26/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.26/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_3702,c_7300]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_12,plain,
% 3.26/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.26/1.00      | k1_xboole_0 = X0
% 3.26/1.00      | k1_xboole_0 = X1 ),
% 3.26/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_90,plain,
% 3.26/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.26/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_11,plain,
% 3.26/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.26/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_91,plain,
% 3.26/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_26,plain,
% 3.26/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.26/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.26/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.26/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_477,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.26/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.26/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.26/1.00      | sK5 != X1
% 3.26/1.00      | sK3 != k1_xboole_0
% 3.26/1.00      | sK6 != X0 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_180]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_478,plain,
% 3.26/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.26/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
% 3.26/1.00      | k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
% 3.26/1.00      | sK3 != k1_xboole_0 ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_477]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1505,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
% 3.26/1.00      | sK3 != k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1668,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
% 3.26/1.00      | sK3 != k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_1505,c_11]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1767,plain,
% 3.26/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.26/1.00      | ~ r1_tarski(sK6,k2_zfmisc_1(sK3,sK5)) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1768,plain,
% 3.26/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) = iProver_top
% 3.26/1.00      | r1_tarski(sK6,k2_zfmisc_1(sK3,sK5)) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_1767]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1828,plain,
% 3.26/1.00      ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK5))
% 3.26/1.00      | r2_hidden(sK1(sK6,k2_zfmisc_1(sK3,sK5)),sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1835,plain,
% 3.26/1.00      ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK5)) = iProver_top
% 3.26/1.00      | r2_hidden(sK1(sK6,k2_zfmisc_1(sK3,sK5)),sK6) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_1828]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_835,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1793,plain,
% 3.26/1.00      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_835]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1860,plain,
% 3.26/1.00      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1793]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_834,plain,( X0 = X0 ),theory(equality) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1861,plain,
% 3.26/1.00      ( sK3 = sK3 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_834]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1973,plain,
% 3.26/1.00      ( k1_relset_1(sK3,sK5,sK6) != X0
% 3.26/1.00      | k1_relset_1(sK3,sK5,sK6) = sK3
% 3.26/1.00      | sK3 != X0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_835]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2270,plain,
% 3.26/1.00      ( k1_relset_1(sK3,sK5,sK6) != k1_relat_1(sK6)
% 3.26/1.00      | k1_relset_1(sK3,sK5,sK6) = sK3
% 3.26/1.00      | sK3 != k1_relat_1(sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1973]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2271,plain,
% 3.26/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.26/1.00      | k1_relset_1(sK3,sK5,sK6) = k1_relat_1(sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2272,plain,
% 3.26/1.00      ( k1_relset_1(sK3,sK5,sK6) = k1_relat_1(sK6)
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2271]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_6,plain,
% 3.26/1.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.26/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2589,plain,
% 3.26/1.00      ( r2_hidden(sK2(sK3),sK3) | k1_xboole_0 = sK3 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2590,plain,
% 3.26/1.00      ( k1_xboole_0 = sK3 | r2_hidden(sK2(sK3),sK3) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2589]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1,plain,
% 3.26/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2662,plain,
% 3.26/1.00      ( ~ r2_hidden(sK1(sK6,k2_zfmisc_1(sK3,sK5)),sK6)
% 3.26/1.00      | ~ v1_xboole_0(sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2670,plain,
% 3.26/1.00      ( ~ r1_tarski(sK6,X0)
% 3.26/1.00      | ~ r2_hidden(sK1(sK6,k2_zfmisc_1(sK3,sK5)),sK6)
% 3.26/1.00      | ~ v1_xboole_0(X0) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_318]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2671,plain,
% 3.26/1.00      ( r1_tarski(sK6,X0) != iProver_top
% 3.26/1.00      | r2_hidden(sK1(sK6,k2_zfmisc_1(sK3,sK5)),sK6) != iProver_top
% 3.26/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2670]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2673,plain,
% 3.26/1.00      ( r1_tarski(sK6,k1_xboole_0) != iProver_top
% 3.26/1.00      | r2_hidden(sK1(sK6,k2_zfmisc_1(sK3,sK5)),sK6) != iProver_top
% 3.26/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_2671]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2918,plain,
% 3.26/1.00      ( sK5 = sK5 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_834]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_17,plain,
% 3.26/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 3.26/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1518,plain,
% 3.26/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.26/1.00      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3732,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | v1_xboole_0(sK3) = iProver_top
% 3.26/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_3702,c_1518]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3723,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK5,sK6) != X0
% 3.26/1.00      | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
% 3.26/1.00      | k1_xboole_0 != X0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_835]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3901,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_relset_1(X0,X1,X2)
% 3.26/1.00      | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
% 3.26/1.00      | k1_xboole_0 != k1_relset_1(X0,X1,X2) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_3723]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3903,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.26/1.00      | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
% 3.26/1.00      | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_3901]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_843,plain,
% 3.26/1.00      ( X0 != X1
% 3.26/1.00      | X2 != X3
% 3.26/1.00      | X4 != X5
% 3.26/1.00      | k1_relset_1(X0,X2,X4) = k1_relset_1(X1,X3,X5) ),
% 3.26/1.00      theory(equality) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3902,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK5,sK6) = k1_relset_1(X0,X1,X2)
% 3.26/1.00      | sK5 != X1
% 3.26/1.00      | sK6 != X2
% 3.26/1.00      | k1_xboole_0 != X0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_843]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3904,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK5,sK6) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.26/1.00      | sK5 != k1_xboole_0
% 3.26/1.00      | sK6 != k1_xboole_0
% 3.26/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_3902]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_836,plain,
% 3.26/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.26/1.00      theory(equality) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4167,plain,
% 3.26/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_836]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4169,plain,
% 3.26/1.00      ( v1_xboole_0(sK6)
% 3.26/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.26/1.00      | sK6 != k1_xboole_0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_4167]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2610,plain,
% 3.26/1.00      ( sK5 != X0 | sK5 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_835]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4202,plain,
% 3.26/1.00      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_2610]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_0,plain,
% 3.26/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1529,plain,
% 3.26/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.26/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2313,plain,
% 3.26/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.26/1.00      | v1_xboole_0(X1) != iProver_top
% 3.26/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1529,c_1509]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4279,plain,
% 3.26/1.00      ( v1_xboole_0(k2_relat_1(sK6)) = iProver_top
% 3.26/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_3615,c_2313]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1856,plain,
% 3.26/1.00      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_835]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2826,plain,
% 3.26/1.00      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1856]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4312,plain,
% 3.26/1.00      ( k1_relat_1(sK6) != sK3 | sK3 = k1_relat_1(sK6) | sK3 != sK3 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_2826]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1520,plain,
% 3.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.26/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_10,plain,
% 3.26/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.26/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3437,plain,
% 3.26/1.00      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 3.26/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_10,c_1514]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3609,plain,
% 3.26/1.00      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 3.26/1.00      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1520,c_3437]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4481,plain,
% 3.26/1.00      ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1521,c_3609]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1524,plain,
% 3.26/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1523,plain,
% 3.26/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1528,plain,
% 3.26/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.26/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2319,plain,
% 3.26/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1523,c_1528]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2412,plain,
% 3.26/1.00      ( k1_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1518,c_2319]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2423,plain,
% 3.26/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1524,c_2412]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4483,plain,
% 3.26/1.00      ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.26/1.00      inference(light_normalisation,[status(thm)],[c_4481,c_2423]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4492,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_4483]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2889,plain,
% 3.26/1.00      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1526,c_1528]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2727,plain,
% 3.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.26/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.26/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_10,c_1512]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3963,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
% 3.26/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.26/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_3702,c_2727]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4185,plain,
% 3.26/1.00      ( r1_tarski(sK3,X0) != iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.26/1.00      | sK4 = k1_xboole_0 ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_3963,c_2651]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4186,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
% 3.26/1.00      | r1_tarski(sK3,X0) != iProver_top ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_4185]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4195,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.26/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.26/1.00      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_2889,c_4186]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_5678,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.26/1.00      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1521,c_4195]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2729,plain,
% 3.26/1.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.26/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.26/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1512,c_1519]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4931,plain,
% 3.26/1.00      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.26/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.26/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_10,c_2729]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4997,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
% 3.26/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.26/1.00      | r1_tarski(sK6,k1_xboole_0) = iProver_top
% 3.26/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_3702,c_4931]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_5252,plain,
% 3.26/1.00      ( r1_tarski(sK6,k1_xboole_0) = iProver_top
% 3.26/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.26/1.00      | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
% 3.26/1.00      | sK4 = k1_xboole_0 ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_4997,c_2651]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_5253,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
% 3.26/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.26/1.00      | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_5252]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_5262,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.26/1.00      | r1_tarski(sK6,k1_xboole_0) = iProver_top
% 3.26/1.00      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_2889,c_5253]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_5645,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | r1_tarski(sK6,k1_xboole_0) = iProver_top
% 3.26/1.00      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1521,c_5262]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_5835,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | r1_tarski(sK6,k1_xboole_0) = iProver_top
% 3.26/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_4279,c_5645]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2188,plain,
% 3.26/1.00      ( k1_xboole_0 = X0
% 3.26/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.26/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1523,c_1509]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_6432,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | sK6 = k1_xboole_0
% 3.26/1.00      | v1_xboole_0(sK5) != iProver_top
% 3.26/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_5835,c_2188]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_6430,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | v1_xboole_0(sK5) != iProver_top
% 3.26/1.00      | v1_xboole_0(sK6) = iProver_top
% 3.26/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_5835,c_2313]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7401,plain,
% 3.26/1.00      ( k1_relset_1(X0,X1,X2) != X3
% 3.26/1.00      | k1_xboole_0 != X3
% 3.26/1.00      | k1_xboole_0 = k1_relset_1(X0,X1,X2) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_835]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7402,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.26/1.00      | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.26/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_7401]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7453,plain,
% 3.26/1.00      ( ~ r2_hidden(sK2(sK3),sK3) | ~ v1_xboole_0(sK3) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7454,plain,
% 3.26/1.00      ( r2_hidden(sK2(sK3),sK3) != iProver_top
% 3.26/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_7453]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7471,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0 | v1_xboole_0(sK5) != iProver_top ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_7311,c_90,c_91,c_5,c_102,c_507,c_1668,c_1767,c_1768,
% 3.26/1.00                 c_1828,c_1835,c_1860,c_1861,c_2270,c_2272,c_2590,c_2662,
% 3.26/1.00                 c_2673,c_2918,c_3702,c_3732,c_3903,c_3904,c_4169,c_4202,
% 3.26/1.00                 c_4279,c_4312,c_4492,c_5678,c_5835,c_6432,c_6430,c_7402,
% 3.26/1.00                 c_7454]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8061,plain,
% 3.26/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_836]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8062,plain,
% 3.26/1.00      ( sK5 != X0
% 3.26/1.00      | v1_xboole_0(X0) != iProver_top
% 3.26/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_8061]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8064,plain,
% 3.26/1.00      ( sK5 != k1_xboole_0
% 3.26/1.00      | v1_xboole_0(sK5) = iProver_top
% 3.26/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_8062]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8376,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_8232,c_102,c_3702,c_7471,c_8064]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8383,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
% 3.26/1.00      | r1_tarski(k1_relat_1(sK6),sK3) != iProver_top
% 3.26/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1512,c_8376]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8490,plain,
% 3.26/1.00      ( r1_tarski(k1_relat_1(sK6),sK3) != iProver_top
% 3.26/1.00      | sK4 = k1_xboole_0 ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_8383,c_2651,c_3615]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8491,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0
% 3.26/1.00      | r1_tarski(k1_relat_1(sK6),sK3) != iProver_top ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_8490]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8497,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0 | r1_tarski(sK3,sK3) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_3702,c_8491]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8605,plain,
% 3.26/1.00      ( sK4 = k1_xboole_0 ),
% 3.26/1.00      inference(forward_subsumption_resolution,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_8497,c_1521]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8616,plain,
% 3.26/1.00      ( k1_relset_1(sK3,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_8605,c_3436]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_31,negated_conjecture,
% 3.26/1.00      ( k1_xboole_0 != sK4 | k1_xboole_0 = sK3 ),
% 3.26/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8624,plain,
% 3.26/1.00      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_8605,c_31]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8625,plain,
% 3.26/1.00      ( sK3 = k1_xboole_0 ),
% 3.26/1.00      inference(equality_resolution_simp,[status(thm)],[c_8624]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_28,plain,
% 3.26/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.26/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.26/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.26/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_493,plain,
% 3.26/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.26/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.26/1.00      | sK4 != X1
% 3.26/1.00      | sK3 != k1_xboole_0
% 3.26/1.00      | sK6 != X0 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_34]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_494,plain,
% 3.26/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
% 3.26/1.00      | k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
% 3.26/1.00      | sK3 != k1_xboole_0 ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_493]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1504,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
% 3.26/1.00      | sK3 != k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1644,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
% 3.26/1.00      | sK3 != k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_1504,c_11]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8620,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 3.26/1.00      | sK3 != k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_8605,c_1644]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8638,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 3.26/1.00      | k1_xboole_0 != k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(light_normalisation,[status(thm)],[c_8620,c_8625]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8639,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.26/1.00      inference(equality_resolution_simp,[status(thm)],[c_8638]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8623,plain,
% 3.26/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_8605,c_1510]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8628,plain,
% 3.26/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.26/1.00      inference(light_normalisation,[status(thm)],[c_8623,c_8625]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8630,plain,
% 3.26/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.26/1.00      inference(demodulation,[status(thm)],[c_8628,c_11]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8642,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
% 3.26/1.00      inference(forward_subsumption_resolution,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_8639,c_8630]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_8652,plain,
% 3.26/1.00      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 3.26/1.00      inference(light_normalisation,[status(thm)],[c_8616,c_8625,c_8642]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_6384,plain,
% 3.26/1.00      ( ~ r1_tarski(sK6,X0)
% 3.26/1.00      | ~ r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6)
% 3.26/1.00      | ~ v1_xboole_0(X0) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_318]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_6385,plain,
% 3.26/1.00      ( r1_tarski(sK6,X0) != iProver_top
% 3.26/1.00      | r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6) != iProver_top
% 3.26/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_6384]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_6387,plain,
% 3.26/1.00      ( r1_tarski(sK6,k1_xboole_0) != iProver_top
% 3.26/1.00      | r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6) != iProver_top
% 3.26/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_6385]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4448,plain,
% 3.26/1.00      ( X0 != X1 | X0 = k1_relat_1(sK6) | k1_relat_1(sK6) != X1 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_835]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4449,plain,
% 3.26/1.00      ( k1_relat_1(sK6) != k1_xboole_0
% 3.26/1.00      | k1_xboole_0 = k1_relat_1(sK6)
% 3.26/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_4448]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3896,plain,
% 3.26/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
% 3.26/1.00      | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_relat_1(sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3897,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK5,sK6) = k1_relat_1(sK6)
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_3896]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3895,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_relat_1(sK6)
% 3.26/1.00      | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0
% 3.26/1.00      | k1_xboole_0 != k1_relat_1(sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_3723]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2690,plain,
% 3.26/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0)) | r1_tarski(sK6,X0) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2691,plain,
% 3.26/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
% 3.26/1.00      | r1_tarski(sK6,X0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2690]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2693,plain,
% 3.26/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.26/1.00      | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_2691]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2603,plain,
% 3.26/1.00      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_835]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2604,plain,
% 3.26/1.00      ( sK4 != k1_xboole_0
% 3.26/1.00      | k1_xboole_0 = sK4
% 3.26/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_2603]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1897,plain,
% 3.26/1.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.26/1.00      | r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2208,plain,
% 3.26/1.00      ( r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK5))
% 3.26/1.00      | r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1897]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2212,plain,
% 3.26/1.00      ( r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK5)) = iProver_top
% 3.26/1.00      | r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2208]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1796,plain,
% 3.26/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/1.00      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2076,plain,
% 3.26/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
% 3.26/1.00      | ~ r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK5)) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1796]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2077,plain,
% 3.26/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) = iProver_top
% 3.26/1.00      | r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK5)) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2076]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_479,plain,
% 3.26/1.00      ( k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
% 3.26/1.00      | sK3 != k1_xboole_0
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
% 3.26/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5))) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(contradiction,plain,
% 3.26/1.00      ( $false ),
% 3.26/1.00      inference(minisat,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_8652,c_8630,c_8605,c_6387,c_4449,c_3897,c_3895,c_2693,
% 3.26/1.00                 c_2673,c_2604,c_2212,c_2077,c_1861,c_1860,c_1835,c_1768,
% 3.26/1.00                 c_479,c_102,c_91,c_90,c_31]) ).
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.26/1.00  
% 3.26/1.00  ------                               Statistics
% 3.26/1.00  
% 3.26/1.00  ------ General
% 3.26/1.00  
% 3.26/1.00  abstr_ref_over_cycles:                  0
% 3.26/1.00  abstr_ref_under_cycles:                 0
% 3.26/1.00  gc_basic_clause_elim:                   0
% 3.26/1.00  forced_gc_time:                         0
% 3.26/1.00  parsing_time:                           0.009
% 3.26/1.00  unif_index_cands_time:                  0.
% 3.26/1.00  unif_index_add_time:                    0.
% 3.26/1.00  orderings_time:                         0.
% 3.26/1.00  out_proof_time:                         0.013
% 3.26/1.00  total_time:                             0.211
% 3.26/1.00  num_of_symbols:                         52
% 3.26/1.00  num_of_terms:                           5791
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing
% 3.26/1.00  
% 3.26/1.00  num_of_splits:                          0
% 3.26/1.00  num_of_split_atoms:                     0
% 3.26/1.00  num_of_reused_defs:                     0
% 3.26/1.00  num_eq_ax_congr_red:                    23
% 3.26/1.00  num_of_sem_filtered_clauses:            2
% 3.26/1.00  num_of_subtypes:                        0
% 3.26/1.00  monotx_restored_types:                  0
% 3.26/1.00  sat_num_of_epr_types:                   0
% 3.26/1.00  sat_num_of_non_cyclic_types:            0
% 3.26/1.00  sat_guarded_non_collapsed_types:        0
% 3.26/1.00  num_pure_diseq_elim:                    0
% 3.26/1.00  simp_replaced_by:                       0
% 3.26/1.00  res_preprocessed:                       157
% 3.26/1.00  prep_upred:                             0
% 3.26/1.00  prep_unflattend:                        33
% 3.26/1.00  smt_new_axioms:                         0
% 3.26/1.00  pred_elim_cands:                        5
% 3.26/1.00  pred_elim:                              1
% 3.26/1.00  pred_elim_cl:                           1
% 3.26/1.00  pred_elim_cycles:                       3
% 3.26/1.00  merged_defs:                            8
% 3.26/1.00  merged_defs_ncl:                        0
% 3.26/1.00  bin_hyper_res:                          10
% 3.26/1.00  prep_cycles:                            4
% 3.26/1.00  pred_elim_time:                         0.005
% 3.26/1.00  splitting_time:                         0.
% 3.26/1.00  sem_filter_time:                        0.
% 3.26/1.00  monotx_time:                            0.001
% 3.26/1.00  subtype_inf_time:                       0.
% 3.26/1.00  
% 3.26/1.00  ------ Problem properties
% 3.26/1.00  
% 3.26/1.00  clauses:                                33
% 3.26/1.00  conjectures:                            3
% 3.26/1.00  epr:                                    8
% 3.26/1.00  horn:                                   27
% 3.26/1.00  ground:                                 11
% 3.26/1.00  unary:                                  7
% 3.26/1.00  binary:                                 13
% 3.26/1.00  lits:                                   77
% 3.26/1.00  lits_eq:                                30
% 3.26/1.00  fd_pure:                                0
% 3.26/1.00  fd_pseudo:                              0
% 3.26/1.00  fd_cond:                                2
% 3.26/1.00  fd_pseudo_cond:                         1
% 3.26/1.00  ac_symbols:                             0
% 3.26/1.00  
% 3.26/1.00  ------ Propositional Solver
% 3.26/1.00  
% 3.26/1.00  prop_solver_calls:                      30
% 3.26/1.00  prop_fast_solver_calls:                 1196
% 3.26/1.00  smt_solver_calls:                       0
% 3.26/1.00  smt_fast_solver_calls:                  0
% 3.26/1.00  prop_num_of_clauses:                    2952
% 3.26/1.00  prop_preprocess_simplified:             7719
% 3.26/1.00  prop_fo_subsumed:                       22
% 3.26/1.00  prop_solver_time:                       0.
% 3.26/1.00  smt_solver_time:                        0.
% 3.26/1.00  smt_fast_solver_time:                   0.
% 3.26/1.00  prop_fast_solver_time:                  0.
% 3.26/1.00  prop_unsat_core_time:                   0.
% 3.26/1.00  
% 3.26/1.00  ------ QBF
% 3.26/1.00  
% 3.26/1.00  qbf_q_res:                              0
% 3.26/1.00  qbf_num_tautologies:                    0
% 3.26/1.00  qbf_prep_cycles:                        0
% 3.26/1.00  
% 3.26/1.00  ------ BMC1
% 3.26/1.00  
% 3.26/1.00  bmc1_current_bound:                     -1
% 3.26/1.00  bmc1_last_solved_bound:                 -1
% 3.26/1.00  bmc1_unsat_core_size:                   -1
% 3.26/1.00  bmc1_unsat_core_parents_size:           -1
% 3.26/1.00  bmc1_merge_next_fun:                    0
% 3.26/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.26/1.00  
% 3.26/1.00  ------ Instantiation
% 3.26/1.00  
% 3.26/1.00  inst_num_of_clauses:                    867
% 3.26/1.00  inst_num_in_passive:                    373
% 3.26/1.00  inst_num_in_active:                     389
% 3.26/1.00  inst_num_in_unprocessed:                106
% 3.26/1.00  inst_num_of_loops:                      720
% 3.26/1.00  inst_num_of_learning_restarts:          0
% 3.26/1.00  inst_num_moves_active_passive:          327
% 3.26/1.00  inst_lit_activity:                      0
% 3.26/1.00  inst_lit_activity_moves:                0
% 3.26/1.00  inst_num_tautologies:                   0
% 3.26/1.00  inst_num_prop_implied:                  0
% 3.26/1.00  inst_num_existing_simplified:           0
% 3.26/1.00  inst_num_eq_res_simplified:             0
% 3.26/1.00  inst_num_child_elim:                    0
% 3.26/1.00  inst_num_of_dismatching_blockings:      178
% 3.26/1.00  inst_num_of_non_proper_insts:           871
% 3.26/1.00  inst_num_of_duplicates:                 0
% 3.26/1.00  inst_inst_num_from_inst_to_res:         0
% 3.26/1.00  inst_dismatching_checking_time:         0.
% 3.26/1.00  
% 3.26/1.00  ------ Resolution
% 3.26/1.00  
% 3.26/1.00  res_num_of_clauses:                     0
% 3.26/1.00  res_num_in_passive:                     0
% 3.26/1.00  res_num_in_active:                      0
% 3.26/1.00  res_num_of_loops:                       161
% 3.26/1.00  res_forward_subset_subsumed:            44
% 3.26/1.00  res_backward_subset_subsumed:           2
% 3.26/1.00  res_forward_subsumed:                   0
% 3.26/1.00  res_backward_subsumed:                  0
% 3.26/1.00  res_forward_subsumption_resolution:     0
% 3.26/1.00  res_backward_subsumption_resolution:    0
% 3.26/1.00  res_clause_to_clause_subsumption:       1149
% 3.26/1.00  res_orphan_elimination:                 0
% 3.26/1.00  res_tautology_del:                      69
% 3.26/1.00  res_num_eq_res_simplified:              1
% 3.26/1.00  res_num_sel_changes:                    0
% 3.26/1.00  res_moves_from_active_to_pass:          0
% 3.26/1.00  
% 3.26/1.00  ------ Superposition
% 3.26/1.00  
% 3.26/1.00  sup_time_total:                         0.
% 3.26/1.00  sup_time_generating:                    0.
% 3.26/1.00  sup_time_sim_full:                      0.
% 3.26/1.00  sup_time_sim_immed:                     0.
% 3.26/1.00  
% 3.26/1.00  sup_num_of_clauses:                     185
% 3.26/1.00  sup_num_in_active:                      102
% 3.26/1.00  sup_num_in_passive:                     83
% 3.26/1.00  sup_num_of_loops:                       142
% 3.26/1.00  sup_fw_superposition:                   198
% 3.26/1.00  sup_bw_superposition:                   79
% 3.26/1.00  sup_immediate_simplified:               56
% 3.26/1.00  sup_given_eliminated:                   5
% 3.26/1.00  comparisons_done:                       0
% 3.26/1.00  comparisons_avoided:                    21
% 3.26/1.00  
% 3.26/1.00  ------ Simplifications
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  sim_fw_subset_subsumed:                 13
% 3.26/1.00  sim_bw_subset_subsumed:                 28
% 3.26/1.00  sim_fw_subsumed:                        7
% 3.26/1.00  sim_bw_subsumed:                        14
% 3.26/1.00  sim_fw_subsumption_res:                 3
% 3.26/1.00  sim_bw_subsumption_res:                 0
% 3.26/1.00  sim_tautology_del:                      9
% 3.26/1.00  sim_eq_tautology_del:                   19
% 3.26/1.00  sim_eq_res_simp:                        3
% 3.26/1.00  sim_fw_demodulated:                     13
% 3.26/1.00  sim_bw_demodulated:                     21
% 3.26/1.00  sim_light_normalised:                   34
% 3.26/1.00  sim_joinable_taut:                      0
% 3.26/1.00  sim_joinable_simp:                      0
% 3.26/1.00  sim_ac_normalised:                      0
% 3.26/1.00  sim_smt_subsumption:                    0
% 3.26/1.00  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:10 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  161 (1562 expanded)
%              Number of clauses        :   98 ( 464 expanded)
%              Number of leaves         :   17 ( 378 expanded)
%              Depth                    :   25
%              Number of atoms          :  545 (9830 expanded)
%              Number of equality atoms :  237 (2304 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK6)
        & ! [X4] :
            ( k1_funct_1(sK6,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK6,X0,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(sK5,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ r2_hidden(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f42,f41])).

fof(f72,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f75,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f74,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4906,plain,
    ( ~ r2_hidden(sK1(sK5,X0),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4908,plain,
    ( ~ r2_hidden(sK1(sK5,k1_xboole_0),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4906])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_494,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_496,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_26])).

cnf(c_2154,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2156,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2909,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2154,c_2156])).

cnf(c_3151,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_496,c_2909])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_505,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_507,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_29])).

cnf(c_2152,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2910,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2152,c_2156])).

cnf(c_3192,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_507,c_2910])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2159,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3599,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3151,c_2159])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_37,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2363,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2364,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2363])).

cnf(c_4484,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3599,c_35,c_37,c_2364])).

cnf(c_4485,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4484])).

cnf(c_4497,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3192,c_4485])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_411,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_2366,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2367,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2366])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2458,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2666,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2458])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2667,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1571,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2392,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1571])).

cnf(c_3154,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2392])).

cnf(c_4530,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4497,c_32,c_34,c_26,c_411,c_2367,c_2666,c_2667,c_3154])).

cnf(c_4536,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3192,c_4530])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2155,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4552,plain,
    ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4536,c_2155])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2160,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4589,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_2160])).

cnf(c_4590,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4589])).

cnf(c_4592,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4589,c_31,c_29,c_28,c_26,c_411,c_2363,c_2366,c_2666,c_2667,c_3154,c_4590])).

cnf(c_4596,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3151,c_4592])).

cnf(c_4660,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4596,c_3192])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2157,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3323,plain,
    ( v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2154,c_2157])).

cnf(c_4671,plain,
    ( v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4660,c_3323])).

cnf(c_3324,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2152,c_2157])).

cnf(c_4670,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4660,c_3324])).

cnf(c_4761,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4670])).

cnf(c_4218,plain,
    ( ~ r2_hidden(sK1(X0,sK5),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4220,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK5),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4218])).

cnf(c_3981,plain,
    ( ~ r2_hidden(sK1(sK6,X0),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3982,plain,
    ( r2_hidden(sK1(sK6,X0),sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3981])).

cnf(c_3984,plain,
    ( r2_hidden(sK1(sK6,k1_xboole_0),sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3982])).

cnf(c_3237,plain,
    ( ~ r2_hidden(sK1(X0,sK6),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3238,plain,
    ( r2_hidden(sK1(X0,sK6),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3237])).

cnf(c_3240,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3238])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2885,plain,
    ( r1_tarski(sK5,X0)
    | r2_hidden(sK1(sK5,X0),sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2897,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | r2_hidden(sK1(sK5,k1_xboole_0),sK5) ),
    inference(instantiation,[status(thm)],[c_2885])).

cnf(c_2865,plain,
    ( r1_tarski(sK6,X0)
    | r2_hidden(sK1(sK6,X0),sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2876,plain,
    ( r1_tarski(sK6,X0) = iProver_top
    | r2_hidden(sK1(sK6,X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2865])).

cnf(c_2878,plain,
    ( r1_tarski(sK6,k1_xboole_0) = iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2876])).

cnf(c_2686,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2688,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | sK5 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2686])).

cnf(c_2651,plain,
    ( r1_tarski(X0,sK5)
    | r2_hidden(sK1(X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2663,plain,
    ( r1_tarski(k1_xboole_0,sK5)
    | r2_hidden(sK1(k1_xboole_0,sK5),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2651])).

cnf(c_2630,plain,
    ( r1_tarski(X0,sK6)
    | r2_hidden(sK1(X0,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2641,plain,
    ( r1_tarski(X0,sK6) = iProver_top
    | r2_hidden(sK1(X0,sK6),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2630])).

cnf(c_2643,plain,
    ( r1_tarski(k1_xboole_0,sK6) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2641])).

cnf(c_2591,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2592,plain,
    ( sK6 = X0
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2591])).

cnf(c_2594,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2592])).

cnf(c_2393,plain,
    ( sK6 != k1_xboole_0
    | sK5 = sK6
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2392])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_92,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4908,c_4671,c_4761,c_4220,c_3984,c_3240,c_2897,c_2878,c_2688,c_2663,c_2643,c_2594,c_2393,c_411,c_92,c_5,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.76/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/0.98  
% 2.76/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.76/0.98  
% 2.76/0.98  ------  iProver source info
% 2.76/0.98  
% 2.76/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.76/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.76/0.98  git: non_committed_changes: false
% 2.76/0.98  git: last_make_outside_of_git: false
% 2.76/0.98  
% 2.76/0.98  ------ 
% 2.76/0.98  
% 2.76/0.98  ------ Input Options
% 2.76/0.98  
% 2.76/0.98  --out_options                           all
% 2.76/0.98  --tptp_safe_out                         true
% 2.76/0.98  --problem_path                          ""
% 2.76/0.98  --include_path                          ""
% 2.76/0.98  --clausifier                            res/vclausify_rel
% 2.76/0.98  --clausifier_options                    --mode clausify
% 2.76/0.98  --stdin                                 false
% 2.76/0.98  --stats_out                             all
% 2.76/0.98  
% 2.76/0.98  ------ General Options
% 2.76/0.98  
% 2.76/0.98  --fof                                   false
% 2.76/0.98  --time_out_real                         305.
% 2.76/0.98  --time_out_virtual                      -1.
% 2.76/0.98  --symbol_type_check                     false
% 2.76/0.98  --clausify_out                          false
% 2.76/0.98  --sig_cnt_out                           false
% 2.76/0.98  --trig_cnt_out                          false
% 2.76/0.98  --trig_cnt_out_tolerance                1.
% 2.76/0.98  --trig_cnt_out_sk_spl                   false
% 2.76/0.98  --abstr_cl_out                          false
% 2.76/0.98  
% 2.76/0.98  ------ Global Options
% 2.76/0.98  
% 2.76/0.98  --schedule                              default
% 2.76/0.98  --add_important_lit                     false
% 2.76/0.98  --prop_solver_per_cl                    1000
% 2.76/0.98  --min_unsat_core                        false
% 2.76/0.98  --soft_assumptions                      false
% 2.76/0.98  --soft_lemma_size                       3
% 2.76/0.98  --prop_impl_unit_size                   0
% 2.76/0.98  --prop_impl_unit                        []
% 2.76/0.98  --share_sel_clauses                     true
% 2.76/0.98  --reset_solvers                         false
% 2.76/0.98  --bc_imp_inh                            [conj_cone]
% 2.76/0.98  --conj_cone_tolerance                   3.
% 2.76/0.98  --extra_neg_conj                        none
% 2.76/0.98  --large_theory_mode                     true
% 2.76/0.98  --prolific_symb_bound                   200
% 2.76/0.98  --lt_threshold                          2000
% 2.76/0.98  --clause_weak_htbl                      true
% 2.76/0.98  --gc_record_bc_elim                     false
% 2.76/0.98  
% 2.76/0.98  ------ Preprocessing Options
% 2.76/0.98  
% 2.76/0.98  --preprocessing_flag                    true
% 2.76/0.98  --time_out_prep_mult                    0.1
% 2.76/0.98  --splitting_mode                        input
% 2.76/0.98  --splitting_grd                         true
% 2.76/0.98  --splitting_cvd                         false
% 2.76/0.98  --splitting_cvd_svl                     false
% 2.76/0.98  --splitting_nvd                         32
% 2.76/0.98  --sub_typing                            true
% 2.76/0.98  --prep_gs_sim                           true
% 2.76/0.98  --prep_unflatten                        true
% 2.76/0.98  --prep_res_sim                          true
% 2.76/0.98  --prep_upred                            true
% 2.76/0.98  --prep_sem_filter                       exhaustive
% 2.76/0.98  --prep_sem_filter_out                   false
% 2.76/0.98  --pred_elim                             true
% 2.76/0.98  --res_sim_input                         true
% 2.76/0.98  --eq_ax_congr_red                       true
% 2.76/0.98  --pure_diseq_elim                       true
% 2.76/0.98  --brand_transform                       false
% 2.76/0.98  --non_eq_to_eq                          false
% 2.76/0.98  --prep_def_merge                        true
% 2.76/0.98  --prep_def_merge_prop_impl              false
% 2.76/0.98  --prep_def_merge_mbd                    true
% 2.76/0.98  --prep_def_merge_tr_red                 false
% 2.76/0.98  --prep_def_merge_tr_cl                  false
% 2.76/0.98  --smt_preprocessing                     true
% 2.76/0.98  --smt_ac_axioms                         fast
% 2.76/0.98  --preprocessed_out                      false
% 2.76/0.98  --preprocessed_stats                    false
% 2.76/0.98  
% 2.76/0.98  ------ Abstraction refinement Options
% 2.76/0.98  
% 2.76/0.98  --abstr_ref                             []
% 2.76/0.98  --abstr_ref_prep                        false
% 2.76/0.98  --abstr_ref_until_sat                   false
% 2.76/0.98  --abstr_ref_sig_restrict                funpre
% 2.76/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/0.98  --abstr_ref_under                       []
% 2.76/0.98  
% 2.76/0.98  ------ SAT Options
% 2.76/0.98  
% 2.76/0.98  --sat_mode                              false
% 2.76/0.98  --sat_fm_restart_options                ""
% 2.76/0.98  --sat_gr_def                            false
% 2.76/0.98  --sat_epr_types                         true
% 2.76/0.98  --sat_non_cyclic_types                  false
% 2.76/0.98  --sat_finite_models                     false
% 2.76/0.98  --sat_fm_lemmas                         false
% 2.76/0.98  --sat_fm_prep                           false
% 2.76/0.98  --sat_fm_uc_incr                        true
% 2.76/0.98  --sat_out_model                         small
% 2.76/0.98  --sat_out_clauses                       false
% 2.76/0.98  
% 2.76/0.98  ------ QBF Options
% 2.76/0.98  
% 2.76/0.98  --qbf_mode                              false
% 2.76/0.98  --qbf_elim_univ                         false
% 2.76/0.98  --qbf_dom_inst                          none
% 2.76/0.98  --qbf_dom_pre_inst                      false
% 2.76/0.98  --qbf_sk_in                             false
% 2.76/0.98  --qbf_pred_elim                         true
% 2.76/0.98  --qbf_split                             512
% 2.76/0.98  
% 2.76/0.98  ------ BMC1 Options
% 2.76/0.98  
% 2.76/0.98  --bmc1_incremental                      false
% 2.76/0.98  --bmc1_axioms                           reachable_all
% 2.76/0.98  --bmc1_min_bound                        0
% 2.76/0.98  --bmc1_max_bound                        -1
% 2.76/0.98  --bmc1_max_bound_default                -1
% 2.76/0.98  --bmc1_symbol_reachability              true
% 2.76/0.98  --bmc1_property_lemmas                  false
% 2.76/0.98  --bmc1_k_induction                      false
% 2.76/0.98  --bmc1_non_equiv_states                 false
% 2.76/0.98  --bmc1_deadlock                         false
% 2.76/0.98  --bmc1_ucm                              false
% 2.76/0.98  --bmc1_add_unsat_core                   none
% 2.76/0.98  --bmc1_unsat_core_children              false
% 2.76/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/0.98  --bmc1_out_stat                         full
% 2.76/0.98  --bmc1_ground_init                      false
% 2.76/0.98  --bmc1_pre_inst_next_state              false
% 2.76/0.98  --bmc1_pre_inst_state                   false
% 2.76/0.98  --bmc1_pre_inst_reach_state             false
% 2.76/0.98  --bmc1_out_unsat_core                   false
% 2.76/0.98  --bmc1_aig_witness_out                  false
% 2.76/0.98  --bmc1_verbose                          false
% 2.76/0.98  --bmc1_dump_clauses_tptp                false
% 2.76/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.76/0.98  --bmc1_dump_file                        -
% 2.76/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.76/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.76/0.98  --bmc1_ucm_extend_mode                  1
% 2.76/0.98  --bmc1_ucm_init_mode                    2
% 2.76/0.98  --bmc1_ucm_cone_mode                    none
% 2.76/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.76/0.98  --bmc1_ucm_relax_model                  4
% 2.76/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.76/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/0.98  --bmc1_ucm_layered_model                none
% 2.76/0.98  --bmc1_ucm_max_lemma_size               10
% 2.76/0.98  
% 2.76/0.98  ------ AIG Options
% 2.76/0.98  
% 2.76/0.98  --aig_mode                              false
% 2.76/0.98  
% 2.76/0.98  ------ Instantiation Options
% 2.76/0.98  
% 2.76/0.98  --instantiation_flag                    true
% 2.76/0.98  --inst_sos_flag                         false
% 2.76/0.98  --inst_sos_phase                        true
% 2.76/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/0.98  --inst_lit_sel_side                     num_symb
% 2.76/0.98  --inst_solver_per_active                1400
% 2.76/0.98  --inst_solver_calls_frac                1.
% 2.76/0.98  --inst_passive_queue_type               priority_queues
% 2.76/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/0.98  --inst_passive_queues_freq              [25;2]
% 2.76/0.98  --inst_dismatching                      true
% 2.76/0.98  --inst_eager_unprocessed_to_passive     true
% 2.76/0.98  --inst_prop_sim_given                   true
% 2.76/0.98  --inst_prop_sim_new                     false
% 2.76/0.98  --inst_subs_new                         false
% 2.76/0.98  --inst_eq_res_simp                      false
% 2.76/0.98  --inst_subs_given                       false
% 2.76/0.98  --inst_orphan_elimination               true
% 2.76/0.98  --inst_learning_loop_flag               true
% 2.76/0.98  --inst_learning_start                   3000
% 2.76/0.98  --inst_learning_factor                  2
% 2.76/0.98  --inst_start_prop_sim_after_learn       3
% 2.76/0.98  --inst_sel_renew                        solver
% 2.76/0.98  --inst_lit_activity_flag                true
% 2.76/0.98  --inst_restr_to_given                   false
% 2.76/0.98  --inst_activity_threshold               500
% 2.76/0.98  --inst_out_proof                        true
% 2.76/0.98  
% 2.76/0.98  ------ Resolution Options
% 2.76/0.98  
% 2.76/0.98  --resolution_flag                       true
% 2.76/0.98  --res_lit_sel                           adaptive
% 2.76/0.98  --res_lit_sel_side                      none
% 2.76/0.98  --res_ordering                          kbo
% 2.76/0.98  --res_to_prop_solver                    active
% 2.76/0.98  --res_prop_simpl_new                    false
% 2.76/0.98  --res_prop_simpl_given                  true
% 2.76/0.98  --res_passive_queue_type                priority_queues
% 2.76/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/0.98  --res_passive_queues_freq               [15;5]
% 2.76/0.98  --res_forward_subs                      full
% 2.76/0.98  --res_backward_subs                     full
% 2.76/0.98  --res_forward_subs_resolution           true
% 2.76/0.98  --res_backward_subs_resolution          true
% 2.76/0.98  --res_orphan_elimination                true
% 2.76/0.98  --res_time_limit                        2.
% 2.76/0.98  --res_out_proof                         true
% 2.76/0.98  
% 2.76/0.98  ------ Superposition Options
% 2.76/0.98  
% 2.76/0.98  --superposition_flag                    true
% 2.76/0.98  --sup_passive_queue_type                priority_queues
% 2.76/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.76/0.98  --demod_completeness_check              fast
% 2.76/0.98  --demod_use_ground                      true
% 2.76/0.98  --sup_to_prop_solver                    passive
% 2.76/0.98  --sup_prop_simpl_new                    true
% 2.76/0.98  --sup_prop_simpl_given                  true
% 2.76/0.98  --sup_fun_splitting                     false
% 2.76/0.98  --sup_smt_interval                      50000
% 2.76/0.98  
% 2.76/0.98  ------ Superposition Simplification Setup
% 2.76/0.98  
% 2.76/0.98  --sup_indices_passive                   []
% 2.76/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.98  --sup_full_bw                           [BwDemod]
% 2.76/0.98  --sup_immed_triv                        [TrivRules]
% 2.76/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.98  --sup_immed_bw_main                     []
% 2.76/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.98  
% 2.76/0.98  ------ Combination Options
% 2.76/0.98  
% 2.76/0.98  --comb_res_mult                         3
% 2.76/0.98  --comb_sup_mult                         2
% 2.76/0.98  --comb_inst_mult                        10
% 2.76/0.98  
% 2.76/0.98  ------ Debug Options
% 2.76/0.98  
% 2.76/0.98  --dbg_backtrace                         false
% 2.76/0.98  --dbg_dump_prop_clauses                 false
% 2.76/0.98  --dbg_dump_prop_clauses_file            -
% 2.76/0.98  --dbg_out_stat                          false
% 2.76/0.98  ------ Parsing...
% 2.76/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.76/0.98  
% 2.76/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.76/0.98  
% 2.76/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.76/0.98  
% 2.76/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.76/0.98  ------ Proving...
% 2.76/0.98  ------ Problem Properties 
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  clauses                                 27
% 2.76/0.98  conjectures                             5
% 2.76/0.98  EPR                                     8
% 2.76/0.98  Horn                                    20
% 2.76/0.98  unary                                   7
% 2.76/0.98  binary                                  11
% 2.76/0.98  lits                                    66
% 2.76/0.98  lits eq                                 23
% 2.76/0.98  fd_pure                                 0
% 2.76/0.98  fd_pseudo                               0
% 2.76/0.98  fd_cond                                 0
% 2.76/0.98  fd_pseudo_cond                          3
% 2.76/0.98  AC symbols                              0
% 2.76/0.98  
% 2.76/0.98  ------ Schedule dynamic 5 is on 
% 2.76/0.98  
% 2.76/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  ------ 
% 2.76/0.98  Current options:
% 2.76/0.98  ------ 
% 2.76/0.98  
% 2.76/0.98  ------ Input Options
% 2.76/0.98  
% 2.76/0.98  --out_options                           all
% 2.76/0.98  --tptp_safe_out                         true
% 2.76/0.98  --problem_path                          ""
% 2.76/0.98  --include_path                          ""
% 2.76/0.98  --clausifier                            res/vclausify_rel
% 2.76/0.98  --clausifier_options                    --mode clausify
% 2.76/0.98  --stdin                                 false
% 2.76/0.98  --stats_out                             all
% 2.76/0.98  
% 2.76/0.98  ------ General Options
% 2.76/0.98  
% 2.76/0.98  --fof                                   false
% 2.76/0.98  --time_out_real                         305.
% 2.76/0.98  --time_out_virtual                      -1.
% 2.76/0.98  --symbol_type_check                     false
% 2.76/0.98  --clausify_out                          false
% 2.76/0.98  --sig_cnt_out                           false
% 2.76/0.98  --trig_cnt_out                          false
% 2.76/0.98  --trig_cnt_out_tolerance                1.
% 2.76/0.98  --trig_cnt_out_sk_spl                   false
% 2.76/0.98  --abstr_cl_out                          false
% 2.76/0.98  
% 2.76/0.98  ------ Global Options
% 2.76/0.98  
% 2.76/0.98  --schedule                              default
% 2.76/0.98  --add_important_lit                     false
% 2.76/0.98  --prop_solver_per_cl                    1000
% 2.76/0.98  --min_unsat_core                        false
% 2.76/0.98  --soft_assumptions                      false
% 2.76/0.98  --soft_lemma_size                       3
% 2.76/0.98  --prop_impl_unit_size                   0
% 2.76/0.98  --prop_impl_unit                        []
% 2.76/0.98  --share_sel_clauses                     true
% 2.76/0.98  --reset_solvers                         false
% 2.76/0.98  --bc_imp_inh                            [conj_cone]
% 2.76/0.98  --conj_cone_tolerance                   3.
% 2.76/0.98  --extra_neg_conj                        none
% 2.76/0.98  --large_theory_mode                     true
% 2.76/0.98  --prolific_symb_bound                   200
% 2.76/0.98  --lt_threshold                          2000
% 2.76/0.98  --clause_weak_htbl                      true
% 2.76/0.98  --gc_record_bc_elim                     false
% 2.76/0.98  
% 2.76/0.98  ------ Preprocessing Options
% 2.76/0.98  
% 2.76/0.98  --preprocessing_flag                    true
% 2.76/0.98  --time_out_prep_mult                    0.1
% 2.76/0.98  --splitting_mode                        input
% 2.76/0.98  --splitting_grd                         true
% 2.76/0.98  --splitting_cvd                         false
% 2.76/0.98  --splitting_cvd_svl                     false
% 2.76/0.98  --splitting_nvd                         32
% 2.76/0.98  --sub_typing                            true
% 2.76/0.98  --prep_gs_sim                           true
% 2.76/0.98  --prep_unflatten                        true
% 2.76/0.98  --prep_res_sim                          true
% 2.76/0.98  --prep_upred                            true
% 2.76/0.98  --prep_sem_filter                       exhaustive
% 2.76/0.98  --prep_sem_filter_out                   false
% 2.76/0.98  --pred_elim                             true
% 2.76/0.98  --res_sim_input                         true
% 2.76/0.98  --eq_ax_congr_red                       true
% 2.76/0.98  --pure_diseq_elim                       true
% 2.76/0.98  --brand_transform                       false
% 2.76/0.98  --non_eq_to_eq                          false
% 2.76/0.98  --prep_def_merge                        true
% 2.76/0.98  --prep_def_merge_prop_impl              false
% 2.76/0.98  --prep_def_merge_mbd                    true
% 2.76/0.98  --prep_def_merge_tr_red                 false
% 2.76/0.98  --prep_def_merge_tr_cl                  false
% 2.76/0.98  --smt_preprocessing                     true
% 2.76/0.98  --smt_ac_axioms                         fast
% 2.76/0.98  --preprocessed_out                      false
% 2.76/0.98  --preprocessed_stats                    false
% 2.76/0.98  
% 2.76/0.98  ------ Abstraction refinement Options
% 2.76/0.98  
% 2.76/0.98  --abstr_ref                             []
% 2.76/0.98  --abstr_ref_prep                        false
% 2.76/0.98  --abstr_ref_until_sat                   false
% 2.76/0.98  --abstr_ref_sig_restrict                funpre
% 2.76/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/0.98  --abstr_ref_under                       []
% 2.76/0.98  
% 2.76/0.98  ------ SAT Options
% 2.76/0.98  
% 2.76/0.98  --sat_mode                              false
% 2.76/0.98  --sat_fm_restart_options                ""
% 2.76/0.98  --sat_gr_def                            false
% 2.76/0.98  --sat_epr_types                         true
% 2.76/0.98  --sat_non_cyclic_types                  false
% 2.76/0.98  --sat_finite_models                     false
% 2.76/0.98  --sat_fm_lemmas                         false
% 2.76/0.98  --sat_fm_prep                           false
% 2.76/0.98  --sat_fm_uc_incr                        true
% 2.76/0.98  --sat_out_model                         small
% 2.76/0.98  --sat_out_clauses                       false
% 2.76/0.98  
% 2.76/0.98  ------ QBF Options
% 2.76/0.98  
% 2.76/0.98  --qbf_mode                              false
% 2.76/0.98  --qbf_elim_univ                         false
% 2.76/0.98  --qbf_dom_inst                          none
% 2.76/0.98  --qbf_dom_pre_inst                      false
% 2.76/0.98  --qbf_sk_in                             false
% 2.76/0.98  --qbf_pred_elim                         true
% 2.76/0.98  --qbf_split                             512
% 2.76/0.98  
% 2.76/0.98  ------ BMC1 Options
% 2.76/0.98  
% 2.76/0.98  --bmc1_incremental                      false
% 2.76/0.98  --bmc1_axioms                           reachable_all
% 2.76/0.98  --bmc1_min_bound                        0
% 2.76/0.98  --bmc1_max_bound                        -1
% 2.76/0.98  --bmc1_max_bound_default                -1
% 2.76/0.98  --bmc1_symbol_reachability              true
% 2.76/0.98  --bmc1_property_lemmas                  false
% 2.76/0.98  --bmc1_k_induction                      false
% 2.76/0.98  --bmc1_non_equiv_states                 false
% 2.76/0.98  --bmc1_deadlock                         false
% 2.76/0.98  --bmc1_ucm                              false
% 2.76/0.98  --bmc1_add_unsat_core                   none
% 2.76/0.98  --bmc1_unsat_core_children              false
% 2.76/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/0.98  --bmc1_out_stat                         full
% 2.76/0.98  --bmc1_ground_init                      false
% 2.76/0.98  --bmc1_pre_inst_next_state              false
% 2.76/0.98  --bmc1_pre_inst_state                   false
% 2.76/0.98  --bmc1_pre_inst_reach_state             false
% 2.76/0.98  --bmc1_out_unsat_core                   false
% 2.76/0.98  --bmc1_aig_witness_out                  false
% 2.76/0.98  --bmc1_verbose                          false
% 2.76/0.98  --bmc1_dump_clauses_tptp                false
% 2.76/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.76/0.98  --bmc1_dump_file                        -
% 2.76/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.76/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.76/0.98  --bmc1_ucm_extend_mode                  1
% 2.76/0.98  --bmc1_ucm_init_mode                    2
% 2.76/0.98  --bmc1_ucm_cone_mode                    none
% 2.76/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.76/0.98  --bmc1_ucm_relax_model                  4
% 2.76/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.76/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/0.98  --bmc1_ucm_layered_model                none
% 2.76/0.98  --bmc1_ucm_max_lemma_size               10
% 2.76/0.98  
% 2.76/0.98  ------ AIG Options
% 2.76/0.98  
% 2.76/0.98  --aig_mode                              false
% 2.76/0.98  
% 2.76/0.98  ------ Instantiation Options
% 2.76/0.98  
% 2.76/0.98  --instantiation_flag                    true
% 2.76/0.98  --inst_sos_flag                         false
% 2.76/0.98  --inst_sos_phase                        true
% 2.76/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/0.98  --inst_lit_sel_side                     none
% 2.76/0.98  --inst_solver_per_active                1400
% 2.76/0.98  --inst_solver_calls_frac                1.
% 2.76/0.98  --inst_passive_queue_type               priority_queues
% 2.76/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/0.98  --inst_passive_queues_freq              [25;2]
% 2.76/0.98  --inst_dismatching                      true
% 2.76/0.98  --inst_eager_unprocessed_to_passive     true
% 2.76/0.98  --inst_prop_sim_given                   true
% 2.76/0.98  --inst_prop_sim_new                     false
% 2.76/0.98  --inst_subs_new                         false
% 2.76/0.98  --inst_eq_res_simp                      false
% 2.76/0.98  --inst_subs_given                       false
% 2.76/0.98  --inst_orphan_elimination               true
% 2.76/0.98  --inst_learning_loop_flag               true
% 2.76/0.98  --inst_learning_start                   3000
% 2.76/0.98  --inst_learning_factor                  2
% 2.76/0.98  --inst_start_prop_sim_after_learn       3
% 2.76/0.98  --inst_sel_renew                        solver
% 2.76/0.98  --inst_lit_activity_flag                true
% 2.76/0.98  --inst_restr_to_given                   false
% 2.76/0.98  --inst_activity_threshold               500
% 2.76/0.98  --inst_out_proof                        true
% 2.76/0.98  
% 2.76/0.98  ------ Resolution Options
% 2.76/0.98  
% 2.76/0.98  --resolution_flag                       false
% 2.76/0.98  --res_lit_sel                           adaptive
% 2.76/0.98  --res_lit_sel_side                      none
% 2.76/0.98  --res_ordering                          kbo
% 2.76/0.98  --res_to_prop_solver                    active
% 2.76/0.98  --res_prop_simpl_new                    false
% 2.76/0.98  --res_prop_simpl_given                  true
% 2.76/0.98  --res_passive_queue_type                priority_queues
% 2.76/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/0.98  --res_passive_queues_freq               [15;5]
% 2.76/0.98  --res_forward_subs                      full
% 2.76/0.98  --res_backward_subs                     full
% 2.76/0.98  --res_forward_subs_resolution           true
% 2.76/0.98  --res_backward_subs_resolution          true
% 2.76/0.98  --res_orphan_elimination                true
% 2.76/0.98  --res_time_limit                        2.
% 2.76/0.98  --res_out_proof                         true
% 2.76/0.98  
% 2.76/0.98  ------ Superposition Options
% 2.76/0.98  
% 2.76/0.98  --superposition_flag                    true
% 2.76/0.98  --sup_passive_queue_type                priority_queues
% 2.76/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.76/0.98  --demod_completeness_check              fast
% 2.76/0.98  --demod_use_ground                      true
% 2.76/0.98  --sup_to_prop_solver                    passive
% 2.76/0.98  --sup_prop_simpl_new                    true
% 2.76/0.98  --sup_prop_simpl_given                  true
% 2.76/0.98  --sup_fun_splitting                     false
% 2.76/0.98  --sup_smt_interval                      50000
% 2.76/0.98  
% 2.76/0.98  ------ Superposition Simplification Setup
% 2.76/0.98  
% 2.76/0.98  --sup_indices_passive                   []
% 2.76/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.98  --sup_full_bw                           [BwDemod]
% 2.76/0.98  --sup_immed_triv                        [TrivRules]
% 2.76/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.98  --sup_immed_bw_main                     []
% 2.76/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.98  
% 2.76/0.98  ------ Combination Options
% 2.76/0.98  
% 2.76/0.98  --comb_res_mult                         3
% 2.76/0.98  --comb_sup_mult                         2
% 2.76/0.98  --comb_inst_mult                        10
% 2.76/0.98  
% 2.76/0.98  ------ Debug Options
% 2.76/0.98  
% 2.76/0.98  --dbg_backtrace                         false
% 2.76/0.98  --dbg_dump_prop_clauses                 false
% 2.76/0.98  --dbg_dump_prop_clauses_file            -
% 2.76/0.98  --dbg_out_stat                          false
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  ------ Proving...
% 2.76/0.98  
% 2.76/0.98  
% 2.76/0.98  % SZS status Theorem for theBenchmark.p
% 2.76/0.98  
% 2.76/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.76/0.98  
% 2.76/0.98  fof(f1,axiom,(
% 2.76/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f26,plain,(
% 2.76/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.76/0.98    inference(nnf_transformation,[],[f1])).
% 2.76/0.98  
% 2.76/0.98  fof(f27,plain,(
% 2.76/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.76/0.98    inference(rectify,[],[f26])).
% 2.76/0.98  
% 2.76/0.98  fof(f28,plain,(
% 2.76/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.76/0.98    introduced(choice_axiom,[])).
% 2.76/0.98  
% 2.76/0.98  fof(f29,plain,(
% 2.76/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.76/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.76/0.98  
% 2.76/0.98  fof(f44,plain,(
% 2.76/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f29])).
% 2.76/0.98  
% 2.76/0.98  fof(f11,axiom,(
% 2.76/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f22,plain,(
% 2.76/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.98    inference(ennf_transformation,[],[f11])).
% 2.76/0.98  
% 2.76/0.98  fof(f23,plain,(
% 2.76/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.98    inference(flattening,[],[f22])).
% 2.76/0.98  
% 2.76/0.98  fof(f40,plain,(
% 2.76/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.98    inference(nnf_transformation,[],[f23])).
% 2.76/0.98  
% 2.76/0.98  fof(f62,plain,(
% 2.76/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.98    inference(cnf_transformation,[],[f40])).
% 2.76/0.98  
% 2.76/0.98  fof(f12,conjecture,(
% 2.76/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f13,negated_conjecture,(
% 2.76/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.76/0.98    inference(negated_conjecture,[],[f12])).
% 2.76/0.98  
% 2.76/0.98  fof(f24,plain,(
% 2.76/0.98    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.76/0.98    inference(ennf_transformation,[],[f13])).
% 2.76/0.98  
% 2.76/0.98  fof(f25,plain,(
% 2.76/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.76/0.98    inference(flattening,[],[f24])).
% 2.76/0.98  
% 2.76/0.98  fof(f42,plain,(
% 2.76/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 2.76/0.98    introduced(choice_axiom,[])).
% 2.76/0.98  
% 2.76/0.98  fof(f41,plain,(
% 2.76/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 2.76/0.98    introduced(choice_axiom,[])).
% 2.76/0.98  
% 2.76/0.98  fof(f43,plain,(
% 2.76/0.98    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 2.76/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f42,f41])).
% 2.76/0.98  
% 2.76/0.98  fof(f72,plain,(
% 2.76/0.98    v1_funct_2(sK6,sK3,sK4)),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f73,plain,(
% 2.76/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f9,axiom,(
% 2.76/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f19,plain,(
% 2.76/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.98    inference(ennf_transformation,[],[f9])).
% 2.76/0.98  
% 2.76/0.98  fof(f59,plain,(
% 2.76/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.98    inference(cnf_transformation,[],[f19])).
% 2.76/0.98  
% 2.76/0.98  fof(f69,plain,(
% 2.76/0.98    v1_funct_2(sK5,sK3,sK4)),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f70,plain,(
% 2.76/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f6,axiom,(
% 2.76/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f15,plain,(
% 2.76/0.98    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.76/0.98    inference(ennf_transformation,[],[f6])).
% 2.76/0.98  
% 2.76/0.98  fof(f16,plain,(
% 2.76/0.98    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.76/0.98    inference(flattening,[],[f15])).
% 2.76/0.98  
% 2.76/0.98  fof(f37,plain,(
% 2.76/0.98    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 2.76/0.98    introduced(choice_axiom,[])).
% 2.76/0.98  
% 2.76/0.98  fof(f38,plain,(
% 2.76/0.98    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.76/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f37])).
% 2.76/0.98  
% 2.76/0.98  fof(f55,plain,(
% 2.76/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f38])).
% 2.76/0.98  
% 2.76/0.98  fof(f71,plain,(
% 2.76/0.98    v1_funct_1(sK6)),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f7,axiom,(
% 2.76/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f17,plain,(
% 2.76/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.98    inference(ennf_transformation,[],[f7])).
% 2.76/0.98  
% 2.76/0.98  fof(f57,plain,(
% 2.76/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.98    inference(cnf_transformation,[],[f17])).
% 2.76/0.98  
% 2.76/0.98  fof(f68,plain,(
% 2.76/0.98    v1_funct_1(sK5)),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f10,axiom,(
% 2.76/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f20,plain,(
% 2.76/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.76/0.98    inference(ennf_transformation,[],[f10])).
% 2.76/0.98  
% 2.76/0.98  fof(f21,plain,(
% 2.76/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.98    inference(flattening,[],[f20])).
% 2.76/0.98  
% 2.76/0.98  fof(f39,plain,(
% 2.76/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.98    inference(nnf_transformation,[],[f21])).
% 2.76/0.98  
% 2.76/0.98  fof(f61,plain,(
% 2.76/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.98    inference(cnf_transformation,[],[f39])).
% 2.76/0.98  
% 2.76/0.98  fof(f78,plain,(
% 2.76/0.98    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.98    inference(equality_resolution,[],[f61])).
% 2.76/0.98  
% 2.76/0.98  fof(f75,plain,(
% 2.76/0.98    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f4,axiom,(
% 2.76/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f34,plain,(
% 2.76/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.76/0.98    inference(nnf_transformation,[],[f4])).
% 2.76/0.98  
% 2.76/0.98  fof(f35,plain,(
% 2.76/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.76/0.98    inference(flattening,[],[f34])).
% 2.76/0.98  
% 2.76/0.98  fof(f52,plain,(
% 2.76/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f35])).
% 2.76/0.98  
% 2.76/0.98  fof(f50,plain,(
% 2.76/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.76/0.98    inference(cnf_transformation,[],[f35])).
% 2.76/0.98  
% 2.76/0.98  fof(f77,plain,(
% 2.76/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.76/0.98    inference(equality_resolution,[],[f50])).
% 2.76/0.98  
% 2.76/0.98  fof(f74,plain,(
% 2.76/0.98    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f43])).
% 2.76/0.98  
% 2.76/0.98  fof(f56,plain,(
% 2.76/0.98    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f38])).
% 2.76/0.98  
% 2.76/0.98  fof(f8,axiom,(
% 2.76/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f18,plain,(
% 2.76/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.76/0.98    inference(ennf_transformation,[],[f8])).
% 2.76/0.98  
% 2.76/0.98  fof(f58,plain,(
% 2.76/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f18])).
% 2.76/0.98  
% 2.76/0.98  fof(f2,axiom,(
% 2.76/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f14,plain,(
% 2.76/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.76/0.98    inference(ennf_transformation,[],[f2])).
% 2.76/0.98  
% 2.76/0.98  fof(f30,plain,(
% 2.76/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.76/0.98    inference(nnf_transformation,[],[f14])).
% 2.76/0.98  
% 2.76/0.98  fof(f31,plain,(
% 2.76/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.76/0.98    inference(rectify,[],[f30])).
% 2.76/0.98  
% 2.76/0.98  fof(f32,plain,(
% 2.76/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.76/0.98    introduced(choice_axiom,[])).
% 2.76/0.98  
% 2.76/0.98  fof(f33,plain,(
% 2.76/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.76/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 2.76/0.98  
% 2.76/0.98  fof(f47,plain,(
% 2.76/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.76/0.98    inference(cnf_transformation,[],[f33])).
% 2.76/0.98  
% 2.76/0.98  fof(f3,axiom,(
% 2.76/0.98    v1_xboole_0(k1_xboole_0)),
% 2.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.98  
% 2.76/0.98  fof(f49,plain,(
% 2.76/0.98    v1_xboole_0(k1_xboole_0)),
% 2.76/0.98    inference(cnf_transformation,[],[f3])).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1,plain,
% 2.76/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.76/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4906,plain,
% 2.76/0.98      ( ~ r2_hidden(sK1(sK5,X0),sK5) | ~ v1_xboole_0(sK5) ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4908,plain,
% 2.76/0.98      ( ~ r2_hidden(sK1(sK5,k1_xboole_0),sK5) | ~ v1_xboole_0(sK5) ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_4906]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_23,plain,
% 2.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.76/0.98      | k1_xboole_0 = X2 ),
% 2.76/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_27,negated_conjecture,
% 2.76/0.98      ( v1_funct_2(sK6,sK3,sK4) ),
% 2.76/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_493,plain,
% 2.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.76/0.98      | sK6 != X0
% 2.76/0.98      | sK4 != X2
% 2.76/0.98      | sK3 != X1
% 2.76/0.98      | k1_xboole_0 = X2 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_494,plain,
% 2.76/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.76/0.98      | k1_relset_1(sK3,sK4,sK6) = sK3
% 2.76/0.98      | k1_xboole_0 = sK4 ),
% 2.76/0.98      inference(unflattening,[status(thm)],[c_493]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_26,negated_conjecture,
% 2.76/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.76/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_496,plain,
% 2.76/0.98      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_494,c_26]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2154,plain,
% 2.76/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_15,plain,
% 2.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2156,plain,
% 2.76/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.76/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2909,plain,
% 2.76/0.98      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_2154,c_2156]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3151,plain,
% 2.76/0.98      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_496,c_2909]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_30,negated_conjecture,
% 2.76/0.98      ( v1_funct_2(sK5,sK3,sK4) ),
% 2.76/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_504,plain,
% 2.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.76/0.98      | sK5 != X0
% 2.76/0.98      | sK4 != X2
% 2.76/0.98      | sK3 != X1
% 2.76/0.98      | k1_xboole_0 = X2 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_505,plain,
% 2.76/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.76/0.98      | k1_relset_1(sK3,sK4,sK5) = sK3
% 2.76/0.98      | k1_xboole_0 = sK4 ),
% 2.76/0.98      inference(unflattening,[status(thm)],[c_504]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_29,negated_conjecture,
% 2.76/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.76/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_507,plain,
% 2.76/0.98      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_505,c_29]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2152,plain,
% 2.76/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2910,plain,
% 2.76/0.98      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_2152,c_2156]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3192,plain,
% 2.76/0.98      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_507,c_2910]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_12,plain,
% 2.76/0.98      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 2.76/0.98      | ~ v1_relat_1(X1)
% 2.76/0.98      | ~ v1_relat_1(X0)
% 2.76/0.98      | ~ v1_funct_1(X1)
% 2.76/0.98      | ~ v1_funct_1(X0)
% 2.76/0.98      | X1 = X0
% 2.76/0.98      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2159,plain,
% 2.76/0.98      ( X0 = X1
% 2.76/0.98      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.76/0.98      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.76/0.98      | v1_relat_1(X1) != iProver_top
% 2.76/0.98      | v1_relat_1(X0) != iProver_top
% 2.76/0.98      | v1_funct_1(X0) != iProver_top
% 2.76/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3599,plain,
% 2.76/0.98      ( k1_relat_1(X0) != sK3
% 2.76/0.98      | sK6 = X0
% 2.76/0.98      | sK4 = k1_xboole_0
% 2.76/0.98      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.76/0.98      | v1_relat_1(X0) != iProver_top
% 2.76/0.98      | v1_relat_1(sK6) != iProver_top
% 2.76/0.98      | v1_funct_1(X0) != iProver_top
% 2.76/0.98      | v1_funct_1(sK6) != iProver_top ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_3151,c_2159]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_28,negated_conjecture,
% 2.76/0.98      ( v1_funct_1(sK6) ),
% 2.76/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_35,plain,
% 2.76/0.98      ( v1_funct_1(sK6) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_37,plain,
% 2.76/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_13,plain,
% 2.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | v1_relat_1(X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2363,plain,
% 2.76/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.76/0.98      | v1_relat_1(sK6) ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2364,plain,
% 2.76/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.76/0.98      | v1_relat_1(sK6) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_2363]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4484,plain,
% 2.76/0.98      ( v1_funct_1(X0) != iProver_top
% 2.76/0.98      | k1_relat_1(X0) != sK3
% 2.76/0.98      | sK6 = X0
% 2.76/0.98      | sK4 = k1_xboole_0
% 2.76/0.98      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.76/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_3599,c_35,c_37,c_2364]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4485,plain,
% 2.76/0.98      ( k1_relat_1(X0) != sK3
% 2.76/0.98      | sK6 = X0
% 2.76/0.98      | sK4 = k1_xboole_0
% 2.76/0.98      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.76/0.98      | v1_relat_1(X0) != iProver_top
% 2.76/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.76/0.98      inference(renaming,[status(thm)],[c_4484]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4497,plain,
% 2.76/0.98      ( sK6 = sK5
% 2.76/0.98      | sK4 = k1_xboole_0
% 2.76/0.98      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
% 2.76/0.98      | v1_relat_1(sK5) != iProver_top
% 2.76/0.98      | v1_funct_1(sK5) != iProver_top ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_3192,c_4485]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_31,negated_conjecture,
% 2.76/0.98      ( v1_funct_1(sK5) ),
% 2.76/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_32,plain,
% 2.76/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_34,plain,
% 2.76/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_16,plain,
% 2.76/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 2.76/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.76/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_24,negated_conjecture,
% 2.76/0.98      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 2.76/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_410,plain,
% 2.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | sK6 != X0
% 2.76/0.98      | sK5 != X0
% 2.76/0.98      | sK4 != X2
% 2.76/0.98      | sK3 != X1 ),
% 2.76/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_411,plain,
% 2.76/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.76/0.98      | sK5 != sK6 ),
% 2.76/0.98      inference(unflattening,[status(thm)],[c_410]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2366,plain,
% 2.76/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.76/0.98      | v1_relat_1(sK5) ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2367,plain,
% 2.76/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.76/0.98      | v1_relat_1(sK5) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_2366]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_6,plain,
% 2.76/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.76/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2458,plain,
% 2.76/0.98      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | X0 = sK5 ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2666,plain,
% 2.76/0.98      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_2458]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_8,plain,
% 2.76/0.98      ( r1_tarski(X0,X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2667,plain,
% 2.76/0.98      ( r1_tarski(sK5,sK5) ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_1571,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2392,plain,
% 2.76/0.98      ( sK6 != X0 | sK5 != X0 | sK5 = sK6 ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_1571]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3154,plain,
% 2.76/0.98      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_2392]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4530,plain,
% 2.76/0.98      ( sK4 = k1_xboole_0
% 2.76/0.98      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_4497,c_32,c_34,c_26,c_411,c_2367,c_2666,c_2667,c_3154]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4536,plain,
% 2.76/0.98      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_3192,c_4530]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_25,negated_conjecture,
% 2.76/0.98      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2155,plain,
% 2.76/0.98      ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
% 2.76/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4552,plain,
% 2.76/0.98      ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
% 2.76/0.98      | sK4 = k1_xboole_0 ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_4536,c_2155]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_11,plain,
% 2.76/0.98      ( ~ v1_relat_1(X0)
% 2.76/0.98      | ~ v1_relat_1(X1)
% 2.76/0.98      | ~ v1_funct_1(X0)
% 2.76/0.98      | ~ v1_funct_1(X1)
% 2.76/0.98      | X0 = X1
% 2.76/0.98      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 2.76/0.98      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.76/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2160,plain,
% 2.76/0.98      ( X0 = X1
% 2.76/0.98      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 2.76/0.98      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.76/0.98      | v1_relat_1(X0) != iProver_top
% 2.76/0.98      | v1_relat_1(X1) != iProver_top
% 2.76/0.98      | v1_funct_1(X1) != iProver_top
% 2.76/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4589,plain,
% 2.76/0.98      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 2.76/0.98      | sK6 = sK5
% 2.76/0.98      | sK4 = k1_xboole_0
% 2.76/0.98      | v1_relat_1(sK6) != iProver_top
% 2.76/0.98      | v1_relat_1(sK5) != iProver_top
% 2.76/0.98      | v1_funct_1(sK6) != iProver_top
% 2.76/0.98      | v1_funct_1(sK5) != iProver_top ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_4552,c_2160]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4590,plain,
% 2.76/0.98      ( ~ v1_relat_1(sK6)
% 2.76/0.98      | ~ v1_relat_1(sK5)
% 2.76/0.98      | ~ v1_funct_1(sK6)
% 2.76/0.98      | ~ v1_funct_1(sK5)
% 2.76/0.98      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 2.76/0.98      | sK6 = sK5
% 2.76/0.98      | sK4 = k1_xboole_0 ),
% 2.76/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4589]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4592,plain,
% 2.76/0.98      ( k1_relat_1(sK5) != k1_relat_1(sK6) | sK4 = k1_xboole_0 ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_4589,c_31,c_29,c_28,c_26,c_411,c_2363,c_2366,c_2666,
% 2.76/0.98                 c_2667,c_3154,c_4590]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4596,plain,
% 2.76/0.98      ( k1_relat_1(sK5) != sK3 | sK4 = k1_xboole_0 ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_3151,c_4592]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4660,plain,
% 2.76/0.98      ( sK4 = k1_xboole_0 ),
% 2.76/0.98      inference(global_propositional_subsumption,
% 2.76/0.98                [status(thm)],
% 2.76/0.98                [c_4596,c_3192]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_14,plain,
% 2.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.98      | ~ v1_xboole_0(X2)
% 2.76/0.98      | v1_xboole_0(X0) ),
% 2.76/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_2157,plain,
% 2.76/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.76/0.98      | v1_xboole_0(X2) != iProver_top
% 2.76/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3323,plain,
% 2.76/0.98      ( v1_xboole_0(sK6) = iProver_top
% 2.76/0.98      | v1_xboole_0(sK4) != iProver_top ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_2154,c_2157]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4671,plain,
% 2.76/0.98      ( v1_xboole_0(sK6) = iProver_top
% 2.76/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.76/0.98      inference(demodulation,[status(thm)],[c_4660,c_3323]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3324,plain,
% 2.76/0.98      ( v1_xboole_0(sK5) = iProver_top
% 2.76/0.98      | v1_xboole_0(sK4) != iProver_top ),
% 2.76/0.98      inference(superposition,[status(thm)],[c_2152,c_2157]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4670,plain,
% 2.76/0.98      ( v1_xboole_0(sK5) = iProver_top
% 2.76/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.76/0.98      inference(demodulation,[status(thm)],[c_4660,c_3324]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4761,plain,
% 2.76/0.98      ( v1_xboole_0(sK5) | ~ v1_xboole_0(k1_xboole_0) ),
% 2.76/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4670]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4218,plain,
% 2.76/0.98      ( ~ r2_hidden(sK1(X0,sK5),X0) | ~ v1_xboole_0(X0) ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_4220,plain,
% 2.76/0.98      ( ~ r2_hidden(sK1(k1_xboole_0,sK5),k1_xboole_0)
% 2.76/0.98      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_4218]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3981,plain,
% 2.76/0.98      ( ~ r2_hidden(sK1(sK6,X0),sK6) | ~ v1_xboole_0(sK6) ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3982,plain,
% 2.76/0.98      ( r2_hidden(sK1(sK6,X0),sK6) != iProver_top
% 2.76/0.98      | v1_xboole_0(sK6) != iProver_top ),
% 2.76/0.98      inference(predicate_to_equality,[status(thm)],[c_3981]) ).
% 2.76/0.98  
% 2.76/0.98  cnf(c_3984,plain,
% 2.76/0.98      ( r2_hidden(sK1(sK6,k1_xboole_0),sK6) != iProver_top
% 2.76/0.98      | v1_xboole_0(sK6) != iProver_top ),
% 2.76/0.98      inference(instantiation,[status(thm)],[c_3982]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3237,plain,
% 2.76/0.99      ( ~ r2_hidden(sK1(X0,sK6),X0) | ~ v1_xboole_0(X0) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3238,plain,
% 2.76/0.99      ( r2_hidden(sK1(X0,sK6),X0) != iProver_top
% 2.76/0.99      | v1_xboole_0(X0) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_3237]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3240,plain,
% 2.76/0.99      ( r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) != iProver_top
% 2.76/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_3238]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3,plain,
% 2.76/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.76/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2885,plain,
% 2.76/0.99      ( r1_tarski(sK5,X0) | r2_hidden(sK1(sK5,X0),sK5) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2897,plain,
% 2.76/0.99      ( r1_tarski(sK5,k1_xboole_0)
% 2.76/0.99      | r2_hidden(sK1(sK5,k1_xboole_0),sK5) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_2885]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2865,plain,
% 2.76/0.99      ( r1_tarski(sK6,X0) | r2_hidden(sK1(sK6,X0),sK6) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2876,plain,
% 2.76/0.99      ( r1_tarski(sK6,X0) = iProver_top
% 2.76/0.99      | r2_hidden(sK1(sK6,X0),sK6) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2865]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2878,plain,
% 2.76/0.99      ( r1_tarski(sK6,k1_xboole_0) = iProver_top
% 2.76/0.99      | r2_hidden(sK1(sK6,k1_xboole_0),sK6) = iProver_top ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_2876]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2686,plain,
% 2.76/0.99      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2688,plain,
% 2.76/0.99      ( ~ r1_tarski(sK5,k1_xboole_0)
% 2.76/0.99      | ~ r1_tarski(k1_xboole_0,sK5)
% 2.76/0.99      | sK5 = k1_xboole_0 ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_2686]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2651,plain,
% 2.76/0.99      ( r1_tarski(X0,sK5) | r2_hidden(sK1(X0,sK5),X0) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2663,plain,
% 2.76/0.99      ( r1_tarski(k1_xboole_0,sK5)
% 2.76/0.99      | r2_hidden(sK1(k1_xboole_0,sK5),k1_xboole_0) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_2651]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2630,plain,
% 2.76/0.99      ( r1_tarski(X0,sK6) | r2_hidden(sK1(X0,sK6),X0) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2641,plain,
% 2.76/0.99      ( r1_tarski(X0,sK6) = iProver_top
% 2.76/0.99      | r2_hidden(sK1(X0,sK6),X0) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2630]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2643,plain,
% 2.76/0.99      ( r1_tarski(k1_xboole_0,sK6) = iProver_top
% 2.76/0.99      | r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) = iProver_top ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_2641]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2591,plain,
% 2.76/0.99      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2592,plain,
% 2.76/0.99      ( sK6 = X0
% 2.76/0.99      | r1_tarski(X0,sK6) != iProver_top
% 2.76/0.99      | r1_tarski(sK6,X0) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2591]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2594,plain,
% 2.76/0.99      ( sK6 = k1_xboole_0
% 2.76/0.99      | r1_tarski(sK6,k1_xboole_0) != iProver_top
% 2.76/0.99      | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_2592]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2393,plain,
% 2.76/0.99      ( sK6 != k1_xboole_0 | sK5 = sK6 | sK5 != k1_xboole_0 ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_2392]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_5,plain,
% 2.76/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.76/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_92,plain,
% 2.76/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(contradiction,plain,
% 2.76/0.99      ( $false ),
% 2.76/0.99      inference(minisat,
% 2.76/0.99                [status(thm)],
% 2.76/0.99                [c_4908,c_4671,c_4761,c_4220,c_3984,c_3240,c_2897,c_2878,
% 2.76/0.99                 c_2688,c_2663,c_2643,c_2594,c_2393,c_411,c_92,c_5,c_26]) ).
% 2.76/0.99  
% 2.76/0.99  
% 2.76/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.76/0.99  
% 2.76/0.99  ------                               Statistics
% 2.76/0.99  
% 2.76/0.99  ------ General
% 2.76/0.99  
% 2.76/0.99  abstr_ref_over_cycles:                  0
% 2.76/0.99  abstr_ref_under_cycles:                 0
% 2.76/0.99  gc_basic_clause_elim:                   0
% 2.76/0.99  forced_gc_time:                         0
% 2.76/0.99  parsing_time:                           0.008
% 2.76/0.99  unif_index_cands_time:                  0.
% 2.76/0.99  unif_index_add_time:                    0.
% 2.76/0.99  orderings_time:                         0.
% 2.76/0.99  out_proof_time:                         0.009
% 2.76/0.99  total_time:                             0.147
% 2.76/0.99  num_of_symbols:                         52
% 2.76/0.99  num_of_terms:                           3347
% 2.76/0.99  
% 2.76/0.99  ------ Preprocessing
% 2.76/0.99  
% 2.76/0.99  num_of_splits:                          0
% 2.76/0.99  num_of_split_atoms:                     0
% 2.76/0.99  num_of_reused_defs:                     0
% 2.76/0.99  num_eq_ax_congr_red:                    29
% 2.76/0.99  num_of_sem_filtered_clauses:            1
% 2.76/0.99  num_of_subtypes:                        0
% 2.76/0.99  monotx_restored_types:                  0
% 2.76/0.99  sat_num_of_epr_types:                   0
% 2.76/0.99  sat_num_of_non_cyclic_types:            0
% 2.76/0.99  sat_guarded_non_collapsed_types:        0
% 2.76/0.99  num_pure_diseq_elim:                    0
% 2.76/0.99  simp_replaced_by:                       0
% 2.76/0.99  res_preprocessed:                       133
% 2.76/0.99  prep_upred:                             0
% 2.76/0.99  prep_unflattend:                        71
% 2.76/0.99  smt_new_axioms:                         0
% 2.76/0.99  pred_elim_cands:                        6
% 2.76/0.99  pred_elim:                              2
% 2.76/0.99  pred_elim_cl:                           4
% 2.76/0.99  pred_elim_cycles:                       4
% 2.76/0.99  merged_defs:                            8
% 2.76/0.99  merged_defs_ncl:                        0
% 2.76/0.99  bin_hyper_res:                          8
% 2.76/0.99  prep_cycles:                            4
% 2.76/0.99  pred_elim_time:                         0.017
% 2.76/0.99  splitting_time:                         0.
% 2.76/0.99  sem_filter_time:                        0.
% 2.76/0.99  monotx_time:                            0.001
% 2.76/0.99  subtype_inf_time:                       0.
% 2.76/0.99  
% 2.76/0.99  ------ Problem properties
% 2.76/0.99  
% 2.76/0.99  clauses:                                27
% 2.76/0.99  conjectures:                            5
% 2.76/0.99  epr:                                    8
% 2.76/0.99  horn:                                   20
% 2.76/0.99  ground:                                 12
% 2.76/0.99  unary:                                  7
% 2.76/0.99  binary:                                 11
% 2.76/0.99  lits:                                   66
% 2.76/0.99  lits_eq:                                23
% 2.76/0.99  fd_pure:                                0
% 2.76/0.99  fd_pseudo:                              0
% 2.76/0.99  fd_cond:                                0
% 2.76/0.99  fd_pseudo_cond:                         3
% 2.76/0.99  ac_symbols:                             0
% 2.76/0.99  
% 2.76/0.99  ------ Propositional Solver
% 2.76/0.99  
% 2.76/0.99  prop_solver_calls:                      28
% 2.76/0.99  prop_fast_solver_calls:                 1018
% 2.76/0.99  smt_solver_calls:                       0
% 2.76/0.99  smt_fast_solver_calls:                  0
% 2.76/0.99  prop_num_of_clauses:                    1296
% 2.76/0.99  prop_preprocess_simplified:             4837
% 2.76/0.99  prop_fo_subsumed:                       14
% 2.76/0.99  prop_solver_time:                       0.
% 2.76/0.99  smt_solver_time:                        0.
% 2.76/0.99  smt_fast_solver_time:                   0.
% 2.76/0.99  prop_fast_solver_time:                  0.
% 2.76/0.99  prop_unsat_core_time:                   0.
% 2.76/0.99  
% 2.76/0.99  ------ QBF
% 2.76/0.99  
% 2.76/0.99  qbf_q_res:                              0
% 2.76/0.99  qbf_num_tautologies:                    0
% 2.76/0.99  qbf_prep_cycles:                        0
% 2.76/0.99  
% 2.76/0.99  ------ BMC1
% 2.76/0.99  
% 2.76/0.99  bmc1_current_bound:                     -1
% 2.76/0.99  bmc1_last_solved_bound:                 -1
% 2.76/0.99  bmc1_unsat_core_size:                   -1
% 2.76/0.99  bmc1_unsat_core_parents_size:           -1
% 2.76/0.99  bmc1_merge_next_fun:                    0
% 2.76/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.76/0.99  
% 2.76/0.99  ------ Instantiation
% 2.76/0.99  
% 2.76/0.99  inst_num_of_clauses:                    358
% 2.76/0.99  inst_num_in_passive:                    98
% 2.76/0.99  inst_num_in_active:                     232
% 2.76/0.99  inst_num_in_unprocessed:                27
% 2.76/0.99  inst_num_of_loops:                      318
% 2.76/0.99  inst_num_of_learning_restarts:          0
% 2.76/0.99  inst_num_moves_active_passive:          82
% 2.76/0.99  inst_lit_activity:                      0
% 2.76/0.99  inst_lit_activity_moves:                0
% 2.76/0.99  inst_num_tautologies:                   0
% 2.76/0.99  inst_num_prop_implied:                  0
% 2.76/0.99  inst_num_existing_simplified:           0
% 2.76/0.99  inst_num_eq_res_simplified:             0
% 2.76/0.99  inst_num_child_elim:                    0
% 2.76/0.99  inst_num_of_dismatching_blockings:      125
% 2.76/0.99  inst_num_of_non_proper_insts:           404
% 2.76/0.99  inst_num_of_duplicates:                 0
% 2.76/0.99  inst_inst_num_from_inst_to_res:         0
% 2.76/0.99  inst_dismatching_checking_time:         0.
% 2.76/0.99  
% 2.76/0.99  ------ Resolution
% 2.76/0.99  
% 2.76/0.99  res_num_of_clauses:                     0
% 2.76/0.99  res_num_in_passive:                     0
% 2.76/0.99  res_num_in_active:                      0
% 2.76/0.99  res_num_of_loops:                       137
% 2.76/0.99  res_forward_subset_subsumed:            37
% 2.76/0.99  res_backward_subset_subsumed:           0
% 2.76/0.99  res_forward_subsumed:                   0
% 2.76/0.99  res_backward_subsumed:                  0
% 2.76/0.99  res_forward_subsumption_resolution:     0
% 2.76/0.99  res_backward_subsumption_resolution:    0
% 2.76/0.99  res_clause_to_clause_subsumption:       247
% 2.76/0.99  res_orphan_elimination:                 0
% 2.76/0.99  res_tautology_del:                      60
% 2.76/0.99  res_num_eq_res_simplified:              0
% 2.76/0.99  res_num_sel_changes:                    0
% 2.76/0.99  res_moves_from_active_to_pass:          0
% 2.76/0.99  
% 2.76/0.99  ------ Superposition
% 2.76/0.99  
% 2.76/0.99  sup_time_total:                         0.
% 2.76/0.99  sup_time_generating:                    0.
% 2.76/0.99  sup_time_sim_full:                      0.
% 2.76/0.99  sup_time_sim_immed:                     0.
% 2.76/0.99  
% 2.76/0.99  sup_num_of_clauses:                     73
% 2.76/0.99  sup_num_in_active:                      39
% 2.76/0.99  sup_num_in_passive:                     34
% 2.76/0.99  sup_num_of_loops:                       62
% 2.76/0.99  sup_fw_superposition:                   52
% 2.76/0.99  sup_bw_superposition:                   24
% 2.76/0.99  sup_immediate_simplified:               3
% 2.76/0.99  sup_given_eliminated:                   0
% 2.76/0.99  comparisons_done:                       0
% 2.76/0.99  comparisons_avoided:                    14
% 2.76/0.99  
% 2.76/0.99  ------ Simplifications
% 2.76/0.99  
% 2.76/0.99  
% 2.76/0.99  sim_fw_subset_subsumed:                 0
% 2.76/0.99  sim_bw_subset_subsumed:                 4
% 2.76/0.99  sim_fw_subsumed:                        1
% 2.76/0.99  sim_bw_subsumed:                        0
% 2.76/0.99  sim_fw_subsumption_res:                 2
% 2.76/0.99  sim_bw_subsumption_res:                 0
% 2.76/0.99  sim_tautology_del:                      4
% 2.76/0.99  sim_eq_tautology_del:                   8
% 2.76/0.99  sim_eq_res_simp:                        2
% 2.76/0.99  sim_fw_demodulated:                     0
% 2.76/0.99  sim_bw_demodulated:                     21
% 2.76/0.99  sim_light_normalised:                   0
% 2.76/0.99  sim_joinable_taut:                      0
% 2.76/0.99  sim_joinable_simp:                      0
% 2.76/0.99  sim_ac_normalised:                      0
% 2.76/0.99  sim_smt_subsumption:                    0
% 2.76/0.99  
%------------------------------------------------------------------------------

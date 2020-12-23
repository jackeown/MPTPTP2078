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
% DateTime   : Thu Dec  3 12:04:12 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 580 expanded)
%              Number of clauses        :   69 ( 174 expanded)
%              Number of leaves         :   12 ( 156 expanded)
%              Depth                    :   22
%              Number of atoms          :  399 (3251 expanded)
%              Number of equality atoms :  159 ( 802 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) )
           => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
             => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f28,plain,(
    ! [X4,X2,X0,X3] :
      ( ? [X5] :
          ( k1_funct_1(X3,X5) = X4
          & r2_hidden(X5,X2)
          & r2_hidden(X5,X0) )
     => ( k1_funct_1(X3,sK6) = X4
        & r2_hidden(sK6,X2)
        & r2_hidden(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
     => ( ~ r2_hidden(sK5,k7_relset_1(X0,X1,X3,X2))
        & ? [X5] :
            ( k1_funct_1(X3,X5) = sK5
            & r2_hidden(X5,X2)
            & r2_hidden(X5,X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
            & ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) ) )
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(sK1,sK2,sK4,sK3))
          & ? [X5] :
              ( k1_funct_1(sK4,X5) = X4
              & r2_hidden(X5,sK3)
              & r2_hidden(X5,sK1) ) )
      & k1_xboole_0 != sK2
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))
    & k1_funct_1(sK4,sK6) = sK5
    & r2_hidden(sK6,sK3)
    & r2_hidden(sK6,sK1)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f18,f28,f27,f26])).

fof(f52,plain,(
    k1_funct_1(sK4,sK6) = sK5 ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f36])).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    r2_hidden(sK6,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ~ r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    r2_hidden(sK6,sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_17,negated_conjecture,
    ( k1_funct_1(sK4,sK6) = sK5 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_359,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_360,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_263,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_485,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_360,c_264])).

cnf(c_754,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
    | ~ sP6_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP6_iProver_split])],[c_485])).

cnf(c_1114,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
    | sP6_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_755,plain,
    ( sP6_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_485])).

cnf(c_810,plain,
    ( sP6_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_811,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
    | sP6_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_759,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1275,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_558,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_360])).

cnf(c_559,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK4,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X0,X2),sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_248,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_249,plain,
    ( r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_499,plain,
    ( r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_360,c_249])).

cnf(c_568,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK4,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_559,c_499])).

cnf(c_743,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_568])).

cnf(c_1276,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_1280,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1276])).

cnf(c_1571,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1114,c_810,c_811,c_1275,c_1280])).

cnf(c_1572,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_1571])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_305,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_306,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_617,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != sK4
    | sK2 != X1
    | sK1 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_306])).

cnf(c_618,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_619,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_20])).

cnf(c_620,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_619])).

cnf(c_679,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_620])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_350,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_351,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_1294,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_351])).

cnf(c_1481,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(demodulation,[status(thm)],[c_679,c_1294])).

cnf(c_1577,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1572,c_1481])).

cnf(c_1583,plain,
    ( r2_hidden(k4_tarski(sK6,sK5),sK4) = iProver_top
    | r2_hidden(sK6,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_1577])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK6,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_27,plain,
    ( r2_hidden(sK6,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1637,plain,
    ( r2_hidden(k4_tarski(sK6,sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1583,c_27])).

cnf(c_744,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK4,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK4)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_568])).

cnf(c_1099,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(sK4,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),sK4) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_745,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_568])).

cnf(c_783,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_784,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(sK4,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),sK4) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_1645,plain,
    ( r2_hidden(k4_tarski(X0,X2),sK4) != iProver_top
    | r2_hidden(X2,k9_relat_1(sK4,X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1099,c_783,c_784,c_1275,c_1280])).

cnf(c_1646,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(sK4,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_1645])).

cnf(c_1655,plain,
    ( r2_hidden(sK6,X0) != iProver_top
    | r2_hidden(sK5,k9_relat_1(sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1637,c_1646])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_341,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_342,plain,
    ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_1317,plain,
    ( k7_relset_1(sK1,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_342])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1121,plain,
    ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1349,plain,
    ( r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1317,c_1121])).

cnf(c_1708,plain,
    ( r2_hidden(sK6,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1349])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK6,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_28,plain,
    ( r2_hidden(sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1708,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:36:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.56/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.00  
% 1.56/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.56/1.00  
% 1.56/1.00  ------  iProver source info
% 1.56/1.00  
% 1.56/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.56/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.56/1.00  git: non_committed_changes: false
% 1.56/1.00  git: last_make_outside_of_git: false
% 1.56/1.00  
% 1.56/1.00  ------ 
% 1.56/1.00  
% 1.56/1.00  ------ Input Options
% 1.56/1.00  
% 1.56/1.00  --out_options                           all
% 1.56/1.00  --tptp_safe_out                         true
% 1.56/1.00  --problem_path                          ""
% 1.56/1.00  --include_path                          ""
% 1.56/1.00  --clausifier                            res/vclausify_rel
% 1.56/1.00  --clausifier_options                    --mode clausify
% 1.56/1.00  --stdin                                 false
% 1.56/1.00  --stats_out                             all
% 1.56/1.00  
% 1.56/1.00  ------ General Options
% 1.56/1.00  
% 1.56/1.00  --fof                                   false
% 1.56/1.00  --time_out_real                         305.
% 1.56/1.00  --time_out_virtual                      -1.
% 1.56/1.00  --symbol_type_check                     false
% 1.56/1.00  --clausify_out                          false
% 1.56/1.00  --sig_cnt_out                           false
% 1.56/1.00  --trig_cnt_out                          false
% 1.56/1.00  --trig_cnt_out_tolerance                1.
% 1.56/1.00  --trig_cnt_out_sk_spl                   false
% 1.56/1.00  --abstr_cl_out                          false
% 1.56/1.00  
% 1.56/1.00  ------ Global Options
% 1.56/1.00  
% 1.56/1.00  --schedule                              default
% 1.56/1.00  --add_important_lit                     false
% 1.56/1.00  --prop_solver_per_cl                    1000
% 1.56/1.00  --min_unsat_core                        false
% 1.56/1.00  --soft_assumptions                      false
% 1.56/1.00  --soft_lemma_size                       3
% 1.56/1.00  --prop_impl_unit_size                   0
% 1.56/1.00  --prop_impl_unit                        []
% 1.56/1.00  --share_sel_clauses                     true
% 1.56/1.00  --reset_solvers                         false
% 1.56/1.00  --bc_imp_inh                            [conj_cone]
% 1.56/1.00  --conj_cone_tolerance                   3.
% 1.56/1.00  --extra_neg_conj                        none
% 1.56/1.00  --large_theory_mode                     true
% 1.56/1.00  --prolific_symb_bound                   200
% 1.56/1.00  --lt_threshold                          2000
% 1.56/1.00  --clause_weak_htbl                      true
% 1.56/1.00  --gc_record_bc_elim                     false
% 1.56/1.00  
% 1.56/1.00  ------ Preprocessing Options
% 1.56/1.00  
% 1.56/1.00  --preprocessing_flag                    true
% 1.56/1.00  --time_out_prep_mult                    0.1
% 1.56/1.00  --splitting_mode                        input
% 1.56/1.00  --splitting_grd                         true
% 1.56/1.00  --splitting_cvd                         false
% 1.56/1.00  --splitting_cvd_svl                     false
% 1.56/1.00  --splitting_nvd                         32
% 1.56/1.00  --sub_typing                            true
% 1.56/1.00  --prep_gs_sim                           true
% 1.56/1.00  --prep_unflatten                        true
% 1.56/1.00  --prep_res_sim                          true
% 1.56/1.00  --prep_upred                            true
% 1.56/1.00  --prep_sem_filter                       exhaustive
% 1.56/1.00  --prep_sem_filter_out                   false
% 1.56/1.00  --pred_elim                             true
% 1.56/1.00  --res_sim_input                         true
% 1.56/1.00  --eq_ax_congr_red                       true
% 1.56/1.00  --pure_diseq_elim                       true
% 1.56/1.00  --brand_transform                       false
% 1.56/1.00  --non_eq_to_eq                          false
% 1.56/1.00  --prep_def_merge                        true
% 1.56/1.00  --prep_def_merge_prop_impl              false
% 1.56/1.00  --prep_def_merge_mbd                    true
% 1.56/1.00  --prep_def_merge_tr_red                 false
% 1.56/1.00  --prep_def_merge_tr_cl                  false
% 1.56/1.00  --smt_preprocessing                     true
% 1.56/1.00  --smt_ac_axioms                         fast
% 1.56/1.00  --preprocessed_out                      false
% 1.56/1.00  --preprocessed_stats                    false
% 1.56/1.00  
% 1.56/1.00  ------ Abstraction refinement Options
% 1.56/1.00  
% 1.56/1.00  --abstr_ref                             []
% 1.56/1.00  --abstr_ref_prep                        false
% 1.56/1.00  --abstr_ref_until_sat                   false
% 1.56/1.00  --abstr_ref_sig_restrict                funpre
% 1.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.56/1.00  --abstr_ref_under                       []
% 1.56/1.00  
% 1.56/1.00  ------ SAT Options
% 1.56/1.00  
% 1.56/1.00  --sat_mode                              false
% 1.56/1.00  --sat_fm_restart_options                ""
% 1.56/1.00  --sat_gr_def                            false
% 1.56/1.00  --sat_epr_types                         true
% 1.56/1.00  --sat_non_cyclic_types                  false
% 1.56/1.00  --sat_finite_models                     false
% 1.56/1.00  --sat_fm_lemmas                         false
% 1.56/1.00  --sat_fm_prep                           false
% 1.56/1.00  --sat_fm_uc_incr                        true
% 1.56/1.00  --sat_out_model                         small
% 1.56/1.00  --sat_out_clauses                       false
% 1.56/1.00  
% 1.56/1.00  ------ QBF Options
% 1.56/1.00  
% 1.56/1.00  --qbf_mode                              false
% 1.56/1.00  --qbf_elim_univ                         false
% 1.56/1.00  --qbf_dom_inst                          none
% 1.56/1.00  --qbf_dom_pre_inst                      false
% 1.56/1.00  --qbf_sk_in                             false
% 1.56/1.00  --qbf_pred_elim                         true
% 1.56/1.00  --qbf_split                             512
% 1.56/1.00  
% 1.56/1.00  ------ BMC1 Options
% 1.56/1.00  
% 1.56/1.00  --bmc1_incremental                      false
% 1.56/1.00  --bmc1_axioms                           reachable_all
% 1.56/1.00  --bmc1_min_bound                        0
% 1.56/1.00  --bmc1_max_bound                        -1
% 1.56/1.00  --bmc1_max_bound_default                -1
% 1.56/1.00  --bmc1_symbol_reachability              true
% 1.56/1.00  --bmc1_property_lemmas                  false
% 1.56/1.00  --bmc1_k_induction                      false
% 1.56/1.00  --bmc1_non_equiv_states                 false
% 1.56/1.00  --bmc1_deadlock                         false
% 1.56/1.00  --bmc1_ucm                              false
% 1.56/1.00  --bmc1_add_unsat_core                   none
% 1.56/1.00  --bmc1_unsat_core_children              false
% 1.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.56/1.00  --bmc1_out_stat                         full
% 1.56/1.00  --bmc1_ground_init                      false
% 1.56/1.00  --bmc1_pre_inst_next_state              false
% 1.56/1.00  --bmc1_pre_inst_state                   false
% 1.56/1.00  --bmc1_pre_inst_reach_state             false
% 1.56/1.00  --bmc1_out_unsat_core                   false
% 1.56/1.00  --bmc1_aig_witness_out                  false
% 1.56/1.00  --bmc1_verbose                          false
% 1.56/1.00  --bmc1_dump_clauses_tptp                false
% 1.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.56/1.00  --bmc1_dump_file                        -
% 1.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.56/1.00  --bmc1_ucm_extend_mode                  1
% 1.56/1.00  --bmc1_ucm_init_mode                    2
% 1.56/1.00  --bmc1_ucm_cone_mode                    none
% 1.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.56/1.00  --bmc1_ucm_relax_model                  4
% 1.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.56/1.00  --bmc1_ucm_layered_model                none
% 1.56/1.00  --bmc1_ucm_max_lemma_size               10
% 1.56/1.00  
% 1.56/1.00  ------ AIG Options
% 1.56/1.00  
% 1.56/1.00  --aig_mode                              false
% 1.56/1.00  
% 1.56/1.00  ------ Instantiation Options
% 1.56/1.00  
% 1.56/1.00  --instantiation_flag                    true
% 1.56/1.00  --inst_sos_flag                         false
% 1.56/1.00  --inst_sos_phase                        true
% 1.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.56/1.00  --inst_lit_sel_side                     num_symb
% 1.56/1.00  --inst_solver_per_active                1400
% 1.56/1.00  --inst_solver_calls_frac                1.
% 1.56/1.00  --inst_passive_queue_type               priority_queues
% 1.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.56/1.00  --inst_passive_queues_freq              [25;2]
% 1.56/1.00  --inst_dismatching                      true
% 1.56/1.00  --inst_eager_unprocessed_to_passive     true
% 1.56/1.00  --inst_prop_sim_given                   true
% 1.56/1.00  --inst_prop_sim_new                     false
% 1.56/1.00  --inst_subs_new                         false
% 1.56/1.00  --inst_eq_res_simp                      false
% 1.56/1.00  --inst_subs_given                       false
% 1.56/1.00  --inst_orphan_elimination               true
% 1.56/1.00  --inst_learning_loop_flag               true
% 1.56/1.00  --inst_learning_start                   3000
% 1.56/1.00  --inst_learning_factor                  2
% 1.56/1.00  --inst_start_prop_sim_after_learn       3
% 1.56/1.00  --inst_sel_renew                        solver
% 1.56/1.00  --inst_lit_activity_flag                true
% 1.56/1.00  --inst_restr_to_given                   false
% 1.56/1.00  --inst_activity_threshold               500
% 1.56/1.00  --inst_out_proof                        true
% 1.56/1.00  
% 1.56/1.00  ------ Resolution Options
% 1.56/1.00  
% 1.56/1.00  --resolution_flag                       true
% 1.56/1.00  --res_lit_sel                           adaptive
% 1.56/1.00  --res_lit_sel_side                      none
% 1.56/1.00  --res_ordering                          kbo
% 1.56/1.00  --res_to_prop_solver                    active
% 1.56/1.00  --res_prop_simpl_new                    false
% 1.56/1.00  --res_prop_simpl_given                  true
% 1.56/1.00  --res_passive_queue_type                priority_queues
% 1.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.56/1.00  --res_passive_queues_freq               [15;5]
% 1.56/1.00  --res_forward_subs                      full
% 1.56/1.00  --res_backward_subs                     full
% 1.56/1.00  --res_forward_subs_resolution           true
% 1.56/1.00  --res_backward_subs_resolution          true
% 1.56/1.00  --res_orphan_elimination                true
% 1.56/1.00  --res_time_limit                        2.
% 1.56/1.00  --res_out_proof                         true
% 1.56/1.00  
% 1.56/1.00  ------ Superposition Options
% 1.56/1.00  
% 1.56/1.00  --superposition_flag                    true
% 1.56/1.00  --sup_passive_queue_type                priority_queues
% 1.56/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.56/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.56/1.00  --demod_completeness_check              fast
% 1.56/1.00  --demod_use_ground                      true
% 1.56/1.00  --sup_to_prop_solver                    passive
% 1.56/1.00  --sup_prop_simpl_new                    true
% 1.56/1.00  --sup_prop_simpl_given                  true
% 1.56/1.00  --sup_fun_splitting                     false
% 1.56/1.00  --sup_smt_interval                      50000
% 1.56/1.00  
% 1.56/1.00  ------ Superposition Simplification Setup
% 1.56/1.00  
% 1.56/1.00  --sup_indices_passive                   []
% 1.56/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/1.00  --sup_full_bw                           [BwDemod]
% 1.56/1.00  --sup_immed_triv                        [TrivRules]
% 1.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/1.00  --sup_immed_bw_main                     []
% 1.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/1.00  
% 1.56/1.00  ------ Combination Options
% 1.56/1.00  
% 1.56/1.00  --comb_res_mult                         3
% 1.56/1.00  --comb_sup_mult                         2
% 1.56/1.00  --comb_inst_mult                        10
% 1.56/1.00  
% 1.56/1.00  ------ Debug Options
% 1.56/1.00  
% 1.56/1.00  --dbg_backtrace                         false
% 1.56/1.00  --dbg_dump_prop_clauses                 false
% 1.56/1.00  --dbg_dump_prop_clauses_file            -
% 1.56/1.00  --dbg_out_stat                          false
% 1.56/1.00  ------ Parsing...
% 1.56/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.56/1.00  
% 1.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.56/1.00  
% 1.56/1.00  ------ Preprocessing... gs_s  sp: 14 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.56/1.00  
% 1.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.56/1.00  ------ Proving...
% 1.56/1.00  ------ Problem Properties 
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  clauses                                 31
% 1.56/1.00  conjectures                             5
% 1.56/1.00  EPR                                     10
% 1.56/1.00  Horn                                    23
% 1.56/1.00  unary                                   6
% 1.56/1.00  binary                                  16
% 1.56/1.00  lits                                    67
% 1.56/1.00  lits eq                                 22
% 1.56/1.00  fd_pure                                 0
% 1.56/1.00  fd_pseudo                               0
% 1.56/1.00  fd_cond                                 0
% 1.56/1.00  fd_pseudo_cond                          1
% 1.56/1.00  AC symbols                              0
% 1.56/1.00  
% 1.56/1.00  ------ Schedule dynamic 5 is on 
% 1.56/1.00  
% 1.56/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  ------ 
% 1.56/1.00  Current options:
% 1.56/1.00  ------ 
% 1.56/1.00  
% 1.56/1.00  ------ Input Options
% 1.56/1.00  
% 1.56/1.00  --out_options                           all
% 1.56/1.00  --tptp_safe_out                         true
% 1.56/1.00  --problem_path                          ""
% 1.56/1.00  --include_path                          ""
% 1.56/1.00  --clausifier                            res/vclausify_rel
% 1.56/1.00  --clausifier_options                    --mode clausify
% 1.56/1.00  --stdin                                 false
% 1.56/1.00  --stats_out                             all
% 1.56/1.00  
% 1.56/1.00  ------ General Options
% 1.56/1.00  
% 1.56/1.00  --fof                                   false
% 1.56/1.00  --time_out_real                         305.
% 1.56/1.00  --time_out_virtual                      -1.
% 1.56/1.00  --symbol_type_check                     false
% 1.56/1.00  --clausify_out                          false
% 1.56/1.00  --sig_cnt_out                           false
% 1.56/1.00  --trig_cnt_out                          false
% 1.56/1.00  --trig_cnt_out_tolerance                1.
% 1.56/1.00  --trig_cnt_out_sk_spl                   false
% 1.56/1.00  --abstr_cl_out                          false
% 1.56/1.00  
% 1.56/1.00  ------ Global Options
% 1.56/1.00  
% 1.56/1.00  --schedule                              default
% 1.56/1.00  --add_important_lit                     false
% 1.56/1.00  --prop_solver_per_cl                    1000
% 1.56/1.00  --min_unsat_core                        false
% 1.56/1.00  --soft_assumptions                      false
% 1.56/1.00  --soft_lemma_size                       3
% 1.56/1.00  --prop_impl_unit_size                   0
% 1.56/1.00  --prop_impl_unit                        []
% 1.56/1.00  --share_sel_clauses                     true
% 1.56/1.00  --reset_solvers                         false
% 1.56/1.00  --bc_imp_inh                            [conj_cone]
% 1.56/1.00  --conj_cone_tolerance                   3.
% 1.56/1.00  --extra_neg_conj                        none
% 1.56/1.00  --large_theory_mode                     true
% 1.56/1.00  --prolific_symb_bound                   200
% 1.56/1.00  --lt_threshold                          2000
% 1.56/1.00  --clause_weak_htbl                      true
% 1.56/1.00  --gc_record_bc_elim                     false
% 1.56/1.00  
% 1.56/1.00  ------ Preprocessing Options
% 1.56/1.00  
% 1.56/1.00  --preprocessing_flag                    true
% 1.56/1.00  --time_out_prep_mult                    0.1
% 1.56/1.00  --splitting_mode                        input
% 1.56/1.00  --splitting_grd                         true
% 1.56/1.00  --splitting_cvd                         false
% 1.56/1.00  --splitting_cvd_svl                     false
% 1.56/1.00  --splitting_nvd                         32
% 1.56/1.00  --sub_typing                            true
% 1.56/1.00  --prep_gs_sim                           true
% 1.56/1.00  --prep_unflatten                        true
% 1.56/1.00  --prep_res_sim                          true
% 1.56/1.00  --prep_upred                            true
% 1.56/1.00  --prep_sem_filter                       exhaustive
% 1.56/1.00  --prep_sem_filter_out                   false
% 1.56/1.00  --pred_elim                             true
% 1.56/1.00  --res_sim_input                         true
% 1.56/1.00  --eq_ax_congr_red                       true
% 1.56/1.00  --pure_diseq_elim                       true
% 1.56/1.00  --brand_transform                       false
% 1.56/1.00  --non_eq_to_eq                          false
% 1.56/1.00  --prep_def_merge                        true
% 1.56/1.00  --prep_def_merge_prop_impl              false
% 1.56/1.00  --prep_def_merge_mbd                    true
% 1.56/1.00  --prep_def_merge_tr_red                 false
% 1.56/1.00  --prep_def_merge_tr_cl                  false
% 1.56/1.00  --smt_preprocessing                     true
% 1.56/1.00  --smt_ac_axioms                         fast
% 1.56/1.00  --preprocessed_out                      false
% 1.56/1.00  --preprocessed_stats                    false
% 1.56/1.00  
% 1.56/1.00  ------ Abstraction refinement Options
% 1.56/1.00  
% 1.56/1.00  --abstr_ref                             []
% 1.56/1.00  --abstr_ref_prep                        false
% 1.56/1.00  --abstr_ref_until_sat                   false
% 1.56/1.00  --abstr_ref_sig_restrict                funpre
% 1.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.56/1.00  --abstr_ref_under                       []
% 1.56/1.00  
% 1.56/1.00  ------ SAT Options
% 1.56/1.00  
% 1.56/1.00  --sat_mode                              false
% 1.56/1.00  --sat_fm_restart_options                ""
% 1.56/1.00  --sat_gr_def                            false
% 1.56/1.00  --sat_epr_types                         true
% 1.56/1.00  --sat_non_cyclic_types                  false
% 1.56/1.00  --sat_finite_models                     false
% 1.56/1.00  --sat_fm_lemmas                         false
% 1.56/1.00  --sat_fm_prep                           false
% 1.56/1.00  --sat_fm_uc_incr                        true
% 1.56/1.00  --sat_out_model                         small
% 1.56/1.00  --sat_out_clauses                       false
% 1.56/1.00  
% 1.56/1.00  ------ QBF Options
% 1.56/1.00  
% 1.56/1.00  --qbf_mode                              false
% 1.56/1.00  --qbf_elim_univ                         false
% 1.56/1.00  --qbf_dom_inst                          none
% 1.56/1.00  --qbf_dom_pre_inst                      false
% 1.56/1.00  --qbf_sk_in                             false
% 1.56/1.00  --qbf_pred_elim                         true
% 1.56/1.00  --qbf_split                             512
% 1.56/1.00  
% 1.56/1.00  ------ BMC1 Options
% 1.56/1.00  
% 1.56/1.00  --bmc1_incremental                      false
% 1.56/1.00  --bmc1_axioms                           reachable_all
% 1.56/1.00  --bmc1_min_bound                        0
% 1.56/1.00  --bmc1_max_bound                        -1
% 1.56/1.00  --bmc1_max_bound_default                -1
% 1.56/1.00  --bmc1_symbol_reachability              true
% 1.56/1.00  --bmc1_property_lemmas                  false
% 1.56/1.00  --bmc1_k_induction                      false
% 1.56/1.00  --bmc1_non_equiv_states                 false
% 1.56/1.00  --bmc1_deadlock                         false
% 1.56/1.00  --bmc1_ucm                              false
% 1.56/1.00  --bmc1_add_unsat_core                   none
% 1.56/1.00  --bmc1_unsat_core_children              false
% 1.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.56/1.00  --bmc1_out_stat                         full
% 1.56/1.00  --bmc1_ground_init                      false
% 1.56/1.00  --bmc1_pre_inst_next_state              false
% 1.56/1.00  --bmc1_pre_inst_state                   false
% 1.56/1.00  --bmc1_pre_inst_reach_state             false
% 1.56/1.00  --bmc1_out_unsat_core                   false
% 1.56/1.00  --bmc1_aig_witness_out                  false
% 1.56/1.00  --bmc1_verbose                          false
% 1.56/1.00  --bmc1_dump_clauses_tptp                false
% 1.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.56/1.00  --bmc1_dump_file                        -
% 1.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.56/1.00  --bmc1_ucm_extend_mode                  1
% 1.56/1.00  --bmc1_ucm_init_mode                    2
% 1.56/1.00  --bmc1_ucm_cone_mode                    none
% 1.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.56/1.00  --bmc1_ucm_relax_model                  4
% 1.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.56/1.00  --bmc1_ucm_layered_model                none
% 1.56/1.00  --bmc1_ucm_max_lemma_size               10
% 1.56/1.00  
% 1.56/1.00  ------ AIG Options
% 1.56/1.00  
% 1.56/1.00  --aig_mode                              false
% 1.56/1.00  
% 1.56/1.00  ------ Instantiation Options
% 1.56/1.00  
% 1.56/1.00  --instantiation_flag                    true
% 1.56/1.00  --inst_sos_flag                         false
% 1.56/1.00  --inst_sos_phase                        true
% 1.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.56/1.00  --inst_lit_sel_side                     none
% 1.56/1.00  --inst_solver_per_active                1400
% 1.56/1.00  --inst_solver_calls_frac                1.
% 1.56/1.00  --inst_passive_queue_type               priority_queues
% 1.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.56/1.00  --inst_passive_queues_freq              [25;2]
% 1.56/1.00  --inst_dismatching                      true
% 1.56/1.00  --inst_eager_unprocessed_to_passive     true
% 1.56/1.00  --inst_prop_sim_given                   true
% 1.56/1.00  --inst_prop_sim_new                     false
% 1.56/1.00  --inst_subs_new                         false
% 1.56/1.00  --inst_eq_res_simp                      false
% 1.56/1.00  --inst_subs_given                       false
% 1.56/1.00  --inst_orphan_elimination               true
% 1.56/1.00  --inst_learning_loop_flag               true
% 1.56/1.00  --inst_learning_start                   3000
% 1.56/1.00  --inst_learning_factor                  2
% 1.56/1.00  --inst_start_prop_sim_after_learn       3
% 1.56/1.00  --inst_sel_renew                        solver
% 1.56/1.00  --inst_lit_activity_flag                true
% 1.56/1.00  --inst_restr_to_given                   false
% 1.56/1.00  --inst_activity_threshold               500
% 1.56/1.00  --inst_out_proof                        true
% 1.56/1.00  
% 1.56/1.00  ------ Resolution Options
% 1.56/1.00  
% 1.56/1.00  --resolution_flag                       false
% 1.56/1.00  --res_lit_sel                           adaptive
% 1.56/1.00  --res_lit_sel_side                      none
% 1.56/1.00  --res_ordering                          kbo
% 1.56/1.00  --res_to_prop_solver                    active
% 1.56/1.00  --res_prop_simpl_new                    false
% 1.56/1.00  --res_prop_simpl_given                  true
% 1.56/1.00  --res_passive_queue_type                priority_queues
% 1.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.56/1.00  --res_passive_queues_freq               [15;5]
% 1.56/1.00  --res_forward_subs                      full
% 1.56/1.00  --res_backward_subs                     full
% 1.56/1.00  --res_forward_subs_resolution           true
% 1.56/1.00  --res_backward_subs_resolution          true
% 1.56/1.00  --res_orphan_elimination                true
% 1.56/1.00  --res_time_limit                        2.
% 1.56/1.00  --res_out_proof                         true
% 1.56/1.00  
% 1.56/1.00  ------ Superposition Options
% 1.56/1.00  
% 1.56/1.00  --superposition_flag                    true
% 1.56/1.00  --sup_passive_queue_type                priority_queues
% 1.56/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.56/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.56/1.00  --demod_completeness_check              fast
% 1.56/1.00  --demod_use_ground                      true
% 1.56/1.00  --sup_to_prop_solver                    passive
% 1.56/1.00  --sup_prop_simpl_new                    true
% 1.56/1.00  --sup_prop_simpl_given                  true
% 1.56/1.00  --sup_fun_splitting                     false
% 1.56/1.00  --sup_smt_interval                      50000
% 1.56/1.00  
% 1.56/1.00  ------ Superposition Simplification Setup
% 1.56/1.00  
% 1.56/1.00  --sup_indices_passive                   []
% 1.56/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/1.00  --sup_full_bw                           [BwDemod]
% 1.56/1.00  --sup_immed_triv                        [TrivRules]
% 1.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/1.00  --sup_immed_bw_main                     []
% 1.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.56/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.56/1.00  
% 1.56/1.00  ------ Combination Options
% 1.56/1.00  
% 1.56/1.00  --comb_res_mult                         3
% 1.56/1.00  --comb_sup_mult                         2
% 1.56/1.00  --comb_inst_mult                        10
% 1.56/1.00  
% 1.56/1.00  ------ Debug Options
% 1.56/1.00  
% 1.56/1.00  --dbg_backtrace                         false
% 1.56/1.00  --dbg_dump_prop_clauses                 false
% 1.56/1.00  --dbg_dump_prop_clauses_file            -
% 1.56/1.00  --dbg_out_stat                          false
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  ------ Proving...
% 1.56/1.00  
% 1.56/1.00  
% 1.56/1.00  % SZS status Theorem for theBenchmark.p
% 1.56/1.00  
% 1.56/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.56/1.00  
% 1.56/1.00  fof(f7,conjecture,(
% 1.56/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f8,negated_conjecture,(
% 1.56/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 1.56/1.00    inference(negated_conjecture,[],[f7])).
% 1.56/1.00  
% 1.56/1.00  fof(f17,plain,(
% 1.56/1.00    ? [X0,X1,X2,X3] : ((? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.56/1.00    inference(ennf_transformation,[],[f8])).
% 1.56/1.00  
% 1.56/1.00  fof(f18,plain,(
% 1.56/1.00    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.56/1.00    inference(flattening,[],[f17])).
% 1.56/1.00  
% 1.56/1.00  fof(f28,plain,(
% 1.56/1.00    ( ! [X4,X2,X0,X3] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => (k1_funct_1(X3,sK6) = X4 & r2_hidden(sK6,X2) & r2_hidden(sK6,X0))) )),
% 1.56/1.00    introduced(choice_axiom,[])).
% 1.56/1.00  
% 1.56/1.00  fof(f27,plain,(
% 1.56/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) => (~r2_hidden(sK5,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = sK5 & r2_hidden(X5,X2) & r2_hidden(X5,X0)))) )),
% 1.56/1.00    introduced(choice_axiom,[])).
% 1.56/1.00  
% 1.56/1.00  fof(f26,plain,(
% 1.56/1.00    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (~r2_hidden(X4,k7_relset_1(sK1,sK2,sK4,sK3)) & ? [X5] : (k1_funct_1(sK4,X5) = X4 & r2_hidden(X5,sK3) & r2_hidden(X5,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.56/1.00    introduced(choice_axiom,[])).
% 1.56/1.00  
% 1.56/1.00  fof(f29,plain,(
% 1.56/1.00    (~r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) & (k1_funct_1(sK4,sK6) = sK5 & r2_hidden(sK6,sK3) & r2_hidden(sK6,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 1.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f18,f28,f27,f26])).
% 1.56/1.00  
% 1.56/1.00  fof(f52,plain,(
% 1.56/1.00    k1_funct_1(sK4,sK6) = sK5),
% 1.56/1.00    inference(cnf_transformation,[],[f29])).
% 1.56/1.00  
% 1.56/1.00  fof(f3,axiom,(
% 1.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f12,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/1.00    inference(ennf_transformation,[],[f3])).
% 1.56/1.00  
% 1.56/1.00  fof(f37,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f12])).
% 1.56/1.00  
% 1.56/1.00  fof(f48,plain,(
% 1.56/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.56/1.00    inference(cnf_transformation,[],[f29])).
% 1.56/1.00  
% 1.56/1.00  fof(f2,axiom,(
% 1.56/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f10,plain,(
% 1.56/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.56/1.00    inference(ennf_transformation,[],[f2])).
% 1.56/1.00  
% 1.56/1.00  fof(f11,plain,(
% 1.56/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.56/1.00    inference(flattening,[],[f10])).
% 1.56/1.00  
% 1.56/1.00  fof(f23,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.56/1.00    inference(nnf_transformation,[],[f11])).
% 1.56/1.00  
% 1.56/1.00  fof(f24,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.56/1.00    inference(flattening,[],[f23])).
% 1.56/1.00  
% 1.56/1.00  fof(f36,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.56/1.00    inference(cnf_transformation,[],[f24])).
% 1.56/1.00  
% 1.56/1.00  fof(f54,plain,(
% 1.56/1.00    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.56/1.00    inference(equality_resolution,[],[f36])).
% 1.56/1.00  
% 1.56/1.00  fof(f46,plain,(
% 1.56/1.00    v1_funct_1(sK4)),
% 1.56/1.00    inference(cnf_transformation,[],[f29])).
% 1.56/1.00  
% 1.56/1.00  fof(f1,axiom,(
% 1.56/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f9,plain,(
% 1.56/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.56/1.00    inference(ennf_transformation,[],[f1])).
% 1.56/1.00  
% 1.56/1.00  fof(f19,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.56/1.00    inference(nnf_transformation,[],[f9])).
% 1.56/1.00  
% 1.56/1.00  fof(f20,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.56/1.00    inference(rectify,[],[f19])).
% 1.56/1.00  
% 1.56/1.00  fof(f21,plain,(
% 1.56/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 1.56/1.00    introduced(choice_axiom,[])).
% 1.56/1.00  
% 1.56/1.00  fof(f22,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 1.56/1.00  
% 1.56/1.00  fof(f33,plain,(
% 1.56/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.56/1.00    inference(cnf_transformation,[],[f22])).
% 1.56/1.00  
% 1.56/1.00  fof(f34,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.56/1.00    inference(cnf_transformation,[],[f24])).
% 1.56/1.00  
% 1.56/1.00  fof(f47,plain,(
% 1.56/1.00    v1_funct_2(sK4,sK1,sK2)),
% 1.56/1.00    inference(cnf_transformation,[],[f29])).
% 1.56/1.00  
% 1.56/1.00  fof(f6,axiom,(
% 1.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f15,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/1.00    inference(ennf_transformation,[],[f6])).
% 1.56/1.00  
% 1.56/1.00  fof(f16,plain,(
% 1.56/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/1.00    inference(flattening,[],[f15])).
% 1.56/1.00  
% 1.56/1.00  fof(f25,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/1.00    inference(nnf_transformation,[],[f16])).
% 1.56/1.00  
% 1.56/1.00  fof(f40,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f25])).
% 1.56/1.00  
% 1.56/1.00  fof(f49,plain,(
% 1.56/1.00    k1_xboole_0 != sK2),
% 1.56/1.00    inference(cnf_transformation,[],[f29])).
% 1.56/1.00  
% 1.56/1.00  fof(f4,axiom,(
% 1.56/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f13,plain,(
% 1.56/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/1.00    inference(ennf_transformation,[],[f4])).
% 1.56/1.00  
% 1.56/1.00  fof(f38,plain,(
% 1.56/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f13])).
% 1.56/1.00  
% 1.56/1.00  fof(f50,plain,(
% 1.56/1.00    r2_hidden(sK6,sK1)),
% 1.56/1.00    inference(cnf_transformation,[],[f29])).
% 1.56/1.00  
% 1.56/1.00  fof(f5,axiom,(
% 1.56/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.56/1.00  
% 1.56/1.00  fof(f14,plain,(
% 1.56/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/1.00    inference(ennf_transformation,[],[f5])).
% 1.56/1.00  
% 1.56/1.00  fof(f39,plain,(
% 1.56/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/1.00    inference(cnf_transformation,[],[f14])).
% 1.56/1.00  
% 1.56/1.00  fof(f53,plain,(
% 1.56/1.00    ~r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))),
% 1.56/1.00    inference(cnf_transformation,[],[f29])).
% 1.56/1.00  
% 1.56/1.00  fof(f51,plain,(
% 1.56/1.00    r2_hidden(sK6,sK3)),
% 1.56/1.00    inference(cnf_transformation,[],[f29])).
% 1.56/1.00  
% 1.56/1.00  cnf(c_17,negated_conjecture,
% 1.56/1.00      ( k1_funct_1(sK4,sK6) = sK5 ),
% 1.56/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_7,plain,
% 1.56/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.56/1.00      | v1_relat_1(X0) ),
% 1.56/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_21,negated_conjecture,
% 1.56/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.56/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_359,plain,
% 1.56/1.00      ( v1_relat_1(X0)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.56/1.00      | sK4 != X0 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_360,plain,
% 1.56/1.00      ( v1_relat_1(sK4)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_359]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_4,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.56/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 1.56/1.00      | ~ v1_funct_1(X1)
% 1.56/1.00      | ~ v1_relat_1(X1) ),
% 1.56/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_23,negated_conjecture,
% 1.56/1.00      ( v1_funct_1(sK4) ),
% 1.56/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_263,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.56/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 1.56/1.00      | ~ v1_relat_1(X1)
% 1.56/1.00      | sK4 != X1 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_264,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 1.56/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
% 1.56/1.00      | ~ v1_relat_1(sK4) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_263]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_485,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 1.56/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.56/1.00      inference(resolution,[status(thm)],[c_360,c_264]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_754,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 1.56/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
% 1.56/1.00      | ~ sP6_iProver_split ),
% 1.56/1.00      inference(splitting,
% 1.56/1.00                [splitting(split),new_symbols(definition,[sP6_iProver_split])],
% 1.56/1.00                [c_485]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1114,plain,
% 1.56/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 1.56/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
% 1.56/1.00      | sP6_iProver_split != iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_755,plain,
% 1.56/1.00      ( sP6_iProver_split | sP0_iProver_split ),
% 1.56/1.00      inference(splitting,
% 1.56/1.00                [splitting(split),new_symbols(definition,[])],
% 1.56/1.00                [c_485]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_810,plain,
% 1.56/1.00      ( sP6_iProver_split = iProver_top
% 1.56/1.00      | sP0_iProver_split = iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_811,plain,
% 1.56/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 1.56/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
% 1.56/1.00      | sP6_iProver_split != iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_759,plain,( X0 = X0 ),theory(equality) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1275,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_759]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_0,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,X1)
% 1.56/1.00      | r2_hidden(X2,k9_relat_1(X3,X1))
% 1.56/1.00      | ~ r2_hidden(X0,k1_relat_1(X3))
% 1.56/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 1.56/1.00      | ~ v1_relat_1(X3) ),
% 1.56/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_558,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,X1)
% 1.56/1.00      | r2_hidden(X2,k9_relat_1(X3,X1))
% 1.56/1.00      | ~ r2_hidden(X0,k1_relat_1(X3))
% 1.56/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.56/1.00      | sK4 != X3 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_360]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_559,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,X1)
% 1.56/1.00      | r2_hidden(X2,k9_relat_1(sK4,X1))
% 1.56/1.00      | ~ r2_hidden(X0,k1_relat_1(sK4))
% 1.56/1.00      | ~ r2_hidden(k4_tarski(X0,X2),sK4)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_558]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_6,plain,
% 1.56/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 1.56/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 1.56/1.00      | ~ v1_funct_1(X1)
% 1.56/1.00      | ~ v1_relat_1(X1) ),
% 1.56/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_248,plain,
% 1.56/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 1.56/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 1.56/1.00      | ~ v1_relat_1(X1)
% 1.56/1.00      | sK4 != X1 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_249,plain,
% 1.56/1.00      ( r2_hidden(X0,k1_relat_1(sK4))
% 1.56/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 1.56/1.00      | ~ v1_relat_1(sK4) ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_248]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_499,plain,
% 1.56/1.00      ( r2_hidden(X0,k1_relat_1(sK4))
% 1.56/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.56/1.00      inference(resolution,[status(thm)],[c_360,c_249]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_568,plain,
% 1.56/1.00      ( ~ r2_hidden(X0,X1)
% 1.56/1.00      | r2_hidden(X2,k9_relat_1(sK4,X1))
% 1.56/1.00      | ~ r2_hidden(k4_tarski(X0,X2),sK4)
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.56/1.00      inference(forward_subsumption_resolution,
% 1.56/1.00                [status(thm)],
% 1.56/1.00                [c_559,c_499]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_743,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.56/1.00      | ~ sP0_iProver_split ),
% 1.56/1.00      inference(splitting,
% 1.56/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.56/1.00                [c_568]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1276,plain,
% 1.56/1.00      ( ~ sP0_iProver_split
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.56/1.00      inference(instantiation,[status(thm)],[c_743]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1280,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.56/1.00      | sP0_iProver_split != iProver_top ),
% 1.56/1.00      inference(predicate_to_equality,[status(thm)],[c_1276]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1571,plain,
% 1.56/1.00      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
% 1.56/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 1.56/1.00      inference(global_propositional_subsumption,
% 1.56/1.00                [status(thm)],
% 1.56/1.00                [c_1114,c_810,c_811,c_1275,c_1280]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_1572,plain,
% 1.56/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 1.56/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
% 1.56/1.00      inference(renaming,[status(thm)],[c_1571]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_22,negated_conjecture,
% 1.56/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 1.56/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_15,plain,
% 1.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.56/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.56/1.00      | k1_relset_1(X1,X2,X0) = X1
% 1.56/1.00      | k1_xboole_0 = X2 ),
% 1.56/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_305,plain,
% 1.56/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.56/1.00      | k1_relset_1(X1,X2,X0) = X1
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.56/1.00      | sK4 != X0
% 1.56/1.00      | k1_xboole_0 = X2 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_306,plain,
% 1.56/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 1.56/1.00      | k1_relset_1(X0,X1,sK4) = X0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.56/1.00      | k1_xboole_0 = X1 ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_305]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_617,plain,
% 1.56/1.00      ( k1_relset_1(X0,X1,sK4) = X0
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.56/1.00      | sK4 != sK4
% 1.56/1.00      | sK2 != X1
% 1.56/1.00      | sK1 != X0
% 1.56/1.00      | k1_xboole_0 = X1 ),
% 1.56/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_306]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_618,plain,
% 1.56/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.56/1.00      | k1_xboole_0 = sK2 ),
% 1.56/1.00      inference(unflattening,[status(thm)],[c_617]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_20,negated_conjecture,
% 1.56/1.00      ( k1_xboole_0 != sK2 ),
% 1.56/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_619,plain,
% 1.56/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.56/1.00      | k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 1.56/1.00      inference(global_propositional_subsumption,
% 1.56/1.00                [status(thm)],
% 1.56/1.00                [c_618,c_20]) ).
% 1.56/1.00  
% 1.56/1.00  cnf(c_620,plain,
% 1.56/1.00      ( k1_relset_1(sK1,sK2,sK4) = sK1
% 1.56/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.56/1.00      inference(renaming,[status(thm)],[c_619]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_679,plain,
% 1.56/1.01      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 1.56/1.01      inference(equality_resolution_simp,[status(thm)],[c_620]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_8,plain,
% 1.56/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.56/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.56/1.01      inference(cnf_transformation,[],[f38]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_350,plain,
% 1.56/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.56/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.56/1.01      | sK4 != X2 ),
% 1.56/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_351,plain,
% 1.56/1.01      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 1.56/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.56/1.01      inference(unflattening,[status(thm)],[c_350]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1294,plain,
% 1.56/1.01      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 1.56/1.01      inference(equality_resolution,[status(thm)],[c_351]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1481,plain,
% 1.56/1.01      ( k1_relat_1(sK4) = sK1 ),
% 1.56/1.01      inference(demodulation,[status(thm)],[c_679,c_1294]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1577,plain,
% 1.56/1.01      ( r2_hidden(X0,sK1) != iProver_top
% 1.56/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
% 1.56/1.01      inference(light_normalisation,[status(thm)],[c_1572,c_1481]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1583,plain,
% 1.56/1.01      ( r2_hidden(k4_tarski(sK6,sK5),sK4) = iProver_top
% 1.56/1.01      | r2_hidden(sK6,sK1) != iProver_top ),
% 1.56/1.01      inference(superposition,[status(thm)],[c_17,c_1577]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_19,negated_conjecture,
% 1.56/1.01      ( r2_hidden(sK6,sK1) ),
% 1.56/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_27,plain,
% 1.56/1.01      ( r2_hidden(sK6,sK1) = iProver_top ),
% 1.56/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1637,plain,
% 1.56/1.01      ( r2_hidden(k4_tarski(sK6,sK5),sK4) = iProver_top ),
% 1.56/1.01      inference(global_propositional_subsumption,
% 1.56/1.01                [status(thm)],
% 1.56/1.01                [c_1583,c_27]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_744,plain,
% 1.56/1.01      ( ~ r2_hidden(X0,X1)
% 1.56/1.01      | r2_hidden(X2,k9_relat_1(sK4,X1))
% 1.56/1.01      | ~ r2_hidden(k4_tarski(X0,X2),sK4)
% 1.56/1.01      | ~ sP1_iProver_split ),
% 1.56/1.01      inference(splitting,
% 1.56/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.56/1.01                [c_568]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1099,plain,
% 1.56/1.01      ( r2_hidden(X0,X1) != iProver_top
% 1.56/1.01      | r2_hidden(X2,k9_relat_1(sK4,X1)) = iProver_top
% 1.56/1.01      | r2_hidden(k4_tarski(X0,X2),sK4) != iProver_top
% 1.56/1.01      | sP1_iProver_split != iProver_top ),
% 1.56/1.01      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_745,plain,
% 1.56/1.01      ( sP1_iProver_split | sP0_iProver_split ),
% 1.56/1.01      inference(splitting,
% 1.56/1.01                [splitting(split),new_symbols(definition,[])],
% 1.56/1.01                [c_568]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_783,plain,
% 1.56/1.01      ( sP1_iProver_split = iProver_top
% 1.56/1.01      | sP0_iProver_split = iProver_top ),
% 1.56/1.01      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_784,plain,
% 1.56/1.01      ( r2_hidden(X0,X1) != iProver_top
% 1.56/1.01      | r2_hidden(X2,k9_relat_1(sK4,X1)) = iProver_top
% 1.56/1.01      | r2_hidden(k4_tarski(X0,X2),sK4) != iProver_top
% 1.56/1.01      | sP1_iProver_split != iProver_top ),
% 1.56/1.01      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1645,plain,
% 1.56/1.01      ( r2_hidden(k4_tarski(X0,X2),sK4) != iProver_top
% 1.56/1.01      | r2_hidden(X2,k9_relat_1(sK4,X1)) = iProver_top
% 1.56/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 1.56/1.01      inference(global_propositional_subsumption,
% 1.56/1.01                [status(thm)],
% 1.56/1.01                [c_1099,c_783,c_784,c_1275,c_1280]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1646,plain,
% 1.56/1.01      ( r2_hidden(X0,X1) != iProver_top
% 1.56/1.01      | r2_hidden(X2,k9_relat_1(sK4,X1)) = iProver_top
% 1.56/1.01      | r2_hidden(k4_tarski(X0,X2),sK4) != iProver_top ),
% 1.56/1.01      inference(renaming,[status(thm)],[c_1645]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1655,plain,
% 1.56/1.01      ( r2_hidden(sK6,X0) != iProver_top
% 1.56/1.01      | r2_hidden(sK5,k9_relat_1(sK4,X0)) = iProver_top ),
% 1.56/1.01      inference(superposition,[status(thm)],[c_1637,c_1646]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_9,plain,
% 1.56/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.56/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.56/1.01      inference(cnf_transformation,[],[f39]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_341,plain,
% 1.56/1.01      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 1.56/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.56/1.01      | sK4 != X2 ),
% 1.56/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_342,plain,
% 1.56/1.01      ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
% 1.56/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.56/1.01      inference(unflattening,[status(thm)],[c_341]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1317,plain,
% 1.56/1.01      ( k7_relset_1(sK1,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 1.56/1.01      inference(equality_resolution,[status(thm)],[c_342]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_16,negated_conjecture,
% 1.56/1.01      ( ~ r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
% 1.56/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1121,plain,
% 1.56/1.01      ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) != iProver_top ),
% 1.56/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1349,plain,
% 1.56/1.01      ( r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top ),
% 1.56/1.01      inference(demodulation,[status(thm)],[c_1317,c_1121]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_1708,plain,
% 1.56/1.01      ( r2_hidden(sK6,sK3) != iProver_top ),
% 1.56/1.01      inference(superposition,[status(thm)],[c_1655,c_1349]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_18,negated_conjecture,
% 1.56/1.01      ( r2_hidden(sK6,sK3) ),
% 1.56/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(c_28,plain,
% 1.56/1.01      ( r2_hidden(sK6,sK3) = iProver_top ),
% 1.56/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.56/1.01  
% 1.56/1.01  cnf(contradiction,plain,
% 1.56/1.01      ( $false ),
% 1.56/1.01      inference(minisat,[status(thm)],[c_1708,c_28]) ).
% 1.56/1.01  
% 1.56/1.01  
% 1.56/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.56/1.01  
% 1.56/1.01  ------                               Statistics
% 1.56/1.01  
% 1.56/1.01  ------ General
% 1.56/1.01  
% 1.56/1.01  abstr_ref_over_cycles:                  0
% 1.56/1.01  abstr_ref_under_cycles:                 0
% 1.56/1.01  gc_basic_clause_elim:                   0
% 1.56/1.01  forced_gc_time:                         0
% 1.56/1.01  parsing_time:                           0.01
% 1.56/1.01  unif_index_cands_time:                  0.
% 1.56/1.01  unif_index_add_time:                    0.
% 1.56/1.01  orderings_time:                         0.
% 1.56/1.01  out_proof_time:                         0.012
% 1.56/1.01  total_time:                             0.089
% 1.56/1.01  num_of_symbols:                         60
% 1.56/1.01  num_of_terms:                           1259
% 1.56/1.01  
% 1.56/1.01  ------ Preprocessing
% 1.56/1.01  
% 1.56/1.01  num_of_splits:                          14
% 1.56/1.01  num_of_split_atoms:                     8
% 1.56/1.01  num_of_reused_defs:                     6
% 1.56/1.01  num_eq_ax_congr_red:                    15
% 1.56/1.01  num_of_sem_filtered_clauses:            1
% 1.56/1.01  num_of_subtypes:                        0
% 1.56/1.01  monotx_restored_types:                  0
% 1.56/1.01  sat_num_of_epr_types:                   0
% 1.56/1.01  sat_num_of_non_cyclic_types:            0
% 1.56/1.01  sat_guarded_non_collapsed_types:        0
% 1.56/1.01  num_pure_diseq_elim:                    0
% 1.56/1.01  simp_replaced_by:                       0
% 1.56/1.01  res_preprocessed:                       116
% 1.56/1.01  prep_upred:                             0
% 1.56/1.01  prep_unflattend:                        32
% 1.56/1.01  smt_new_axioms:                         0
% 1.56/1.01  pred_elim_cands:                        1
% 1.56/1.01  pred_elim:                              4
% 1.56/1.01  pred_elim_cl:                           7
% 1.56/1.01  pred_elim_cycles:                       6
% 1.56/1.01  merged_defs:                            0
% 1.56/1.01  merged_defs_ncl:                        0
% 1.56/1.01  bin_hyper_res:                          0
% 1.56/1.01  prep_cycles:                            4
% 1.56/1.01  pred_elim_time:                         0.01
% 1.56/1.01  splitting_time:                         0.
% 1.56/1.01  sem_filter_time:                        0.
% 1.56/1.01  monotx_time:                            0.
% 1.56/1.01  subtype_inf_time:                       0.
% 1.56/1.01  
% 1.56/1.01  ------ Problem properties
% 1.56/1.01  
% 1.56/1.01  clauses:                                31
% 1.56/1.01  conjectures:                            5
% 1.56/1.01  epr:                                    10
% 1.56/1.01  horn:                                   23
% 1.56/1.01  ground:                                 15
% 1.56/1.01  unary:                                  6
% 1.56/1.01  binary:                                 16
% 1.56/1.01  lits:                                   67
% 1.56/1.01  lits_eq:                                22
% 1.56/1.01  fd_pure:                                0
% 1.56/1.01  fd_pseudo:                              0
% 1.56/1.01  fd_cond:                                0
% 1.56/1.01  fd_pseudo_cond:                         1
% 1.56/1.01  ac_symbols:                             0
% 1.56/1.01  
% 1.56/1.01  ------ Propositional Solver
% 1.56/1.01  
% 1.56/1.01  prop_solver_calls:                      26
% 1.56/1.01  prop_fast_solver_calls:                 705
% 1.56/1.01  smt_solver_calls:                       0
% 1.56/1.01  smt_fast_solver_calls:                  0
% 1.56/1.01  prop_num_of_clauses:                    451
% 1.56/1.01  prop_preprocess_simplified:             2751
% 1.56/1.01  prop_fo_subsumed:                       11
% 1.56/1.01  prop_solver_time:                       0.
% 1.56/1.01  smt_solver_time:                        0.
% 1.56/1.01  smt_fast_solver_time:                   0.
% 1.56/1.01  prop_fast_solver_time:                  0.
% 1.56/1.01  prop_unsat_core_time:                   0.
% 1.56/1.01  
% 1.56/1.01  ------ QBF
% 1.56/1.01  
% 1.56/1.01  qbf_q_res:                              0
% 1.56/1.01  qbf_num_tautologies:                    0
% 1.56/1.01  qbf_prep_cycles:                        0
% 1.56/1.01  
% 1.56/1.01  ------ BMC1
% 1.56/1.01  
% 1.56/1.01  bmc1_current_bound:                     -1
% 1.56/1.01  bmc1_last_solved_bound:                 -1
% 1.56/1.01  bmc1_unsat_core_size:                   -1
% 1.56/1.01  bmc1_unsat_core_parents_size:           -1
% 1.56/1.01  bmc1_merge_next_fun:                    0
% 1.56/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.56/1.01  
% 1.56/1.01  ------ Instantiation
% 1.56/1.01  
% 1.56/1.01  inst_num_of_clauses:                    110
% 1.56/1.01  inst_num_in_passive:                    6
% 1.56/1.01  inst_num_in_active:                     99
% 1.56/1.01  inst_num_in_unprocessed:                5
% 1.56/1.01  inst_num_of_loops:                      120
% 1.56/1.01  inst_num_of_learning_restarts:          0
% 1.56/1.01  inst_num_moves_active_passive:          17
% 1.56/1.01  inst_lit_activity:                      0
% 1.56/1.01  inst_lit_activity_moves:                0
% 1.56/1.01  inst_num_tautologies:                   0
% 1.56/1.01  inst_num_prop_implied:                  0
% 1.56/1.01  inst_num_existing_simplified:           0
% 1.56/1.01  inst_num_eq_res_simplified:             0
% 1.56/1.01  inst_num_child_elim:                    0
% 1.56/1.01  inst_num_of_dismatching_blockings:      8
% 1.56/1.01  inst_num_of_non_proper_insts:           71
% 1.56/1.01  inst_num_of_duplicates:                 0
% 1.56/1.01  inst_inst_num_from_inst_to_res:         0
% 1.56/1.01  inst_dismatching_checking_time:         0.
% 1.56/1.01  
% 1.56/1.01  ------ Resolution
% 1.56/1.01  
% 1.56/1.01  res_num_of_clauses:                     0
% 1.56/1.01  res_num_in_passive:                     0
% 1.56/1.01  res_num_in_active:                      0
% 1.56/1.01  res_num_of_loops:                       120
% 1.56/1.01  res_forward_subset_subsumed:            23
% 1.56/1.01  res_backward_subset_subsumed:           0
% 1.56/1.01  res_forward_subsumed:                   0
% 1.56/1.01  res_backward_subsumed:                  0
% 1.56/1.01  res_forward_subsumption_resolution:     1
% 1.56/1.01  res_backward_subsumption_resolution:    0
% 1.56/1.01  res_clause_to_clause_subsumption:       40
% 1.56/1.01  res_orphan_elimination:                 0
% 1.56/1.01  res_tautology_del:                      21
% 1.56/1.01  res_num_eq_res_simplified:              1
% 1.56/1.01  res_num_sel_changes:                    0
% 1.56/1.01  res_moves_from_active_to_pass:          0
% 1.56/1.01  
% 1.56/1.01  ------ Superposition
% 1.56/1.01  
% 1.56/1.01  sup_time_total:                         0.
% 1.56/1.01  sup_time_generating:                    0.
% 1.56/1.01  sup_time_sim_full:                      0.
% 1.56/1.01  sup_time_sim_immed:                     0.
% 1.56/1.01  
% 1.56/1.01  sup_num_of_clauses:                     31
% 1.56/1.01  sup_num_in_active:                      20
% 1.56/1.01  sup_num_in_passive:                     11
% 1.56/1.01  sup_num_of_loops:                       22
% 1.56/1.01  sup_fw_superposition:                   3
% 1.56/1.01  sup_bw_superposition:                   5
% 1.56/1.01  sup_immediate_simplified:               0
% 1.56/1.01  sup_given_eliminated:                   0
% 1.56/1.01  comparisons_done:                       0
% 1.56/1.01  comparisons_avoided:                    0
% 1.56/1.01  
% 1.56/1.01  ------ Simplifications
% 1.56/1.01  
% 1.56/1.01  
% 1.56/1.01  sim_fw_subset_subsumed:                 0
% 1.56/1.01  sim_bw_subset_subsumed:                 0
% 1.56/1.01  sim_fw_subsumed:                        0
% 1.56/1.01  sim_bw_subsumed:                        0
% 1.56/1.01  sim_fw_subsumption_res:                 0
% 1.56/1.01  sim_bw_subsumption_res:                 0
% 1.56/1.01  sim_tautology_del:                      1
% 1.56/1.01  sim_eq_tautology_del:                   1
% 1.56/1.01  sim_eq_res_simp:                        0
% 1.56/1.01  sim_fw_demodulated:                     0
% 1.56/1.01  sim_bw_demodulated:                     3
% 1.56/1.01  sim_light_normalised:                   2
% 1.56/1.01  sim_joinable_taut:                      0
% 1.56/1.01  sim_joinable_simp:                      0
% 1.56/1.01  sim_ac_normalised:                      0
% 1.56/1.01  sim_smt_subsumption:                    0
% 1.56/1.01  
%------------------------------------------------------------------------------

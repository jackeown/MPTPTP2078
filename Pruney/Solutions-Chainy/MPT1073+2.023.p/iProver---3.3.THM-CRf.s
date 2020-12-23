%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:04 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 862 expanded)
%              Number of clauses        :  101 ( 315 expanded)
%              Number of leaves         :   19 ( 166 expanded)
%              Depth                    :   29
%              Number of atoms          :  490 (3540 expanded)
%              Number of equality atoms :  235 ( 938 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f54,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK6,X4) != sK3
          | ~ m1_subset_1(X4,sK4) )
      & r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6))
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ! [X4] :
        ( k1_funct_1(sK6,X4) != sK3
        | ~ m1_subset_1(X4,sK4) )
    & r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f40,f54])).

fof(f91,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f55])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f55])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
     => ( r2_hidden(sK2(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(sK2(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f51])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f96,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f76])).

fof(f93,plain,(
    ! [X4] :
      ( k1_funct_1(sK6,X4) != sK3
      | ~ m1_subset_1(X4,sK4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1506,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1509,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1991,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1506,c_1509])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1992,plain,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1991])).

cnf(c_2478,plain,
    ( sK5 = k1_xboole_0
    | k1_relset_1(sK4,sK5,sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1991,c_36,c_1992])).

cnf(c_2479,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2478])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1519,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2877,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1506,c_1519])).

cnf(c_3269,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2479,c_2877])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1520,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2604,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1506,c_1520])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1525,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2753,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2604,c_1525])).

cnf(c_3535,plain,
    ( k9_relat_1(sK6,sK4) = k2_relat_1(sK6)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3269,c_2753])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1528,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1536,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3779,plain,
    ( m1_subset_1(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(X0,k9_relat_1(X2,X1)) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1528,c_1536])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1527,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1518,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2863,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1506,c_1518])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1507,plain,
    ( r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3165,plain,
    ( r2_hidden(sK3,k2_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2863,c_1507])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X0)
    | k4_tarski(sK1(X3,X1,X2),sK2(X3,X1,X2)) = X3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1515,plain,
    ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5663,plain,
    ( k4_tarski(sK1(X0,sK4,sK5),sK2(X0,sK4,sK5)) = X0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1506,c_1515])).

cnf(c_6145,plain,
    ( k4_tarski(sK1(k4_tarski(sK0(X0,X1,sK6),X0),sK4,sK5),sK2(k4_tarski(sK0(X0,X1,sK6),X0),sK4,sK5)) = k4_tarski(sK0(X0,X1,sK6),X0)
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_5663])).

cnf(c_40,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1867,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1868,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1867])).

cnf(c_6665,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | k4_tarski(sK1(k4_tarski(sK0(X0,X1,sK6),X0),sK4,sK5),sK2(k4_tarski(sK0(X0,X1,sK6),X0),sK4,sK5)) = k4_tarski(sK0(X0,X1,sK6),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6145,c_40,c_1868])).

cnf(c_6666,plain,
    ( k4_tarski(sK1(k4_tarski(sK0(X0,X1,sK6),X0),sK4,sK5),sK2(k4_tarski(sK0(X0,X1,sK6),X0),sK4,sK5)) = k4_tarski(sK0(X0,X1,sK6),X0)
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6665])).

cnf(c_6675,plain,
    ( k4_tarski(sK1(k4_tarski(sK0(X0,k1_relat_1(sK6),sK6),X0),sK4,sK5),sK2(k4_tarski(sK0(X0,k1_relat_1(sK6),sK6),X0),sK4,sK5)) = k4_tarski(sK0(X0,k1_relat_1(sK6),sK6),X0)
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2753,c_6666])).

cnf(c_8791,plain,
    ( k4_tarski(sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5),sK2(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)) = k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3) ),
    inference(superposition,[status(thm)],[c_3165,c_6675])).

cnf(c_19,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1522,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8828,plain,
    ( k1_funct_1(X0,sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)) = sK2(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)
    | r2_hidden(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8791,c_1522])).

cnf(c_9510,plain,
    ( k1_funct_1(sK6,sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)) = sK2(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)
    | r2_hidden(sK3,k9_relat_1(sK6,k1_relat_1(sK6))) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_8828])).

cnf(c_9526,plain,
    ( k1_funct_1(sK6,sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)) = sK2(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)
    | r2_hidden(sK3,k2_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9510,c_2753])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_38,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_9536,plain,
    ( k1_funct_1(sK6,sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)) = sK2(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9526,c_38,c_40,c_1868,c_3165])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1523,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9540,plain,
    ( r2_hidden(sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5),sK2(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)),sK6) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9536,c_1523])).

cnf(c_9550,plain,
    ( r2_hidden(sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK6) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9540,c_8791])).

cnf(c_41,plain,
    ( r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1937,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2025,plain,
    ( ~ v1_relat_1(sK6)
    | k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_678,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2130,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_679,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2429,plain,
    ( X0 != X1
    | X0 = k2_relset_1(sK4,sK5,sK6)
    | k2_relset_1(sK4,sK5,sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_3216,plain,
    ( X0 = k2_relset_1(sK4,sK5,sK6)
    | X0 != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2429])).

cnf(c_3389,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relset_1(sK4,sK5,sK6)
    | k9_relat_1(sK6,k1_relat_1(sK6)) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3216])).

cnf(c_680,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1940,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6))
    | X1 != k2_relset_1(sK4,sK5,sK6)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_2129,plain,
    ( r2_hidden(sK3,X0)
    | ~ r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6))
    | X0 != k2_relset_1(sK4,sK5,sK6)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1940])).

cnf(c_4976,plain,
    ( ~ r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6))
    | r2_hidden(sK3,k9_relat_1(sK6,k1_relat_1(sK6)))
    | k9_relat_1(sK6,k1_relat_1(sK6)) != k2_relset_1(sK4,sK5,sK6)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_4977,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) != k2_relset_1(sK4,sK5,sK6)
    | sK3 != sK3
    | r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) != iProver_top
    | r2_hidden(sK3,k9_relat_1(sK6,k1_relat_1(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4976])).

cnf(c_6092,plain,
    ( r2_hidden(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK6)
    | ~ r2_hidden(sK3,k9_relat_1(sK6,k1_relat_1(sK6)))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_6097,plain,
    ( r2_hidden(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK6) = iProver_top
    | r2_hidden(sK3,k9_relat_1(sK6,k1_relat_1(sK6))) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6092])).

cnf(c_9871,plain,
    ( r2_hidden(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9550,c_35,c_40,c_41,c_1867,c_1868,c_1937,c_2025,c_2130,c_3389,c_4977,c_6097])).

cnf(c_9881,plain,
    ( k1_funct_1(sK6,sK0(sK3,k1_relat_1(sK6),sK6)) = sK3
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9871,c_1522])).

cnf(c_9444,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK0(sK3,k1_relat_1(sK6),sK6)) = sK3 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_10588,plain,
    ( k1_funct_1(sK6,sK0(sK3,k1_relat_1(sK6),sK6)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9881,c_37,c_35,c_34,c_1867,c_1937,c_2025,c_2130,c_3389,c_4976,c_6092,c_9444])).

cnf(c_33,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | k1_funct_1(sK6,X0) != sK3 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1508,plain,
    ( k1_funct_1(sK6,X0) != sK3
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10594,plain,
    ( m1_subset_1(sK0(sK3,k1_relat_1(sK6),sK6),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10588,c_1508])).

cnf(c_10604,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK0(sK3,sK4,sK6),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3269,c_10594])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_134,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_681,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4990,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_4991,plain,
    ( sK5 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4990])).

cnf(c_4993,plain,
    ( sK5 != k1_xboole_0
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4991])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK2(X3,X1,X2),X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1517,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(sK2(X3,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5009,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK2(X0,sK4,sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1506,c_1517])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1540,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5174,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5009,c_1540])).

cnf(c_5313,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_5174])).

cnf(c_7871,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5313,c_40,c_1868])).

cnf(c_7882,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2753,c_7871])).

cnf(c_7932,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3165,c_7882])).

cnf(c_10844,plain,
    ( m1_subset_1(sK0(sK3,sK4,sK6),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10604,c_134,c_4993,c_7932])).

cnf(c_10849,plain,
    ( r2_hidden(sK3,k9_relat_1(sK6,sK4)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3779,c_10844])).

cnf(c_11013,plain,
    ( r2_hidden(sK3,k9_relat_1(sK6,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10849,c_40,c_1868])).

cnf(c_11018,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3535,c_11013])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11018,c_7932,c_4993,c_3165,c_134])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:03:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 4.13/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.01  
% 4.13/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.13/1.01  
% 4.13/1.01  ------  iProver source info
% 4.13/1.01  
% 4.13/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.13/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.13/1.01  git: non_committed_changes: false
% 4.13/1.01  git: last_make_outside_of_git: false
% 4.13/1.01  
% 4.13/1.01  ------ 
% 4.13/1.01  ------ Parsing...
% 4.13/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.01  ------ Proving...
% 4.13/1.01  ------ Problem Properties 
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  clauses                                 37
% 4.13/1.01  conjectures                             5
% 4.13/1.01  EPR                                     7
% 4.13/1.01  Horn                                    33
% 4.13/1.01  unary                                   7
% 4.13/1.01  binary                                  9
% 4.13/1.01  lits                                    98
% 4.13/1.01  lits eq                                 16
% 4.13/1.01  fd_pure                                 0
% 4.13/1.01  fd_pseudo                               0
% 4.13/1.01  fd_cond                                 3
% 4.13/1.01  fd_pseudo_cond                          2
% 4.13/1.01  AC symbols                              0
% 4.13/1.01  
% 4.13/1.01  ------ Input Options Time Limit: Unbounded
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ 
% 4.13/1.01  Current options:
% 4.13/1.01  ------ 
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  ------ Proving...
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  % SZS status Theorem for theBenchmark.p
% 4.13/1.01  
% 4.13/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.13/1.01  
% 4.13/1.01  fof(f18,conjecture,(
% 4.13/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f19,negated_conjecture,(
% 4.13/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 4.13/1.01    inference(negated_conjecture,[],[f18])).
% 4.13/1.01  
% 4.13/1.01  fof(f39,plain,(
% 4.13/1.01    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 4.13/1.01    inference(ennf_transformation,[],[f19])).
% 4.13/1.01  
% 4.13/1.01  fof(f40,plain,(
% 4.13/1.01    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 4.13/1.01    inference(flattening,[],[f39])).
% 4.13/1.01  
% 4.13/1.01  fof(f54,plain,(
% 4.13/1.01    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK6,X4) != sK3 | ~m1_subset_1(X4,sK4)) & r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 4.13/1.01    introduced(choice_axiom,[])).
% 4.13/1.01  
% 4.13/1.01  fof(f55,plain,(
% 4.13/1.01    ! [X4] : (k1_funct_1(sK6,X4) != sK3 | ~m1_subset_1(X4,sK4)) & r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 4.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f40,f54])).
% 4.13/1.01  
% 4.13/1.01  fof(f91,plain,(
% 4.13/1.01    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 4.13/1.01    inference(cnf_transformation,[],[f55])).
% 4.13/1.01  
% 4.13/1.01  fof(f17,axiom,(
% 4.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f37,plain,(
% 4.13/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.13/1.01    inference(ennf_transformation,[],[f17])).
% 4.13/1.01  
% 4.13/1.01  fof(f38,plain,(
% 4.13/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.13/1.01    inference(flattening,[],[f37])).
% 4.13/1.01  
% 4.13/1.01  fof(f53,plain,(
% 4.13/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.13/1.01    inference(nnf_transformation,[],[f38])).
% 4.13/1.01  
% 4.13/1.01  fof(f83,plain,(
% 4.13/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.13/1.01    inference(cnf_transformation,[],[f53])).
% 4.13/1.01  
% 4.13/1.01  fof(f90,plain,(
% 4.13/1.01    v1_funct_2(sK6,sK4,sK5)),
% 4.13/1.01    inference(cnf_transformation,[],[f55])).
% 4.13/1.01  
% 4.13/1.01  fof(f14,axiom,(
% 4.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f33,plain,(
% 4.13/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.13/1.01    inference(ennf_transformation,[],[f14])).
% 4.13/1.01  
% 4.13/1.01  fof(f78,plain,(
% 4.13/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.13/1.01    inference(cnf_transformation,[],[f33])).
% 4.13/1.01  
% 4.13/1.01  fof(f13,axiom,(
% 4.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f32,plain,(
% 4.13/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.13/1.01    inference(ennf_transformation,[],[f13])).
% 4.13/1.01  
% 4.13/1.01  fof(f77,plain,(
% 4.13/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.13/1.01    inference(cnf_transformation,[],[f32])).
% 4.13/1.01  
% 4.13/1.01  fof(f10,axiom,(
% 4.13/1.01    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f27,plain,(
% 4.13/1.01    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.13/1.01    inference(ennf_transformation,[],[f10])).
% 4.13/1.01  
% 4.13/1.01  fof(f72,plain,(
% 4.13/1.01    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f27])).
% 4.13/1.01  
% 4.13/1.01  fof(f9,axiom,(
% 4.13/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f26,plain,(
% 4.13/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 4.13/1.01    inference(ennf_transformation,[],[f9])).
% 4.13/1.01  
% 4.13/1.01  fof(f45,plain,(
% 4.13/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.13/1.01    inference(nnf_transformation,[],[f26])).
% 4.13/1.01  
% 4.13/1.01  fof(f46,plain,(
% 4.13/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.13/1.01    inference(rectify,[],[f45])).
% 4.13/1.01  
% 4.13/1.01  fof(f47,plain,(
% 4.13/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 4.13/1.01    introduced(choice_axiom,[])).
% 4.13/1.01  
% 4.13/1.01  fof(f48,plain,(
% 4.13/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 4.13/1.01  
% 4.13/1.01  fof(f70,plain,(
% 4.13/1.01    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f48])).
% 4.13/1.01  
% 4.13/1.01  fof(f4,axiom,(
% 4.13/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f22,plain,(
% 4.13/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 4.13/1.01    inference(ennf_transformation,[],[f4])).
% 4.13/1.01  
% 4.13/1.01  fof(f61,plain,(
% 4.13/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f22])).
% 4.13/1.01  
% 4.13/1.01  fof(f69,plain,(
% 4.13/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f48])).
% 4.13/1.01  
% 4.13/1.01  fof(f15,axiom,(
% 4.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f34,plain,(
% 4.13/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.13/1.01    inference(ennf_transformation,[],[f15])).
% 4.13/1.01  
% 4.13/1.01  fof(f79,plain,(
% 4.13/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.13/1.01    inference(cnf_transformation,[],[f34])).
% 4.13/1.01  
% 4.13/1.01  fof(f92,plain,(
% 4.13/1.01    r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6))),
% 4.13/1.01    inference(cnf_transformation,[],[f55])).
% 4.13/1.01  
% 4.13/1.01  fof(f16,axiom,(
% 4.13/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f35,plain,(
% 4.13/1.01    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 4.13/1.01    inference(ennf_transformation,[],[f16])).
% 4.13/1.01  
% 4.13/1.01  fof(f36,plain,(
% 4.13/1.01    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 4.13/1.01    inference(flattening,[],[f35])).
% 4.13/1.01  
% 4.13/1.01  fof(f51,plain,(
% 4.13/1.01    ! [X2,X1,X0] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) => (r2_hidden(sK2(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0))),
% 4.13/1.01    introduced(choice_axiom,[])).
% 4.13/1.01  
% 4.13/1.01  fof(f52,plain,(
% 4.13/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(sK2(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 4.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f51])).
% 4.13/1.01  
% 4.13/1.01  fof(f80,plain,(
% 4.13/1.01    ( ! [X2,X0,X3,X1] : (k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0 | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 4.13/1.01    inference(cnf_transformation,[],[f52])).
% 4.13/1.01  
% 4.13/1.01  fof(f12,axiom,(
% 4.13/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f30,plain,(
% 4.13/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.13/1.01    inference(ennf_transformation,[],[f12])).
% 4.13/1.01  
% 4.13/1.01  fof(f31,plain,(
% 4.13/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.13/1.01    inference(flattening,[],[f30])).
% 4.13/1.01  
% 4.13/1.01  fof(f49,plain,(
% 4.13/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.13/1.01    inference(nnf_transformation,[],[f31])).
% 4.13/1.01  
% 4.13/1.01  fof(f50,plain,(
% 4.13/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.13/1.01    inference(flattening,[],[f49])).
% 4.13/1.01  
% 4.13/1.01  fof(f75,plain,(
% 4.13/1.01    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f50])).
% 4.13/1.01  
% 4.13/1.01  fof(f89,plain,(
% 4.13/1.01    v1_funct_1(sK6)),
% 4.13/1.01    inference(cnf_transformation,[],[f55])).
% 4.13/1.01  
% 4.13/1.01  fof(f76,plain,(
% 4.13/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f50])).
% 4.13/1.01  
% 4.13/1.01  fof(f96,plain,(
% 4.13/1.01    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.13/1.01    inference(equality_resolution,[],[f76])).
% 4.13/1.01  
% 4.13/1.01  fof(f93,plain,(
% 4.13/1.01    ( ! [X4] : (k1_funct_1(sK6,X4) != sK3 | ~m1_subset_1(X4,sK4)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f55])).
% 4.13/1.01  
% 4.13/1.01  fof(f2,axiom,(
% 4.13/1.01    v1_xboole_0(k1_xboole_0)),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f57,plain,(
% 4.13/1.01    v1_xboole_0(k1_xboole_0)),
% 4.13/1.01    inference(cnf_transformation,[],[f2])).
% 4.13/1.01  
% 4.13/1.01  fof(f82,plain,(
% 4.13/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 4.13/1.01    inference(cnf_transformation,[],[f52])).
% 4.13/1.01  
% 4.13/1.01  fof(f1,axiom,(
% 4.13/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 4.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.01  
% 4.13/1.01  fof(f20,plain,(
% 4.13/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 4.13/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 4.13/1.01  
% 4.13/1.01  fof(f21,plain,(
% 4.13/1.01    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 4.13/1.01    inference(ennf_transformation,[],[f20])).
% 4.13/1.01  
% 4.13/1.01  fof(f56,plain,(
% 4.13/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 4.13/1.01    inference(cnf_transformation,[],[f21])).
% 4.13/1.01  
% 4.13/1.01  cnf(c_35,negated_conjecture,
% 4.13/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 4.13/1.01      inference(cnf_transformation,[],[f91]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1506,plain,
% 4.13/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_32,plain,
% 4.13/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 4.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.13/1.01      | k1_relset_1(X1,X2,X0) = X1
% 4.13/1.01      | k1_xboole_0 = X2 ),
% 4.13/1.01      inference(cnf_transformation,[],[f83]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1509,plain,
% 4.13/1.01      ( k1_relset_1(X0,X1,X2) = X0
% 4.13/1.01      | k1_xboole_0 = X1
% 4.13/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.13/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1991,plain,
% 4.13/1.01      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 4.13/1.01      | sK5 = k1_xboole_0
% 4.13/1.01      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_1506,c_1509]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_36,negated_conjecture,
% 4.13/1.01      ( v1_funct_2(sK6,sK4,sK5) ),
% 4.13/1.01      inference(cnf_transformation,[],[f90]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1992,plain,
% 4.13/1.01      ( ~ v1_funct_2(sK6,sK4,sK5)
% 4.13/1.01      | k1_relset_1(sK4,sK5,sK6) = sK4
% 4.13/1.01      | sK5 = k1_xboole_0 ),
% 4.13/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1991]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2478,plain,
% 4.13/1.01      ( sK5 = k1_xboole_0 | k1_relset_1(sK4,sK5,sK6) = sK4 ),
% 4.13/1.01      inference(global_propositional_subsumption,
% 4.13/1.01                [status(thm)],
% 4.13/1.01                [c_1991,c_36,c_1992]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2479,plain,
% 4.13/1.01      ( k1_relset_1(sK4,sK5,sK6) = sK4 | sK5 = k1_xboole_0 ),
% 4.13/1.01      inference(renaming,[status(thm)],[c_2478]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_22,plain,
% 4.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.13/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.13/1.01      inference(cnf_transformation,[],[f78]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1519,plain,
% 4.13/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.13/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2877,plain,
% 4.13/1.01      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_1506,c_1519]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_3269,plain,
% 4.13/1.01      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_2479,c_2877]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_21,plain,
% 4.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.13/1.01      | v1_relat_1(X0) ),
% 4.13/1.01      inference(cnf_transformation,[],[f77]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1520,plain,
% 4.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.13/1.01      | v1_relat_1(X0) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2604,plain,
% 4.13/1.01      ( v1_relat_1(sK6) = iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_1506,c_1520]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_16,plain,
% 4.13/1.01      ( ~ v1_relat_1(X0)
% 4.13/1.01      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 4.13/1.01      inference(cnf_transformation,[],[f72]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1525,plain,
% 4.13/1.01      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 4.13/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2753,plain,
% 4.13/1.01      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_2604,c_1525]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_3535,plain,
% 4.13/1.01      ( k9_relat_1(sK6,sK4) = k2_relat_1(sK6) | sK5 = k1_xboole_0 ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_3269,c_2753]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_13,plain,
% 4.13/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 4.13/1.01      | r2_hidden(sK0(X0,X2,X1),X2)
% 4.13/1.01      | ~ v1_relat_1(X1) ),
% 4.13/1.01      inference(cnf_transformation,[],[f70]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1528,plain,
% 4.13/1.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 4.13/1.01      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 4.13/1.01      | v1_relat_1(X1) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_5,plain,
% 4.13/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 4.13/1.01      inference(cnf_transformation,[],[f61]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1536,plain,
% 4.13/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 4.13/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_3779,plain,
% 4.13/1.01      ( m1_subset_1(sK0(X0,X1,X2),X1) = iProver_top
% 4.13/1.01      | r2_hidden(X0,k9_relat_1(X2,X1)) != iProver_top
% 4.13/1.01      | v1_relat_1(X2) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_1528,c_1536]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_14,plain,
% 4.13/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 4.13/1.01      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 4.13/1.01      | ~ v1_relat_1(X1) ),
% 4.13/1.01      inference(cnf_transformation,[],[f69]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1527,plain,
% 4.13/1.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 4.13/1.01      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 4.13/1.01      | v1_relat_1(X1) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_23,plain,
% 4.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.13/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 4.13/1.01      inference(cnf_transformation,[],[f79]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1518,plain,
% 4.13/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 4.13/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2863,plain,
% 4.13/1.01      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_1506,c_1518]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_34,negated_conjecture,
% 4.13/1.01      ( r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) ),
% 4.13/1.01      inference(cnf_transformation,[],[f92]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1507,plain,
% 4.13/1.01      ( r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_3165,plain,
% 4.13/1.01      ( r2_hidden(sK3,k2_relat_1(sK6)) = iProver_top ),
% 4.13/1.01      inference(demodulation,[status(thm)],[c_2863,c_1507]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_26,plain,
% 4.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.13/1.01      | ~ r2_hidden(X3,X0)
% 4.13/1.01      | k4_tarski(sK1(X3,X1,X2),sK2(X3,X1,X2)) = X3 ),
% 4.13/1.01      inference(cnf_transformation,[],[f80]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1515,plain,
% 4.13/1.01      ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X0
% 4.13/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.13/1.01      | r2_hidden(X0,X3) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_5663,plain,
% 4.13/1.01      ( k4_tarski(sK1(X0,sK4,sK5),sK2(X0,sK4,sK5)) = X0
% 4.13/1.01      | r2_hidden(X0,sK6) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_1506,c_1515]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_6145,plain,
% 4.13/1.01      ( k4_tarski(sK1(k4_tarski(sK0(X0,X1,sK6),X0),sK4,sK5),sK2(k4_tarski(sK0(X0,X1,sK6),X0),sK4,sK5)) = k4_tarski(sK0(X0,X1,sK6),X0)
% 4.13/1.01      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 4.13/1.01      | v1_relat_1(sK6) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_1527,c_5663]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_40,plain,
% 4.13/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1867,plain,
% 4.13/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 4.13/1.01      | v1_relat_1(sK6) ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1868,plain,
% 4.13/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 4.13/1.01      | v1_relat_1(sK6) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_1867]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_6665,plain,
% 4.13/1.01      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 4.13/1.01      | k4_tarski(sK1(k4_tarski(sK0(X0,X1,sK6),X0),sK4,sK5),sK2(k4_tarski(sK0(X0,X1,sK6),X0),sK4,sK5)) = k4_tarski(sK0(X0,X1,sK6),X0) ),
% 4.13/1.01      inference(global_propositional_subsumption,
% 4.13/1.01                [status(thm)],
% 4.13/1.01                [c_6145,c_40,c_1868]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_6666,plain,
% 4.13/1.01      ( k4_tarski(sK1(k4_tarski(sK0(X0,X1,sK6),X0),sK4,sK5),sK2(k4_tarski(sK0(X0,X1,sK6),X0),sK4,sK5)) = k4_tarski(sK0(X0,X1,sK6),X0)
% 4.13/1.01      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 4.13/1.01      inference(renaming,[status(thm)],[c_6665]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_6675,plain,
% 4.13/1.01      ( k4_tarski(sK1(k4_tarski(sK0(X0,k1_relat_1(sK6),sK6),X0),sK4,sK5),sK2(k4_tarski(sK0(X0,k1_relat_1(sK6),sK6),X0),sK4,sK5)) = k4_tarski(sK0(X0,k1_relat_1(sK6),sK6),X0)
% 4.13/1.01      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_2753,c_6666]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_8791,plain,
% 4.13/1.01      ( k4_tarski(sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5),sK2(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)) = k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3) ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_3165,c_6675]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_19,plain,
% 4.13/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 4.13/1.01      | ~ v1_funct_1(X2)
% 4.13/1.01      | ~ v1_relat_1(X2)
% 4.13/1.01      | k1_funct_1(X2,X0) = X1 ),
% 4.13/1.01      inference(cnf_transformation,[],[f75]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1522,plain,
% 4.13/1.01      ( k1_funct_1(X0,X1) = X2
% 4.13/1.01      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 4.13/1.01      | v1_funct_1(X0) != iProver_top
% 4.13/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_8828,plain,
% 4.13/1.01      ( k1_funct_1(X0,sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)) = sK2(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)
% 4.13/1.01      | r2_hidden(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),X0) != iProver_top
% 4.13/1.01      | v1_funct_1(X0) != iProver_top
% 4.13/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_8791,c_1522]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_9510,plain,
% 4.13/1.01      ( k1_funct_1(sK6,sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)) = sK2(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)
% 4.13/1.01      | r2_hidden(sK3,k9_relat_1(sK6,k1_relat_1(sK6))) != iProver_top
% 4.13/1.01      | v1_funct_1(sK6) != iProver_top
% 4.13/1.01      | v1_relat_1(sK6) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_1527,c_8828]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_9526,plain,
% 4.13/1.01      ( k1_funct_1(sK6,sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)) = sK2(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)
% 4.13/1.01      | r2_hidden(sK3,k2_relat_1(sK6)) != iProver_top
% 4.13/1.01      | v1_funct_1(sK6) != iProver_top
% 4.13/1.01      | v1_relat_1(sK6) != iProver_top ),
% 4.13/1.01      inference(light_normalisation,[status(thm)],[c_9510,c_2753]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_37,negated_conjecture,
% 4.13/1.01      ( v1_funct_1(sK6) ),
% 4.13/1.01      inference(cnf_transformation,[],[f89]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_38,plain,
% 4.13/1.01      ( v1_funct_1(sK6) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_9536,plain,
% 4.13/1.01      ( k1_funct_1(sK6,sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)) = sK2(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5) ),
% 4.13/1.01      inference(global_propositional_subsumption,
% 4.13/1.01                [status(thm)],
% 4.13/1.01                [c_9526,c_38,c_40,c_1868,c_3165]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_18,plain,
% 4.13/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.13/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 4.13/1.01      | ~ v1_funct_1(X1)
% 4.13/1.01      | ~ v1_relat_1(X1) ),
% 4.13/1.01      inference(cnf_transformation,[],[f96]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1523,plain,
% 4.13/1.01      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 4.13/1.01      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 4.13/1.01      | v1_funct_1(X1) != iProver_top
% 4.13/1.01      | v1_relat_1(X1) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_9540,plain,
% 4.13/1.01      ( r2_hidden(sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5),k1_relat_1(sK6)) != iProver_top
% 4.13/1.01      | r2_hidden(k4_tarski(sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5),sK2(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5)),sK6) = iProver_top
% 4.13/1.01      | v1_funct_1(sK6) != iProver_top
% 4.13/1.01      | v1_relat_1(sK6) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_9536,c_1523]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_9550,plain,
% 4.13/1.01      ( r2_hidden(sK1(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK4,sK5),k1_relat_1(sK6)) != iProver_top
% 4.13/1.01      | r2_hidden(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK6) = iProver_top
% 4.13/1.01      | v1_funct_1(sK6) != iProver_top
% 4.13/1.01      | v1_relat_1(sK6) != iProver_top ),
% 4.13/1.01      inference(light_normalisation,[status(thm)],[c_9540,c_8791]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_41,plain,
% 4.13/1.01      ( r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1937,plain,
% 4.13/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 4.13/1.01      | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_23]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2025,plain,
% 4.13/1.01      ( ~ v1_relat_1(sK6)
% 4.13/1.01      | k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_678,plain,( X0 = X0 ),theory(equality) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2130,plain,
% 4.13/1.01      ( sK3 = sK3 ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_678]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_679,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2429,plain,
% 4.13/1.01      ( X0 != X1
% 4.13/1.01      | X0 = k2_relset_1(sK4,sK5,sK6)
% 4.13/1.01      | k2_relset_1(sK4,sK5,sK6) != X1 ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_679]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_3216,plain,
% 4.13/1.01      ( X0 = k2_relset_1(sK4,sK5,sK6)
% 4.13/1.01      | X0 != k2_relat_1(sK6)
% 4.13/1.01      | k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6) ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_2429]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_3389,plain,
% 4.13/1.01      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 4.13/1.01      | k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relset_1(sK4,sK5,sK6)
% 4.13/1.01      | k9_relat_1(sK6,k1_relat_1(sK6)) != k2_relat_1(sK6) ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_3216]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_680,plain,
% 4.13/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.13/1.01      theory(equality) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1940,plain,
% 4.13/1.01      ( r2_hidden(X0,X1)
% 4.13/1.01      | ~ r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6))
% 4.13/1.01      | X1 != k2_relset_1(sK4,sK5,sK6)
% 4.13/1.01      | X0 != sK3 ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_680]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_2129,plain,
% 4.13/1.01      ( r2_hidden(sK3,X0)
% 4.13/1.01      | ~ r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6))
% 4.13/1.01      | X0 != k2_relset_1(sK4,sK5,sK6)
% 4.13/1.01      | sK3 != sK3 ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_1940]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_4976,plain,
% 4.13/1.01      ( ~ r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6))
% 4.13/1.01      | r2_hidden(sK3,k9_relat_1(sK6,k1_relat_1(sK6)))
% 4.13/1.01      | k9_relat_1(sK6,k1_relat_1(sK6)) != k2_relset_1(sK4,sK5,sK6)
% 4.13/1.01      | sK3 != sK3 ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_2129]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_4977,plain,
% 4.13/1.01      ( k9_relat_1(sK6,k1_relat_1(sK6)) != k2_relset_1(sK4,sK5,sK6)
% 4.13/1.01      | sK3 != sK3
% 4.13/1.01      | r2_hidden(sK3,k2_relset_1(sK4,sK5,sK6)) != iProver_top
% 4.13/1.01      | r2_hidden(sK3,k9_relat_1(sK6,k1_relat_1(sK6))) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_4976]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_6092,plain,
% 4.13/1.01      ( r2_hidden(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK6)
% 4.13/1.01      | ~ r2_hidden(sK3,k9_relat_1(sK6,k1_relat_1(sK6)))
% 4.13/1.01      | ~ v1_relat_1(sK6) ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_6097,plain,
% 4.13/1.01      ( r2_hidden(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK6) = iProver_top
% 4.13/1.01      | r2_hidden(sK3,k9_relat_1(sK6,k1_relat_1(sK6))) != iProver_top
% 4.13/1.01      | v1_relat_1(sK6) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_6092]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_9871,plain,
% 4.13/1.01      ( r2_hidden(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK6) = iProver_top ),
% 4.13/1.01      inference(global_propositional_subsumption,
% 4.13/1.01                [status(thm)],
% 4.13/1.01                [c_9550,c_35,c_40,c_41,c_1867,c_1868,c_1937,c_2025,
% 4.13/1.01                 c_2130,c_3389,c_4977,c_6097]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_9881,plain,
% 4.13/1.01      ( k1_funct_1(sK6,sK0(sK3,k1_relat_1(sK6),sK6)) = sK3
% 4.13/1.01      | v1_funct_1(sK6) != iProver_top
% 4.13/1.01      | v1_relat_1(sK6) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_9871,c_1522]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_9444,plain,
% 4.13/1.01      ( ~ r2_hidden(k4_tarski(sK0(sK3,k1_relat_1(sK6),sK6),sK3),sK6)
% 4.13/1.01      | ~ v1_funct_1(sK6)
% 4.13/1.01      | ~ v1_relat_1(sK6)
% 4.13/1.01      | k1_funct_1(sK6,sK0(sK3,k1_relat_1(sK6),sK6)) = sK3 ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_10588,plain,
% 4.13/1.01      ( k1_funct_1(sK6,sK0(sK3,k1_relat_1(sK6),sK6)) = sK3 ),
% 4.13/1.01      inference(global_propositional_subsumption,
% 4.13/1.01                [status(thm)],
% 4.13/1.01                [c_9881,c_37,c_35,c_34,c_1867,c_1937,c_2025,c_2130,
% 4.13/1.01                 c_3389,c_4976,c_6092,c_9444]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_33,negated_conjecture,
% 4.13/1.01      ( ~ m1_subset_1(X0,sK4) | k1_funct_1(sK6,X0) != sK3 ),
% 4.13/1.01      inference(cnf_transformation,[],[f93]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1508,plain,
% 4.13/1.01      ( k1_funct_1(sK6,X0) != sK3 | m1_subset_1(X0,sK4) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_10594,plain,
% 4.13/1.01      ( m1_subset_1(sK0(sK3,k1_relat_1(sK6),sK6),sK4) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_10588,c_1508]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_10604,plain,
% 4.13/1.01      ( sK5 = k1_xboole_0
% 4.13/1.01      | m1_subset_1(sK0(sK3,sK4,sK6),sK4) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_3269,c_10594]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1,plain,
% 4.13/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 4.13/1.01      inference(cnf_transformation,[],[f57]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_134,plain,
% 4.13/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_681,plain,
% 4.13/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 4.13/1.01      theory(equality) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_4990,plain,
% 4.13/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_681]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_4991,plain,
% 4.13/1.01      ( sK5 != X0
% 4.13/1.01      | v1_xboole_0(X0) != iProver_top
% 4.13/1.01      | v1_xboole_0(sK5) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_4990]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_4993,plain,
% 4.13/1.01      ( sK5 != k1_xboole_0
% 4.13/1.01      | v1_xboole_0(sK5) = iProver_top
% 4.13/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.13/1.01      inference(instantiation,[status(thm)],[c_4991]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_24,plain,
% 4.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.13/1.01      | ~ r2_hidden(X3,X0)
% 4.13/1.01      | r2_hidden(sK2(X3,X1,X2),X2) ),
% 4.13/1.01      inference(cnf_transformation,[],[f82]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1517,plain,
% 4.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.13/1.01      | r2_hidden(X3,X0) != iProver_top
% 4.13/1.01      | r2_hidden(sK2(X3,X1,X2),X2) = iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_5009,plain,
% 4.13/1.01      ( r2_hidden(X0,sK6) != iProver_top
% 4.13/1.01      | r2_hidden(sK2(X0,sK4,sK5),sK5) = iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_1506,c_1517]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_0,plain,
% 4.13/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 4.13/1.01      inference(cnf_transformation,[],[f56]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_1540,plain,
% 4.13/1.01      ( r2_hidden(X0,X1) != iProver_top
% 4.13/1.01      | v1_xboole_0(X1) != iProver_top ),
% 4.13/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_5174,plain,
% 4.13/1.01      ( r2_hidden(X0,sK6) != iProver_top
% 4.13/1.01      | v1_xboole_0(sK5) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_5009,c_1540]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_5313,plain,
% 4.13/1.01      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 4.13/1.01      | v1_relat_1(sK6) != iProver_top
% 4.13/1.01      | v1_xboole_0(sK5) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_1527,c_5174]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_7871,plain,
% 4.13/1.01      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 4.13/1.01      | v1_xboole_0(sK5) != iProver_top ),
% 4.13/1.01      inference(global_propositional_subsumption,
% 4.13/1.01                [status(thm)],
% 4.13/1.01                [c_5313,c_40,c_1868]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_7882,plain,
% 4.13/1.01      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 4.13/1.01      | v1_xboole_0(sK5) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_2753,c_7871]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_7932,plain,
% 4.13/1.01      ( v1_xboole_0(sK5) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_3165,c_7882]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_10844,plain,
% 4.13/1.01      ( m1_subset_1(sK0(sK3,sK4,sK6),sK4) != iProver_top ),
% 4.13/1.01      inference(global_propositional_subsumption,
% 4.13/1.01                [status(thm)],
% 4.13/1.01                [c_10604,c_134,c_4993,c_7932]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_10849,plain,
% 4.13/1.01      ( r2_hidden(sK3,k9_relat_1(sK6,sK4)) != iProver_top
% 4.13/1.01      | v1_relat_1(sK6) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_3779,c_10844]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_11013,plain,
% 4.13/1.01      ( r2_hidden(sK3,k9_relat_1(sK6,sK4)) != iProver_top ),
% 4.13/1.01      inference(global_propositional_subsumption,
% 4.13/1.01                [status(thm)],
% 4.13/1.01                [c_10849,c_40,c_1868]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(c_11018,plain,
% 4.13/1.01      ( sK5 = k1_xboole_0
% 4.13/1.01      | r2_hidden(sK3,k2_relat_1(sK6)) != iProver_top ),
% 4.13/1.01      inference(superposition,[status(thm)],[c_3535,c_11013]) ).
% 4.13/1.01  
% 4.13/1.01  cnf(contradiction,plain,
% 4.13/1.01      ( $false ),
% 4.13/1.01      inference(minisat,
% 4.13/1.01                [status(thm)],
% 4.13/1.01                [c_11018,c_7932,c_4993,c_3165,c_134]) ).
% 4.13/1.01  
% 4.13/1.01  
% 4.13/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.13/1.01  
% 4.13/1.01  ------                               Statistics
% 4.13/1.01  
% 4.13/1.01  ------ Selected
% 4.13/1.01  
% 4.13/1.01  total_time:                             0.427
% 4.13/1.01  
%------------------------------------------------------------------------------

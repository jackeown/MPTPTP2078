%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:49 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  153 (2513 expanded)
%              Number of clauses        :  100 ( 848 expanded)
%              Number of leaves         :   16 ( 589 expanded)
%              Depth                    :   35
%              Number of atoms          :  476 (12460 expanded)
%              Number of equality atoms :  244 (3002 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK5
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK5,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK4,X5) != X4
              | ~ r2_hidden(X5,sK3)
              | ~ r2_hidden(X5,sK1) )
          & r2_hidden(X4,k7_relset_1(sK1,sK2,sK4,sK3)) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ! [X5] :
        ( k1_funct_1(sK4,X5) != sK5
        | ~ r2_hidden(X5,sK3)
        | ~ r2_hidden(X5,sK1) )
    & r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f25,f35,f34])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X5] :
      ( k1_funct_1(sK4,X5) != sK5
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_956,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_965,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2068,plain,
    ( k7_relset_1(sK1,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_956,c_965])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_957,plain,
    ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2370,plain,
    ( r2_hidden(sK5,k9_relat_1(sK4,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2068,c_957])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_974,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_959,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3135,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_959])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_966,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1651,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_956,c_966])).

cnf(c_3139,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3135,c_1651])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,plain,
    ( v1_funct_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3154,plain,
    ( sK2 = k1_xboole_0
    | k1_relat_1(sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3139,c_28])).

cnf(c_3155,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3154])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_972,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3158,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_972])).

cnf(c_29,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1225,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1226,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1225])).

cnf(c_3349,plain,
    ( r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3158,c_29,c_1226])).

cnf(c_3350,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_3349])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_973,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_970,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2947,plain,
    ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
    | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_973,c_970])).

cnf(c_4737,plain,
    ( k1_funct_1(sK4,sK0(sK5,sK3,sK4)) = sK5
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2370,c_2947])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5229,plain,
    ( k1_funct_1(sK4,sK0(sK5,sK3,sK4)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4737,c_27,c_29,c_1226])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,X0) != sK5 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_958,plain,
    ( k1_funct_1(sK4,X0) != sK5
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5233,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),sK1) != iProver_top
    | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5229,c_958])).

cnf(c_5251,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top
    | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3350,c_5233])).

cnf(c_5380,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5251,c_2370])).

cnf(c_5381,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5380])).

cnf(c_5386,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_974,c_5381])).

cnf(c_5389,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5386,c_29,c_1226,c_2370])).

cnf(c_5395,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5389,c_956])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_963,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5645,plain,
    ( sK1 = k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_funct_2(sK4,sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5395,c_963])).

cnf(c_315,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_342,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_1404,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_328,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1306,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | X2 != sK2
    | X1 != sK1
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_1403,plain,
    ( v1_funct_2(sK4,X0,X1)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | X1 != sK2
    | X0 != sK1
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1306])).

cnf(c_1696,plain,
    ( v1_funct_2(sK4,sK1,X0)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | X0 != sK2
    | sK1 != sK1
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_1698,plain,
    ( X0 != sK2
    | sK1 != sK1
    | sK4 != sK4
    | v1_funct_2(sK4,sK1,X0) = iProver_top
    | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1696])).

cnf(c_1700,plain,
    ( sK1 != sK1
    | sK4 != sK4
    | k1_xboole_0 != sK2
    | v1_funct_2(sK4,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK1,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_1697,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_316,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2028,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_2029,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2028])).

cnf(c_5895,plain,
    ( sK4 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5645,c_28,c_29,c_342,c_1226,c_1404,c_1700,c_1697,c_2029,c_2370,c_5386])).

cnf(c_5896,plain,
    ( sK1 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5895])).

cnf(c_5393,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_5389,c_1651])).

cnf(c_5900,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5896,c_5393])).

cnf(c_5901,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5896,c_5395])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_960,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6755,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5901,c_960])).

cnf(c_955,plain,
    ( v1_funct_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5396,plain,
    ( v1_funct_2(sK4,sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5389,c_955])).

cnf(c_5902,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5896,c_5396])).

cnf(c_7117,plain,
    ( sK4 = k1_xboole_0
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6755,c_5902])).

cnf(c_7118,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7117])).

cnf(c_7507,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5900,c_7118])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_968,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2261,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X1),sK0(X0,X2,X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_972,c_968])).

cnf(c_8009,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r1_tarski(k1_xboole_0,sK0(X0,X1,sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7507,c_2261])).

cnf(c_8397,plain,
    ( r1_tarski(k1_xboole_0,sK0(X0,X1,sK4)) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8009,c_29,c_1226])).

cnf(c_8398,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r1_tarski(k1_xboole_0,sK0(X0,X1,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8397])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_979,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8406,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8398,c_979])).

cnf(c_8413,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2370,c_8406])).

cnf(c_8435,plain,
    ( r2_hidden(sK5,k9_relat_1(k1_xboole_0,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8413,c_2370])).

cnf(c_2809,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(X1,k4_tarski(sK0(X0,X2,X1),X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_973,c_968])).

cnf(c_4290,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_979,c_2809])).

cnf(c_1,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1328,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_1])).

cnf(c_1329,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1328])).

cnf(c_1331,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1329])).

cnf(c_1441,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1442,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1441])).

cnf(c_1444,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1442])).

cnf(c_4293,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4290,c_1331,c_1444])).

cnf(c_9364,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8435,c_4293])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:25:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.87/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/0.94  
% 3.87/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/0.94  
% 3.87/0.94  ------  iProver source info
% 3.87/0.94  
% 3.87/0.94  git: date: 2020-06-30 10:37:57 +0100
% 3.87/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/0.94  git: non_committed_changes: false
% 3.87/0.94  git: last_make_outside_of_git: false
% 3.87/0.94  
% 3.87/0.94  ------ 
% 3.87/0.94  ------ Parsing...
% 3.87/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/0.94  
% 3.87/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.87/0.94  
% 3.87/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/0.94  
% 3.87/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/0.94  ------ Proving...
% 3.87/0.94  ------ Problem Properties 
% 3.87/0.94  
% 3.87/0.94  
% 3.87/0.94  clauses                                 27
% 3.87/0.94  conjectures                             5
% 3.87/0.94  EPR                                     5
% 3.87/0.94  Horn                                    23
% 3.87/0.94  unary                                   6
% 3.87/0.94  binary                                  6
% 3.87/0.94  lits                                    71
% 3.87/0.94  lits eq                                 13
% 3.87/0.94  fd_pure                                 0
% 3.87/0.94  fd_pseudo                               0
% 3.87/0.94  fd_cond                                 3
% 3.87/0.94  fd_pseudo_cond                          1
% 3.87/0.94  AC symbols                              0
% 3.87/0.94  
% 3.87/0.94  ------ Input Options Time Limit: Unbounded
% 3.87/0.94  
% 3.87/0.94  
% 3.87/0.94  ------ 
% 3.87/0.94  Current options:
% 3.87/0.94  ------ 
% 3.87/0.94  
% 3.87/0.94  
% 3.87/0.94  
% 3.87/0.94  
% 3.87/0.94  ------ Proving...
% 3.87/0.94  
% 3.87/0.94  
% 3.87/0.94  % SZS status Theorem for theBenchmark.p
% 3.87/0.94  
% 3.87/0.94   Resolution empty clause
% 3.87/0.94  
% 3.87/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/0.94  
% 3.87/0.94  fof(f12,conjecture,(
% 3.87/0.94    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.87/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.94  
% 3.87/0.94  fof(f13,negated_conjecture,(
% 3.87/0.94    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.87/0.94    inference(negated_conjecture,[],[f12])).
% 3.87/0.94  
% 3.87/0.94  fof(f24,plain,(
% 3.87/0.94    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.87/0.94    inference(ennf_transformation,[],[f13])).
% 3.87/0.94  
% 3.87/0.94  fof(f25,plain,(
% 3.87/0.94    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.87/0.94    inference(flattening,[],[f24])).
% 3.87/0.94  
% 3.87/0.94  fof(f35,plain,(
% 3.87/0.94    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK5 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK5,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.87/0.94    introduced(choice_axiom,[])).
% 3.87/0.94  
% 3.87/0.94  fof(f34,plain,(
% 3.87/0.94    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK4,X5) != X4 | ~r2_hidden(X5,sK3) | ~r2_hidden(X5,sK1)) & r2_hidden(X4,k7_relset_1(sK1,sK2,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.87/0.94    introduced(choice_axiom,[])).
% 3.87/0.94  
% 3.87/0.94  fof(f36,plain,(
% 3.87/0.94    (! [X5] : (k1_funct_1(sK4,X5) != sK5 | ~r2_hidden(X5,sK3) | ~r2_hidden(X5,sK1)) & r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.87/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f25,f35,f34])).
% 3.87/0.94  
% 3.87/0.94  fof(f61,plain,(
% 3.87/0.94    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.87/0.94    inference(cnf_transformation,[],[f36])).
% 3.87/0.94  
% 3.87/0.94  fof(f10,axiom,(
% 3.87/0.94    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.87/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.94  
% 3.87/0.94  fof(f21,plain,(
% 3.87/0.94    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.94    inference(ennf_transformation,[],[f10])).
% 3.87/0.94  
% 3.87/0.94  fof(f52,plain,(
% 3.87/0.94    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.94    inference(cnf_transformation,[],[f21])).
% 3.87/0.94  
% 3.87/0.94  fof(f62,plain,(
% 3.87/0.94    r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))),
% 3.87/0.94    inference(cnf_transformation,[],[f36])).
% 3.87/0.94  
% 3.87/0.94  fof(f5,axiom,(
% 3.87/0.94    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.87/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.94  
% 3.87/0.94  fof(f15,plain,(
% 3.87/0.94    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.87/0.94    inference(ennf_transformation,[],[f5])).
% 3.87/0.94  
% 3.87/0.94  fof(f27,plain,(
% 3.87/0.94    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.87/0.94    inference(nnf_transformation,[],[f15])).
% 3.87/0.94  
% 3.87/0.94  fof(f28,plain,(
% 3.87/0.94    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.87/0.94    inference(rectify,[],[f27])).
% 3.87/0.94  
% 3.87/0.94  fof(f29,plain,(
% 3.87/0.94    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.87/0.94    introduced(choice_axiom,[])).
% 3.87/0.94  
% 3.87/0.94  fof(f30,plain,(
% 3.87/0.94    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.87/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.87/0.94  
% 3.87/0.94  fof(f44,plain,(
% 3.87/0.94    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.87/0.94    inference(cnf_transformation,[],[f30])).
% 3.87/0.94  
% 3.87/0.94  fof(f11,axiom,(
% 3.87/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.87/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.94  
% 3.87/0.94  fof(f22,plain,(
% 3.87/0.94    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.94    inference(ennf_transformation,[],[f11])).
% 3.87/0.94  
% 3.87/0.94  fof(f23,plain,(
% 3.87/0.94    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.94    inference(flattening,[],[f22])).
% 3.87/0.94  
% 3.87/0.94  fof(f33,plain,(
% 3.87/0.94    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.94    inference(nnf_transformation,[],[f23])).
% 3.87/0.94  
% 3.87/0.94  fof(f53,plain,(
% 3.87/0.94    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.94    inference(cnf_transformation,[],[f33])).
% 3.87/0.94  
% 3.87/0.94  fof(f9,axiom,(
% 3.87/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.87/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.94  
% 3.87/0.94  fof(f20,plain,(
% 3.87/0.94    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.94    inference(ennf_transformation,[],[f9])).
% 3.87/0.94  
% 3.87/0.94  fof(f51,plain,(
% 3.87/0.94    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.94    inference(cnf_transformation,[],[f20])).
% 3.87/0.94  
% 3.87/0.94  fof(f60,plain,(
% 3.87/0.94    v1_funct_2(sK4,sK1,sK2)),
% 3.87/0.94    inference(cnf_transformation,[],[f36])).
% 3.87/0.94  
% 3.87/0.94  fof(f42,plain,(
% 3.87/0.94    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.87/0.94    inference(cnf_transformation,[],[f30])).
% 3.87/0.94  
% 3.87/0.94  fof(f8,axiom,(
% 3.87/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.87/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.94  
% 3.87/0.94  fof(f19,plain,(
% 3.87/0.94    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.94    inference(ennf_transformation,[],[f8])).
% 3.87/0.94  
% 3.87/0.94  fof(f50,plain,(
% 3.87/0.94    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.94    inference(cnf_transformation,[],[f19])).
% 3.87/0.94  
% 3.87/0.94  fof(f43,plain,(
% 3.87/0.94    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.87/0.94    inference(cnf_transformation,[],[f30])).
% 3.87/0.94  
% 3.87/0.94  fof(f6,axiom,(
% 3.87/0.94    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.87/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.94  
% 3.87/0.94  fof(f16,plain,(
% 3.87/0.94    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.87/0.94    inference(ennf_transformation,[],[f6])).
% 3.87/0.94  
% 3.87/0.94  fof(f17,plain,(
% 3.87/0.94    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.87/0.94    inference(flattening,[],[f16])).
% 3.87/0.94  
% 3.87/0.94  fof(f31,plain,(
% 3.87/0.94    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.87/0.94    inference(nnf_transformation,[],[f17])).
% 3.87/0.94  
% 3.87/0.94  fof(f32,plain,(
% 3.87/0.94    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.87/0.94    inference(flattening,[],[f31])).
% 3.87/0.94  
% 3.87/0.94  fof(f47,plain,(
% 3.87/0.94    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.87/0.94    inference(cnf_transformation,[],[f32])).
% 3.87/0.94  
% 3.87/0.94  fof(f59,plain,(
% 3.87/0.94    v1_funct_1(sK4)),
% 3.87/0.94    inference(cnf_transformation,[],[f36])).
% 3.87/0.94  
% 3.87/0.94  fof(f63,plain,(
% 3.87/0.94    ( ! [X5] : (k1_funct_1(sK4,X5) != sK5 | ~r2_hidden(X5,sK3) | ~r2_hidden(X5,sK1)) )),
% 3.87/0.94    inference(cnf_transformation,[],[f36])).
% 3.87/0.94  
% 3.87/0.94  fof(f57,plain,(
% 3.87/0.94    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.94    inference(cnf_transformation,[],[f33])).
% 3.87/0.94  
% 3.87/0.94  fof(f67,plain,(
% 3.87/0.94    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.87/0.94    inference(equality_resolution,[],[f57])).
% 3.87/0.94  
% 3.87/0.94  fof(f54,plain,(
% 3.87/0.94    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.94    inference(cnf_transformation,[],[f33])).
% 3.87/0.94  
% 3.87/0.94  fof(f69,plain,(
% 3.87/0.94    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.87/0.94    inference(equality_resolution,[],[f54])).
% 3.87/0.94  
% 3.87/0.94  fof(f7,axiom,(
% 3.87/0.94    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.87/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.94  
% 3.87/0.94  fof(f18,plain,(
% 3.87/0.94    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.87/0.94    inference(ennf_transformation,[],[f7])).
% 3.87/0.94  
% 3.87/0.94  fof(f49,plain,(
% 3.87/0.94    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.87/0.94    inference(cnf_transformation,[],[f18])).
% 3.87/0.94  
% 3.87/0.94  fof(f1,axiom,(
% 3.87/0.94    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.87/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.94  
% 3.87/0.94  fof(f37,plain,(
% 3.87/0.94    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.87/0.94    inference(cnf_transformation,[],[f1])).
% 3.87/0.94  
% 3.87/0.94  fof(f2,axiom,(
% 3.87/0.94    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.87/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.94  
% 3.87/0.94  fof(f26,plain,(
% 3.87/0.94    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.87/0.94    inference(nnf_transformation,[],[f2])).
% 3.87/0.94  
% 3.87/0.94  fof(f39,plain,(
% 3.87/0.94    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.87/0.94    inference(cnf_transformation,[],[f26])).
% 3.87/0.94  
% 3.87/0.94  cnf(c_24,negated_conjecture,
% 3.87/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.87/0.94      inference(cnf_transformation,[],[f61]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_956,plain,
% 3.87/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_15,plain,
% 3.87/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.94      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.87/0.94      inference(cnf_transformation,[],[f52]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_965,plain,
% 3.87/0.94      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.87/0.94      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_2068,plain,
% 3.87/0.94      ( k7_relset_1(sK1,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_956,c_965]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_23,negated_conjecture,
% 3.87/0.94      ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
% 3.87/0.94      inference(cnf_transformation,[],[f62]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_957,plain,
% 3.87/0.94      ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) = iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_2370,plain,
% 3.87/0.94      ( r2_hidden(sK5,k9_relat_1(sK4,sK3)) = iProver_top ),
% 3.87/0.94      inference(demodulation,[status(thm)],[c_2068,c_957]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_6,plain,
% 3.87/0.94      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.87/0.94      | r2_hidden(sK0(X0,X2,X1),X2)
% 3.87/0.94      | ~ v1_relat_1(X1) ),
% 3.87/0.94      inference(cnf_transformation,[],[f44]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_974,plain,
% 3.87/0.94      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.87/0.94      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 3.87/0.94      | v1_relat_1(X1) != iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_21,plain,
% 3.87/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.94      | k1_relset_1(X1,X2,X0) = X1
% 3.87/0.94      | k1_xboole_0 = X2 ),
% 3.87/0.94      inference(cnf_transformation,[],[f53]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_959,plain,
% 3.87/0.94      ( k1_relset_1(X0,X1,X2) = X0
% 3.87/0.94      | k1_xboole_0 = X1
% 3.87/0.94      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.87/0.94      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_3135,plain,
% 3.87/0.94      ( k1_relset_1(sK1,sK2,sK4) = sK1
% 3.87/0.94      | sK2 = k1_xboole_0
% 3.87/0.94      | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_956,c_959]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_14,plain,
% 3.87/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.94      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.87/0.94      inference(cnf_transformation,[],[f51]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_966,plain,
% 3.87/0.94      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.87/0.94      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1651,plain,
% 3.87/0.94      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_956,c_966]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_3139,plain,
% 3.87/0.94      ( k1_relat_1(sK4) = sK1
% 3.87/0.94      | sK2 = k1_xboole_0
% 3.87/0.94      | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
% 3.87/0.94      inference(demodulation,[status(thm)],[c_3135,c_1651]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_25,negated_conjecture,
% 3.87/0.94      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.87/0.94      inference(cnf_transformation,[],[f60]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_28,plain,
% 3.87/0.94      ( v1_funct_2(sK4,sK1,sK2) = iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_3154,plain,
% 3.87/0.94      ( sK2 = k1_xboole_0 | k1_relat_1(sK4) = sK1 ),
% 3.87/0.94      inference(global_propositional_subsumption,[status(thm)],[c_3139,c_28]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_3155,plain,
% 3.87/0.94      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.87/0.94      inference(renaming,[status(thm)],[c_3154]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_8,plain,
% 3.87/0.94      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.87/0.94      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 3.87/0.94      | ~ v1_relat_1(X1) ),
% 3.87/0.94      inference(cnf_transformation,[],[f42]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_972,plain,
% 3.87/0.94      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.87/0.94      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.87/0.94      | v1_relat_1(X1) != iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_3158,plain,
% 3.87/0.94      ( sK2 = k1_xboole_0
% 3.87/0.94      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.87/0.94      | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
% 3.87/0.94      | v1_relat_1(sK4) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_3155,c_972]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_29,plain,
% 3.87/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_13,plain,
% 3.87/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.87/0.94      inference(cnf_transformation,[],[f50]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1225,plain,
% 3.87/0.94      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.87/0.94      | v1_relat_1(sK4) ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_13]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1226,plain,
% 3.87/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.87/0.94      | v1_relat_1(sK4) = iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_1225]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_3349,plain,
% 3.87/0.94      ( r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
% 3.87/0.94      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.87/0.94      | sK2 = k1_xboole_0 ),
% 3.87/0.94      inference(global_propositional_subsumption,
% 3.87/0.94                [status(thm)],
% 3.87/0.94                [c_3158,c_29,c_1226]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_3350,plain,
% 3.87/0.94      ( sK2 = k1_xboole_0
% 3.87/0.94      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.87/0.94      | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top ),
% 3.87/0.94      inference(renaming,[status(thm)],[c_3349]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_7,plain,
% 3.87/0.94      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.87/0.94      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.87/0.94      | ~ v1_relat_1(X1) ),
% 3.87/0.94      inference(cnf_transformation,[],[f43]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_973,plain,
% 3.87/0.94      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.87/0.94      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.87/0.94      | v1_relat_1(X1) != iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_10,plain,
% 3.87/0.94      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.87/0.94      | ~ v1_funct_1(X2)
% 3.87/0.94      | ~ v1_relat_1(X2)
% 3.87/0.94      | k1_funct_1(X2,X0) = X1 ),
% 3.87/0.94      inference(cnf_transformation,[],[f47]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_970,plain,
% 3.87/0.94      ( k1_funct_1(X0,X1) = X2
% 3.87/0.94      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 3.87/0.94      | v1_funct_1(X0) != iProver_top
% 3.87/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_2947,plain,
% 3.87/0.94      ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
% 3.87/0.94      | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
% 3.87/0.94      | v1_funct_1(X0) != iProver_top
% 3.87/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_973,c_970]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_4737,plain,
% 3.87/0.94      ( k1_funct_1(sK4,sK0(sK5,sK3,sK4)) = sK5
% 3.87/0.94      | v1_funct_1(sK4) != iProver_top
% 3.87/0.94      | v1_relat_1(sK4) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_2370,c_2947]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_26,negated_conjecture,
% 3.87/0.94      ( v1_funct_1(sK4) ),
% 3.87/0.94      inference(cnf_transformation,[],[f59]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_27,plain,
% 3.87/0.94      ( v1_funct_1(sK4) = iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5229,plain,
% 3.87/0.94      ( k1_funct_1(sK4,sK0(sK5,sK3,sK4)) = sK5 ),
% 3.87/0.94      inference(global_propositional_subsumption,
% 3.87/0.94                [status(thm)],
% 3.87/0.94                [c_4737,c_27,c_29,c_1226]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_22,negated_conjecture,
% 3.87/0.94      ( ~ r2_hidden(X0,sK1) | ~ r2_hidden(X0,sK3) | k1_funct_1(sK4,X0) != sK5 ),
% 3.87/0.94      inference(cnf_transformation,[],[f63]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_958,plain,
% 3.87/0.94      ( k1_funct_1(sK4,X0) != sK5
% 3.87/0.94      | r2_hidden(X0,sK1) != iProver_top
% 3.87/0.94      | r2_hidden(X0,sK3) != iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5233,plain,
% 3.87/0.94      ( r2_hidden(sK0(sK5,sK3,sK4),sK1) != iProver_top
% 3.87/0.94      | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_5229,c_958]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5251,plain,
% 3.87/0.94      ( sK2 = k1_xboole_0
% 3.87/0.94      | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top
% 3.87/0.94      | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_3350,c_5233]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5380,plain,
% 3.87/0.94      ( r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top | sK2 = k1_xboole_0 ),
% 3.87/0.94      inference(global_propositional_subsumption,[status(thm)],[c_5251,c_2370]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5381,plain,
% 3.87/0.94      ( sK2 = k1_xboole_0 | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
% 3.87/0.94      inference(renaming,[status(thm)],[c_5380]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5386,plain,
% 3.87/0.94      ( sK2 = k1_xboole_0
% 3.87/0.94      | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top
% 3.87/0.94      | v1_relat_1(sK4) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_974,c_5381]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5389,plain,
% 3.87/0.94      ( sK2 = k1_xboole_0 ),
% 3.87/0.94      inference(global_propositional_subsumption,
% 3.87/0.94                [status(thm)],
% 3.87/0.94                [c_5386,c_29,c_1226,c_2370]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5395,plain,
% 3.87/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.87/0.94      inference(demodulation,[status(thm)],[c_5389,c_956]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_17,plain,
% 3.87/0.94      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.87/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.87/0.94      | k1_xboole_0 = X1
% 3.87/0.94      | k1_xboole_0 = X0 ),
% 3.87/0.94      inference(cnf_transformation,[],[f67]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_963,plain,
% 3.87/0.94      ( k1_xboole_0 = X0
% 3.87/0.94      | k1_xboole_0 = X1
% 3.87/0.94      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 3.87/0.94      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5645,plain,
% 3.87/0.94      ( sK1 = k1_xboole_0
% 3.87/0.94      | sK4 = k1_xboole_0
% 3.87/0.94      | v1_funct_2(sK4,sK1,k1_xboole_0) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_5395,c_963]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_315,plain,( X0 = X0 ),theory(equality) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_342,plain,
% 3.87/0.94      ( k1_xboole_0 = k1_xboole_0 ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_315]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1404,plain,
% 3.87/0.94      ( sK4 = sK4 ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_315]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_328,plain,
% 3.87/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/0.94      | v1_funct_2(X3,X4,X5)
% 3.87/0.94      | X3 != X0
% 3.87/0.94      | X4 != X1
% 3.87/0.94      | X5 != X2 ),
% 3.87/0.94      theory(equality) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1306,plain,
% 3.87/0.94      ( v1_funct_2(X0,X1,X2)
% 3.87/0.94      | ~ v1_funct_2(sK4,sK1,sK2)
% 3.87/0.94      | X2 != sK2
% 3.87/0.94      | X1 != sK1
% 3.87/0.94      | X0 != sK4 ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_328]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1403,plain,
% 3.87/0.94      ( v1_funct_2(sK4,X0,X1)
% 3.87/0.94      | ~ v1_funct_2(sK4,sK1,sK2)
% 3.87/0.94      | X1 != sK2
% 3.87/0.94      | X0 != sK1
% 3.87/0.94      | sK4 != sK4 ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_1306]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1696,plain,
% 3.87/0.94      ( v1_funct_2(sK4,sK1,X0)
% 3.87/0.94      | ~ v1_funct_2(sK4,sK1,sK2)
% 3.87/0.94      | X0 != sK2
% 3.87/0.94      | sK1 != sK1
% 3.87/0.94      | sK4 != sK4 ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_1403]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1698,plain,
% 3.87/0.94      ( X0 != sK2
% 3.87/0.94      | sK1 != sK1
% 3.87/0.94      | sK4 != sK4
% 3.87/0.94      | v1_funct_2(sK4,sK1,X0) = iProver_top
% 3.87/0.94      | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_1696]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1700,plain,
% 3.87/0.94      ( sK1 != sK1
% 3.87/0.94      | sK4 != sK4
% 3.87/0.94      | k1_xboole_0 != sK2
% 3.87/0.94      | v1_funct_2(sK4,sK1,sK2) != iProver_top
% 3.87/0.94      | v1_funct_2(sK4,sK1,k1_xboole_0) = iProver_top ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_1698]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1697,plain,
% 3.87/0.94      ( sK1 = sK1 ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_315]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_316,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_2028,plain,
% 3.87/0.94      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_316]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_2029,plain,
% 3.87/0.94      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_2028]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5895,plain,
% 3.87/0.94      ( sK4 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.87/0.94      inference(global_propositional_subsumption,
% 3.87/0.94                [status(thm)],
% 3.87/0.94                [c_5645,c_28,c_29,c_342,c_1226,c_1404,c_1700,c_1697,c_2029,
% 3.87/0.94                 c_2370,c_5386]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5896,plain,
% 3.87/0.94      ( sK1 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.87/0.94      inference(renaming,[status(thm)],[c_5895]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5393,plain,
% 3.87/0.94      ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 3.87/0.94      inference(demodulation,[status(thm)],[c_5389,c_1651]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5900,plain,
% 3.87/0.94      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4)
% 3.87/0.94      | sK4 = k1_xboole_0 ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_5896,c_5393]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5901,plain,
% 3.87/0.94      ( sK4 = k1_xboole_0
% 3.87/0.94      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_5896,c_5395]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_20,plain,
% 3.87/0.94      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.87/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.87/0.94      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.87/0.94      inference(cnf_transformation,[],[f69]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_960,plain,
% 3.87/0.94      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 3.87/0.94      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 3.87/0.94      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_6755,plain,
% 3.87/0.94      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 3.87/0.94      | sK4 = k1_xboole_0
% 3.87/0.94      | v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_5901,c_960]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_955,plain,
% 3.87/0.94      ( v1_funct_2(sK4,sK1,sK2) = iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5396,plain,
% 3.87/0.94      ( v1_funct_2(sK4,sK1,k1_xboole_0) = iProver_top ),
% 3.87/0.94      inference(demodulation,[status(thm)],[c_5389,c_955]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_5902,plain,
% 3.87/0.94      ( sK4 = k1_xboole_0
% 3.87/0.94      | v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_5896,c_5396]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_7117,plain,
% 3.87/0.94      ( sK4 = k1_xboole_0
% 3.87/0.94      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
% 3.87/0.94      inference(global_propositional_subsumption,[status(thm)],[c_6755,c_5902]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_7118,plain,
% 3.87/0.94      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 3.87/0.94      | sK4 = k1_xboole_0 ),
% 3.87/0.94      inference(renaming,[status(thm)],[c_7117]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_7507,plain,
% 3.87/0.94      ( k1_relat_1(sK4) = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_5900,c_7118]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_12,plain,
% 3.87/0.94      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.87/0.94      inference(cnf_transformation,[],[f49]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_968,plain,
% 3.87/0.94      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_2261,plain,
% 3.87/0.94      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.87/0.94      | r1_tarski(k1_relat_1(X1),sK0(X0,X2,X1)) != iProver_top
% 3.87/0.94      | v1_relat_1(X1) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_972,c_968]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_8009,plain,
% 3.87/0.94      ( sK4 = k1_xboole_0
% 3.87/0.94      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.87/0.94      | r1_tarski(k1_xboole_0,sK0(X0,X1,sK4)) != iProver_top
% 3.87/0.94      | v1_relat_1(sK4) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_7507,c_2261]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_8397,plain,
% 3.87/0.94      ( r1_tarski(k1_xboole_0,sK0(X0,X1,sK4)) != iProver_top
% 3.87/0.94      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.87/0.94      | sK4 = k1_xboole_0 ),
% 3.87/0.94      inference(global_propositional_subsumption,
% 3.87/0.94                [status(thm)],
% 3.87/0.94                [c_8009,c_29,c_1226]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_8398,plain,
% 3.87/0.94      ( sK4 = k1_xboole_0
% 3.87/0.94      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.87/0.94      | r1_tarski(k1_xboole_0,sK0(X0,X1,sK4)) != iProver_top ),
% 3.87/0.94      inference(renaming,[status(thm)],[c_8397]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_0,plain,
% 3.87/0.94      ( r1_tarski(k1_xboole_0,X0) ),
% 3.87/0.94      inference(cnf_transformation,[],[f37]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_979,plain,
% 3.87/0.94      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_8406,plain,
% 3.87/0.94      ( sK4 = k1_xboole_0 | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 3.87/0.94      inference(forward_subsumption_resolution,[status(thm)],[c_8398,c_979]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_8413,plain,
% 3.87/0.94      ( sK4 = k1_xboole_0 ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_2370,c_8406]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_8435,plain,
% 3.87/0.94      ( r2_hidden(sK5,k9_relat_1(k1_xboole_0,sK3)) = iProver_top ),
% 3.87/0.94      inference(demodulation,[status(thm)],[c_8413,c_2370]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_2809,plain,
% 3.87/0.94      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.87/0.94      | r1_tarski(X1,k4_tarski(sK0(X0,X2,X1),X0)) != iProver_top
% 3.87/0.94      | v1_relat_1(X1) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_973,c_968]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_4290,plain,
% 3.87/0.94      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
% 3.87/0.94      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.87/0.94      inference(superposition,[status(thm)],[c_979,c_2809]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1,plain,
% 3.87/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.87/0.94      inference(cnf_transformation,[],[f39]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1328,plain,
% 3.87/0.94      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0) ),
% 3.87/0.94      inference(resolution,[status(thm)],[c_13,c_1]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1329,plain,
% 3.87/0.94      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.87/0.94      | v1_relat_1(X0) = iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_1328]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1331,plain,
% 3.87/0.94      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.87/0.94      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_1329]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1441,plain,
% 3.87/0.94      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_0]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1442,plain,
% 3.87/0.94      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
% 3.87/0.94      inference(predicate_to_equality,[status(thm)],[c_1441]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_1444,plain,
% 3.87/0.94      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.87/0.94      inference(instantiation,[status(thm)],[c_1442]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_4293,plain,
% 3.87/0.94      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top ),
% 3.87/0.94      inference(global_propositional_subsumption,
% 3.87/0.94                [status(thm)],
% 3.87/0.94                [c_4290,c_1331,c_1444]) ).
% 3.87/0.94  
% 3.87/0.94  cnf(c_9364,plain,
% 3.87/0.94      ( $false ),
% 3.87/0.94      inference(forward_subsumption_resolution,[status(thm)],[c_8435,c_4293]) ).
% 3.87/0.94  
% 3.87/0.94  
% 3.87/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/0.94  
% 3.87/0.94  ------                               Statistics
% 3.87/0.94  
% 3.87/0.94  ------ Selected
% 3.87/0.94  
% 3.87/0.94  total_time:                             0.393
% 3.87/0.94  
%------------------------------------------------------------------------------

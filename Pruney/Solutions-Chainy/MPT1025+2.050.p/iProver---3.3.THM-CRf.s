%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:10 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  201 (24569 expanded)
%              Number of clauses        :  135 (8476 expanded)
%              Number of leaves         :   16 (5440 expanded)
%              Depth                    :   30
%              Number of atoms          :  644 (116079 expanded)
%              Number of equality atoms :  271 (22371 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f20])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK6
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK6,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK5,X5) != X4
              | ~ r2_hidden(X5,sK4)
              | ~ m1_subset_1(X5,sK2) )
          & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ! [X5] :
        ( k1_funct_1(sK5,X5) != sK6
        | ~ r2_hidden(X5,sK4)
        | ~ m1_subset_1(X5,sK2) )
    & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f23,f37,f36])).

fof(f64,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X5] :
      ( k1_funct_1(sK5,X5) != sK6
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_432,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_434,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_26])).

cnf(c_1695,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1699,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2383,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1695,c_1699])).

cnf(c_2483,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_434,c_2383])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1698,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2488,plain,
    ( k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1695,c_1698])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1696,plain,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2767,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2488,c_1696])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1701,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_359,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_360,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_1691,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_3249,plain,
    ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1701,c_1691])).

cnf(c_31,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1896,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2050,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_2051,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2050])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2103,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2104,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2103])).

cnf(c_3621,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3249,c_31,c_2051,c_2104])).

cnf(c_3622,plain,
    ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3621])).

cnf(c_3632,plain,
    ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6 ),
    inference(superposition,[status(thm)],[c_2767,c_3622])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_344,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_345,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_1692,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_182,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_1])).

cnf(c_183,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_1694,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_2283,plain,
    ( m1_subset_1(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1692,c_1694])).

cnf(c_2372,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | m1_subset_1(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2283,c_31,c_2051,c_2104])).

cnf(c_2373,plain,
    ( m1_subset_1(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2372])).

cnf(c_3661,plain,
    ( m1_subset_1(k4_tarski(sK1(sK6,sK4,sK5),sK6),sK5) = iProver_top
    | r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_2373])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4447,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5))
    | ~ r2_hidden(sK6,k9_relat_1(sK5,sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4451,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4447])).

cnf(c_4502,plain,
    ( m1_subset_1(k4_tarski(sK1(sK6,sK4,sK5),sK6),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3661,c_31,c_2051,c_2104,c_2767,c_4451])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1706,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4508,plain,
    ( r2_hidden(k4_tarski(sK1(sK6,sK4,sK5),sK6),sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4502,c_1706])).

cnf(c_3662,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK6,sK4,sK5),sK6),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_1692])).

cnf(c_4739,plain,
    ( r2_hidden(k4_tarski(sK1(sK6,sK4,sK5),sK6),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4508,c_31,c_2051,c_2104,c_2767,c_3662,c_4451])).

cnf(c_15,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_329,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_330,plain,
    ( r2_hidden(X0,k1_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_1693,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_4747,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4739,c_1693])).

cnf(c_4975,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4747,c_31,c_2051,c_2104,c_2767,c_4451])).

cnf(c_4980,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2483,c_4975])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1703,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3294,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1692,c_1703])).

cnf(c_3887,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3294,c_31,c_2051,c_2104])).

cnf(c_3888,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3887])).

cnf(c_1710,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3898,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_xboole_0(k9_relat_1(sK5,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3888,c_1710])).

cnf(c_4983,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),X0) != iProver_top
    | v1_xboole_0(k9_relat_1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4975,c_3898])).

cnf(c_5151,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(k9_relat_1(sK5,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4980,c_4983])).

cnf(c_24,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK5,X0) != sK6 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1697,plain,
    ( k1_funct_1(sK5,X0) != sK6
    | m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3663,plain,
    ( m1_subset_1(sK1(sK6,sK4,sK5),sK2) != iProver_top
    | r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_1697])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4448,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),sK4)
    | ~ r2_hidden(sK6,k9_relat_1(sK5,sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4449,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),sK4) = iProver_top
    | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4448])).

cnf(c_5072,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK1(sK6,sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4980,c_1694])).

cnf(c_5227,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5151,c_31,c_2051,c_2104,c_2767,c_3663,c_4449,c_5072])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_399,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_1690,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_5234,plain,
    ( sK2 = k1_xboole_0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5227,c_1690])).

cnf(c_5246,plain,
    ( sK2 = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5234])).

cnf(c_5237,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5227,c_1695])).

cnf(c_5250,plain,
    ( sK2 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5246,c_5237])).

cnf(c_32,plain,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_593,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != X1
    | sK3 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK5 != X0
    | sK5 = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_183,c_399])).

cnf(c_594,plain,
    ( ~ r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_595,plain,
    ( sK3 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK5 = k1_xboole_0
    | r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_1888,plain,
    ( ~ r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))
    | ~ v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1889,plain,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) != iProver_top
    | v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1888])).

cnf(c_1281,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1992,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4))
    | k7_relset_1(sK2,sK3,sK5,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_2177,plain,
    ( v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4))
    | ~ v1_xboole_0(k9_relat_1(sK5,sK4))
    | k7_relset_1(sK2,sK3,sK5,sK4) != k9_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_2179,plain,
    ( k7_relset_1(sK2,sK3,sK5,sK4) != k9_relat_1(sK5,sK4)
    | v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top
    | v1_xboole_0(k9_relat_1(sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2177])).

cnf(c_1972,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2178,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k7_relset_1(sK2,sK3,sK5,sK4) = k9_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1972])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2413,plain,
    ( r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4))
    | v1_xboole_0(k9_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2414,plain,
    ( r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4)) = iProver_top
    | v1_xboole_0(k9_relat_1(sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2413])).

cnf(c_2814,plain,
    ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5)
    | ~ r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2821,plain,
    ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5) = iProver_top
    | r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2814])).

cnf(c_3335,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_3337,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3335])).

cnf(c_3771,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3772,plain,
    ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3771])).

cnf(c_2520,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1695,c_1706])).

cnf(c_5230,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5227,c_2520])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1707,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2541,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1695,c_1707])).

cnf(c_5231,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5227,c_2541])).

cnf(c_5654,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5250,c_26,c_31,c_25,c_32,c_2,c_595,c_1888,c_1889,c_2050,c_2051,c_2103,c_2104,c_2177,c_2179,c_2178,c_2413,c_2414,c_2767,c_2814,c_2821,c_3337,c_3663,c_3771,c_3772,c_4449,c_5072,c_5230,c_5231])).

cnf(c_5233,plain,
    ( k1_relset_1(sK2,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_5227,c_2383])).

cnf(c_5659,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_5654,c_5233])).

cnf(c_5660,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5654,c_5237])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X1
    | sK2 != k1_xboole_0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_419,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_1689,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_5235,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5227,c_1689])).

cnf(c_5647,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5235,c_26,c_31,c_25,c_32,c_2,c_595,c_1888,c_1889,c_2050,c_2051,c_2103,c_2104,c_2177,c_2179,c_2178,c_2413,c_2414,c_2767,c_2814,c_2821,c_3337,c_3663,c_3771,c_3772,c_4449,c_5072,c_5230,c_5231])).

cnf(c_5735,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5660,c_5647])).

cnf(c_6112,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5659,c_5735])).

cnf(c_5190,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK5))
    | k1_relat_1(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_5192,plain,
    ( v1_xboole_0(k1_relat_1(sK5))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5190])).

cnf(c_3795,plain,
    ( ~ r2_hidden(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),k1_relat_1(sK5))
    | ~ v1_xboole_0(k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2815,plain,
    ( r2_hidden(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),k1_relat_1(sK5))
    | ~ r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6112,c_5192,c_3795,c_2815,c_2413,c_2178,c_2177,c_2103,c_2050,c_1888,c_2,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:49:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.22/1.07  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.07  
% 3.22/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/1.07  
% 3.22/1.07  ------  iProver source info
% 3.22/1.07  
% 3.22/1.07  git: date: 2020-06-30 10:37:57 +0100
% 3.22/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/1.07  git: non_committed_changes: false
% 3.22/1.07  git: last_make_outside_of_git: false
% 3.22/1.07  
% 3.22/1.07  ------ 
% 3.22/1.07  
% 3.22/1.07  ------ Input Options
% 3.22/1.07  
% 3.22/1.07  --out_options                           all
% 3.22/1.07  --tptp_safe_out                         true
% 3.22/1.07  --problem_path                          ""
% 3.22/1.07  --include_path                          ""
% 3.22/1.07  --clausifier                            res/vclausify_rel
% 3.22/1.07  --clausifier_options                    --mode clausify
% 3.22/1.07  --stdin                                 false
% 3.22/1.07  --stats_out                             all
% 3.22/1.07  
% 3.22/1.07  ------ General Options
% 3.22/1.07  
% 3.22/1.07  --fof                                   false
% 3.22/1.07  --time_out_real                         305.
% 3.22/1.07  --time_out_virtual                      -1.
% 3.22/1.07  --symbol_type_check                     false
% 3.22/1.07  --clausify_out                          false
% 3.22/1.07  --sig_cnt_out                           false
% 3.22/1.07  --trig_cnt_out                          false
% 3.22/1.07  --trig_cnt_out_tolerance                1.
% 3.22/1.07  --trig_cnt_out_sk_spl                   false
% 3.22/1.07  --abstr_cl_out                          false
% 3.22/1.07  
% 3.22/1.07  ------ Global Options
% 3.22/1.07  
% 3.22/1.07  --schedule                              default
% 3.22/1.07  --add_important_lit                     false
% 3.22/1.07  --prop_solver_per_cl                    1000
% 3.22/1.07  --min_unsat_core                        false
% 3.22/1.07  --soft_assumptions                      false
% 3.22/1.07  --soft_lemma_size                       3
% 3.22/1.07  --prop_impl_unit_size                   0
% 3.22/1.07  --prop_impl_unit                        []
% 3.22/1.07  --share_sel_clauses                     true
% 3.22/1.07  --reset_solvers                         false
% 3.22/1.07  --bc_imp_inh                            [conj_cone]
% 3.22/1.07  --conj_cone_tolerance                   3.
% 3.22/1.07  --extra_neg_conj                        none
% 3.22/1.07  --large_theory_mode                     true
% 3.22/1.07  --prolific_symb_bound                   200
% 3.22/1.07  --lt_threshold                          2000
% 3.22/1.07  --clause_weak_htbl                      true
% 3.22/1.07  --gc_record_bc_elim                     false
% 3.22/1.07  
% 3.22/1.07  ------ Preprocessing Options
% 3.22/1.07  
% 3.22/1.07  --preprocessing_flag                    true
% 3.22/1.07  --time_out_prep_mult                    0.1
% 3.22/1.07  --splitting_mode                        input
% 3.22/1.07  --splitting_grd                         true
% 3.22/1.07  --splitting_cvd                         false
% 3.22/1.07  --splitting_cvd_svl                     false
% 3.22/1.07  --splitting_nvd                         32
% 3.22/1.07  --sub_typing                            true
% 3.22/1.07  --prep_gs_sim                           true
% 3.22/1.07  --prep_unflatten                        true
% 3.22/1.07  --prep_res_sim                          true
% 3.22/1.07  --prep_upred                            true
% 3.22/1.07  --prep_sem_filter                       exhaustive
% 3.22/1.07  --prep_sem_filter_out                   false
% 3.22/1.07  --pred_elim                             true
% 3.22/1.07  --res_sim_input                         true
% 3.22/1.07  --eq_ax_congr_red                       true
% 3.22/1.07  --pure_diseq_elim                       true
% 3.22/1.07  --brand_transform                       false
% 3.22/1.07  --non_eq_to_eq                          false
% 3.22/1.07  --prep_def_merge                        true
% 3.22/1.07  --prep_def_merge_prop_impl              false
% 3.22/1.07  --prep_def_merge_mbd                    true
% 3.22/1.07  --prep_def_merge_tr_red                 false
% 3.22/1.07  --prep_def_merge_tr_cl                  false
% 3.22/1.07  --smt_preprocessing                     true
% 3.22/1.07  --smt_ac_axioms                         fast
% 3.22/1.07  --preprocessed_out                      false
% 3.22/1.07  --preprocessed_stats                    false
% 3.22/1.07  
% 3.22/1.07  ------ Abstraction refinement Options
% 3.22/1.07  
% 3.22/1.07  --abstr_ref                             []
% 3.22/1.07  --abstr_ref_prep                        false
% 3.22/1.07  --abstr_ref_until_sat                   false
% 3.22/1.07  --abstr_ref_sig_restrict                funpre
% 3.22/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/1.07  --abstr_ref_under                       []
% 3.22/1.07  
% 3.22/1.07  ------ SAT Options
% 3.22/1.07  
% 3.22/1.07  --sat_mode                              false
% 3.22/1.07  --sat_fm_restart_options                ""
% 3.22/1.07  --sat_gr_def                            false
% 3.22/1.07  --sat_epr_types                         true
% 3.22/1.07  --sat_non_cyclic_types                  false
% 3.22/1.07  --sat_finite_models                     false
% 3.22/1.07  --sat_fm_lemmas                         false
% 3.22/1.07  --sat_fm_prep                           false
% 3.22/1.07  --sat_fm_uc_incr                        true
% 3.22/1.07  --sat_out_model                         small
% 3.22/1.07  --sat_out_clauses                       false
% 3.22/1.07  
% 3.22/1.07  ------ QBF Options
% 3.22/1.07  
% 3.22/1.07  --qbf_mode                              false
% 3.22/1.07  --qbf_elim_univ                         false
% 3.22/1.07  --qbf_dom_inst                          none
% 3.22/1.07  --qbf_dom_pre_inst                      false
% 3.22/1.07  --qbf_sk_in                             false
% 3.22/1.07  --qbf_pred_elim                         true
% 3.22/1.07  --qbf_split                             512
% 3.22/1.07  
% 3.22/1.07  ------ BMC1 Options
% 3.22/1.07  
% 3.22/1.07  --bmc1_incremental                      false
% 3.22/1.07  --bmc1_axioms                           reachable_all
% 3.22/1.07  --bmc1_min_bound                        0
% 3.22/1.07  --bmc1_max_bound                        -1
% 3.22/1.07  --bmc1_max_bound_default                -1
% 3.22/1.07  --bmc1_symbol_reachability              true
% 3.22/1.07  --bmc1_property_lemmas                  false
% 3.22/1.07  --bmc1_k_induction                      false
% 3.22/1.07  --bmc1_non_equiv_states                 false
% 3.22/1.07  --bmc1_deadlock                         false
% 3.22/1.07  --bmc1_ucm                              false
% 3.22/1.07  --bmc1_add_unsat_core                   none
% 3.22/1.07  --bmc1_unsat_core_children              false
% 3.22/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/1.07  --bmc1_out_stat                         full
% 3.22/1.07  --bmc1_ground_init                      false
% 3.22/1.07  --bmc1_pre_inst_next_state              false
% 3.22/1.07  --bmc1_pre_inst_state                   false
% 3.22/1.07  --bmc1_pre_inst_reach_state             false
% 3.22/1.07  --bmc1_out_unsat_core                   false
% 3.22/1.07  --bmc1_aig_witness_out                  false
% 3.22/1.07  --bmc1_verbose                          false
% 3.22/1.07  --bmc1_dump_clauses_tptp                false
% 3.22/1.07  --bmc1_dump_unsat_core_tptp             false
% 3.22/1.07  --bmc1_dump_file                        -
% 3.22/1.07  --bmc1_ucm_expand_uc_limit              128
% 3.22/1.07  --bmc1_ucm_n_expand_iterations          6
% 3.22/1.07  --bmc1_ucm_extend_mode                  1
% 3.22/1.07  --bmc1_ucm_init_mode                    2
% 3.22/1.07  --bmc1_ucm_cone_mode                    none
% 3.22/1.07  --bmc1_ucm_reduced_relation_type        0
% 3.22/1.07  --bmc1_ucm_relax_model                  4
% 3.22/1.07  --bmc1_ucm_full_tr_after_sat            true
% 3.22/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/1.07  --bmc1_ucm_layered_model                none
% 3.22/1.07  --bmc1_ucm_max_lemma_size               10
% 3.22/1.07  
% 3.22/1.07  ------ AIG Options
% 3.22/1.07  
% 3.22/1.07  --aig_mode                              false
% 3.22/1.07  
% 3.22/1.07  ------ Instantiation Options
% 3.22/1.07  
% 3.22/1.07  --instantiation_flag                    true
% 3.22/1.07  --inst_sos_flag                         false
% 3.22/1.07  --inst_sos_phase                        true
% 3.22/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/1.07  --inst_lit_sel_side                     num_symb
% 3.22/1.07  --inst_solver_per_active                1400
% 3.22/1.07  --inst_solver_calls_frac                1.
% 3.22/1.07  --inst_passive_queue_type               priority_queues
% 3.22/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/1.07  --inst_passive_queues_freq              [25;2]
% 3.22/1.07  --inst_dismatching                      true
% 3.22/1.07  --inst_eager_unprocessed_to_passive     true
% 3.22/1.07  --inst_prop_sim_given                   true
% 3.22/1.07  --inst_prop_sim_new                     false
% 3.22/1.07  --inst_subs_new                         false
% 3.22/1.07  --inst_eq_res_simp                      false
% 3.22/1.07  --inst_subs_given                       false
% 3.22/1.07  --inst_orphan_elimination               true
% 3.22/1.07  --inst_learning_loop_flag               true
% 3.22/1.07  --inst_learning_start                   3000
% 3.22/1.07  --inst_learning_factor                  2
% 3.22/1.07  --inst_start_prop_sim_after_learn       3
% 3.22/1.07  --inst_sel_renew                        solver
% 3.22/1.07  --inst_lit_activity_flag                true
% 3.22/1.07  --inst_restr_to_given                   false
% 3.22/1.07  --inst_activity_threshold               500
% 3.22/1.07  --inst_out_proof                        true
% 3.22/1.07  
% 3.22/1.07  ------ Resolution Options
% 3.22/1.07  
% 3.22/1.07  --resolution_flag                       true
% 3.22/1.07  --res_lit_sel                           adaptive
% 3.22/1.07  --res_lit_sel_side                      none
% 3.22/1.07  --res_ordering                          kbo
% 3.22/1.07  --res_to_prop_solver                    active
% 3.22/1.07  --res_prop_simpl_new                    false
% 3.22/1.07  --res_prop_simpl_given                  true
% 3.22/1.07  --res_passive_queue_type                priority_queues
% 3.22/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/1.07  --res_passive_queues_freq               [15;5]
% 3.22/1.07  --res_forward_subs                      full
% 3.22/1.07  --res_backward_subs                     full
% 3.22/1.07  --res_forward_subs_resolution           true
% 3.22/1.07  --res_backward_subs_resolution          true
% 3.22/1.07  --res_orphan_elimination                true
% 3.22/1.07  --res_time_limit                        2.
% 3.22/1.07  --res_out_proof                         true
% 3.22/1.07  
% 3.22/1.07  ------ Superposition Options
% 3.22/1.07  
% 3.22/1.07  --superposition_flag                    true
% 3.22/1.07  --sup_passive_queue_type                priority_queues
% 3.22/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/1.07  --sup_passive_queues_freq               [8;1;4]
% 3.22/1.07  --demod_completeness_check              fast
% 3.22/1.07  --demod_use_ground                      true
% 3.22/1.07  --sup_to_prop_solver                    passive
% 3.22/1.07  --sup_prop_simpl_new                    true
% 3.22/1.07  --sup_prop_simpl_given                  true
% 3.22/1.07  --sup_fun_splitting                     false
% 3.22/1.07  --sup_smt_interval                      50000
% 3.22/1.07  
% 3.22/1.07  ------ Superposition Simplification Setup
% 3.22/1.07  
% 3.22/1.07  --sup_indices_passive                   []
% 3.22/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.07  --sup_full_bw                           [BwDemod]
% 3.22/1.07  --sup_immed_triv                        [TrivRules]
% 3.22/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.07  --sup_immed_bw_main                     []
% 3.22/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/1.07  
% 3.22/1.07  ------ Combination Options
% 3.22/1.07  
% 3.22/1.07  --comb_res_mult                         3
% 3.22/1.07  --comb_sup_mult                         2
% 3.22/1.07  --comb_inst_mult                        10
% 3.22/1.07  
% 3.22/1.07  ------ Debug Options
% 3.22/1.07  
% 3.22/1.07  --dbg_backtrace                         false
% 3.22/1.07  --dbg_dump_prop_clauses                 false
% 3.22/1.07  --dbg_dump_prop_clauses_file            -
% 3.22/1.07  --dbg_out_stat                          false
% 3.22/1.07  ------ Parsing...
% 3.22/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/1.07  
% 3.22/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.22/1.07  
% 3.22/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/1.07  
% 3.22/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.07  ------ Proving...
% 3.22/1.07  ------ Problem Properties 
% 3.22/1.07  
% 3.22/1.07  
% 3.22/1.07  clauses                                 24
% 3.22/1.07  conjectures                             3
% 3.22/1.07  EPR                                     6
% 3.22/1.07  Horn                                    20
% 3.22/1.07  unary                                   4
% 3.22/1.07  binary                                  6
% 3.22/1.07  lits                                    61
% 3.22/1.07  lits eq                                 11
% 3.22/1.07  fd_pure                                 0
% 3.22/1.07  fd_pseudo                               0
% 3.22/1.07  fd_cond                                 0
% 3.22/1.07  fd_pseudo_cond                          1
% 3.22/1.07  AC symbols                              0
% 3.22/1.07  
% 3.22/1.07  ------ Schedule dynamic 5 is on 
% 3.22/1.07  
% 3.22/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.22/1.07  
% 3.22/1.07  
% 3.22/1.07  ------ 
% 3.22/1.07  Current options:
% 3.22/1.07  ------ 
% 3.22/1.07  
% 3.22/1.07  ------ Input Options
% 3.22/1.07  
% 3.22/1.07  --out_options                           all
% 3.22/1.07  --tptp_safe_out                         true
% 3.22/1.07  --problem_path                          ""
% 3.22/1.07  --include_path                          ""
% 3.22/1.07  --clausifier                            res/vclausify_rel
% 3.22/1.07  --clausifier_options                    --mode clausify
% 3.22/1.07  --stdin                                 false
% 3.22/1.07  --stats_out                             all
% 3.22/1.07  
% 3.22/1.07  ------ General Options
% 3.22/1.07  
% 3.22/1.07  --fof                                   false
% 3.22/1.07  --time_out_real                         305.
% 3.22/1.07  --time_out_virtual                      -1.
% 3.22/1.07  --symbol_type_check                     false
% 3.22/1.07  --clausify_out                          false
% 3.22/1.07  --sig_cnt_out                           false
% 3.22/1.07  --trig_cnt_out                          false
% 3.22/1.07  --trig_cnt_out_tolerance                1.
% 3.22/1.07  --trig_cnt_out_sk_spl                   false
% 3.22/1.07  --abstr_cl_out                          false
% 3.22/1.07  
% 3.22/1.07  ------ Global Options
% 3.22/1.07  
% 3.22/1.07  --schedule                              default
% 3.22/1.07  --add_important_lit                     false
% 3.22/1.07  --prop_solver_per_cl                    1000
% 3.22/1.07  --min_unsat_core                        false
% 3.22/1.07  --soft_assumptions                      false
% 3.22/1.07  --soft_lemma_size                       3
% 3.22/1.07  --prop_impl_unit_size                   0
% 3.22/1.07  --prop_impl_unit                        []
% 3.22/1.07  --share_sel_clauses                     true
% 3.22/1.07  --reset_solvers                         false
% 3.22/1.07  --bc_imp_inh                            [conj_cone]
% 3.22/1.07  --conj_cone_tolerance                   3.
% 3.22/1.07  --extra_neg_conj                        none
% 3.22/1.07  --large_theory_mode                     true
% 3.22/1.07  --prolific_symb_bound                   200
% 3.22/1.07  --lt_threshold                          2000
% 3.22/1.07  --clause_weak_htbl                      true
% 3.22/1.07  --gc_record_bc_elim                     false
% 3.22/1.07  
% 3.22/1.07  ------ Preprocessing Options
% 3.22/1.07  
% 3.22/1.07  --preprocessing_flag                    true
% 3.22/1.07  --time_out_prep_mult                    0.1
% 3.22/1.07  --splitting_mode                        input
% 3.22/1.07  --splitting_grd                         true
% 3.22/1.07  --splitting_cvd                         false
% 3.22/1.07  --splitting_cvd_svl                     false
% 3.22/1.07  --splitting_nvd                         32
% 3.22/1.07  --sub_typing                            true
% 3.22/1.07  --prep_gs_sim                           true
% 3.22/1.07  --prep_unflatten                        true
% 3.22/1.07  --prep_res_sim                          true
% 3.22/1.07  --prep_upred                            true
% 3.22/1.07  --prep_sem_filter                       exhaustive
% 3.22/1.07  --prep_sem_filter_out                   false
% 3.22/1.07  --pred_elim                             true
% 3.22/1.07  --res_sim_input                         true
% 3.22/1.07  --eq_ax_congr_red                       true
% 3.22/1.07  --pure_diseq_elim                       true
% 3.22/1.07  --brand_transform                       false
% 3.22/1.07  --non_eq_to_eq                          false
% 3.22/1.07  --prep_def_merge                        true
% 3.22/1.07  --prep_def_merge_prop_impl              false
% 3.22/1.07  --prep_def_merge_mbd                    true
% 3.22/1.07  --prep_def_merge_tr_red                 false
% 3.22/1.07  --prep_def_merge_tr_cl                  false
% 3.22/1.07  --smt_preprocessing                     true
% 3.22/1.07  --smt_ac_axioms                         fast
% 3.22/1.07  --preprocessed_out                      false
% 3.22/1.07  --preprocessed_stats                    false
% 3.22/1.07  
% 3.22/1.07  ------ Abstraction refinement Options
% 3.22/1.07  
% 3.22/1.07  --abstr_ref                             []
% 3.22/1.07  --abstr_ref_prep                        false
% 3.22/1.07  --abstr_ref_until_sat                   false
% 3.22/1.07  --abstr_ref_sig_restrict                funpre
% 3.22/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/1.07  --abstr_ref_under                       []
% 3.22/1.07  
% 3.22/1.07  ------ SAT Options
% 3.22/1.07  
% 3.22/1.07  --sat_mode                              false
% 3.22/1.07  --sat_fm_restart_options                ""
% 3.22/1.07  --sat_gr_def                            false
% 3.22/1.07  --sat_epr_types                         true
% 3.22/1.07  --sat_non_cyclic_types                  false
% 3.22/1.07  --sat_finite_models                     false
% 3.22/1.07  --sat_fm_lemmas                         false
% 3.22/1.07  --sat_fm_prep                           false
% 3.22/1.07  --sat_fm_uc_incr                        true
% 3.22/1.07  --sat_out_model                         small
% 3.22/1.07  --sat_out_clauses                       false
% 3.22/1.07  
% 3.22/1.07  ------ QBF Options
% 3.22/1.07  
% 3.22/1.07  --qbf_mode                              false
% 3.22/1.07  --qbf_elim_univ                         false
% 3.22/1.07  --qbf_dom_inst                          none
% 3.22/1.07  --qbf_dom_pre_inst                      false
% 3.22/1.07  --qbf_sk_in                             false
% 3.22/1.07  --qbf_pred_elim                         true
% 3.22/1.07  --qbf_split                             512
% 3.22/1.07  
% 3.22/1.07  ------ BMC1 Options
% 3.22/1.07  
% 3.22/1.07  --bmc1_incremental                      false
% 3.22/1.07  --bmc1_axioms                           reachable_all
% 3.22/1.07  --bmc1_min_bound                        0
% 3.22/1.07  --bmc1_max_bound                        -1
% 3.22/1.07  --bmc1_max_bound_default                -1
% 3.22/1.07  --bmc1_symbol_reachability              true
% 3.22/1.07  --bmc1_property_lemmas                  false
% 3.22/1.07  --bmc1_k_induction                      false
% 3.22/1.07  --bmc1_non_equiv_states                 false
% 3.22/1.07  --bmc1_deadlock                         false
% 3.22/1.07  --bmc1_ucm                              false
% 3.22/1.07  --bmc1_add_unsat_core                   none
% 3.22/1.07  --bmc1_unsat_core_children              false
% 3.22/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/1.07  --bmc1_out_stat                         full
% 3.22/1.07  --bmc1_ground_init                      false
% 3.22/1.07  --bmc1_pre_inst_next_state              false
% 3.22/1.07  --bmc1_pre_inst_state                   false
% 3.22/1.07  --bmc1_pre_inst_reach_state             false
% 3.22/1.07  --bmc1_out_unsat_core                   false
% 3.22/1.07  --bmc1_aig_witness_out                  false
% 3.22/1.07  --bmc1_verbose                          false
% 3.22/1.07  --bmc1_dump_clauses_tptp                false
% 3.22/1.07  --bmc1_dump_unsat_core_tptp             false
% 3.22/1.07  --bmc1_dump_file                        -
% 3.22/1.07  --bmc1_ucm_expand_uc_limit              128
% 3.22/1.07  --bmc1_ucm_n_expand_iterations          6
% 3.22/1.07  --bmc1_ucm_extend_mode                  1
% 3.22/1.07  --bmc1_ucm_init_mode                    2
% 3.22/1.07  --bmc1_ucm_cone_mode                    none
% 3.22/1.07  --bmc1_ucm_reduced_relation_type        0
% 3.22/1.07  --bmc1_ucm_relax_model                  4
% 3.22/1.07  --bmc1_ucm_full_tr_after_sat            true
% 3.22/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/1.07  --bmc1_ucm_layered_model                none
% 3.22/1.07  --bmc1_ucm_max_lemma_size               10
% 3.22/1.07  
% 3.22/1.07  ------ AIG Options
% 3.22/1.07  
% 3.22/1.07  --aig_mode                              false
% 3.22/1.07  
% 3.22/1.07  ------ Instantiation Options
% 3.22/1.07  
% 3.22/1.07  --instantiation_flag                    true
% 3.22/1.07  --inst_sos_flag                         false
% 3.22/1.07  --inst_sos_phase                        true
% 3.22/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/1.07  --inst_lit_sel_side                     none
% 3.22/1.07  --inst_solver_per_active                1400
% 3.22/1.07  --inst_solver_calls_frac                1.
% 3.22/1.07  --inst_passive_queue_type               priority_queues
% 3.22/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/1.07  --inst_passive_queues_freq              [25;2]
% 3.22/1.07  --inst_dismatching                      true
% 3.22/1.07  --inst_eager_unprocessed_to_passive     true
% 3.22/1.07  --inst_prop_sim_given                   true
% 3.22/1.07  --inst_prop_sim_new                     false
% 3.22/1.07  --inst_subs_new                         false
% 3.22/1.07  --inst_eq_res_simp                      false
% 3.22/1.07  --inst_subs_given                       false
% 3.22/1.07  --inst_orphan_elimination               true
% 3.22/1.07  --inst_learning_loop_flag               true
% 3.22/1.07  --inst_learning_start                   3000
% 3.22/1.07  --inst_learning_factor                  2
% 3.22/1.07  --inst_start_prop_sim_after_learn       3
% 3.22/1.07  --inst_sel_renew                        solver
% 3.22/1.07  --inst_lit_activity_flag                true
% 3.22/1.07  --inst_restr_to_given                   false
% 3.22/1.07  --inst_activity_threshold               500
% 3.22/1.07  --inst_out_proof                        true
% 3.22/1.07  
% 3.22/1.07  ------ Resolution Options
% 3.22/1.07  
% 3.22/1.07  --resolution_flag                       false
% 3.22/1.07  --res_lit_sel                           adaptive
% 3.22/1.07  --res_lit_sel_side                      none
% 3.22/1.07  --res_ordering                          kbo
% 3.22/1.07  --res_to_prop_solver                    active
% 3.22/1.07  --res_prop_simpl_new                    false
% 3.22/1.07  --res_prop_simpl_given                  true
% 3.22/1.07  --res_passive_queue_type                priority_queues
% 3.22/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/1.07  --res_passive_queues_freq               [15;5]
% 3.22/1.07  --res_forward_subs                      full
% 3.22/1.07  --res_backward_subs                     full
% 3.22/1.07  --res_forward_subs_resolution           true
% 3.22/1.07  --res_backward_subs_resolution          true
% 3.22/1.07  --res_orphan_elimination                true
% 3.22/1.07  --res_time_limit                        2.
% 3.22/1.07  --res_out_proof                         true
% 3.22/1.07  
% 3.22/1.07  ------ Superposition Options
% 3.22/1.07  
% 3.22/1.07  --superposition_flag                    true
% 3.22/1.07  --sup_passive_queue_type                priority_queues
% 3.22/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/1.07  --sup_passive_queues_freq               [8;1;4]
% 3.22/1.07  --demod_completeness_check              fast
% 3.22/1.07  --demod_use_ground                      true
% 3.22/1.07  --sup_to_prop_solver                    passive
% 3.22/1.07  --sup_prop_simpl_new                    true
% 3.22/1.07  --sup_prop_simpl_given                  true
% 3.22/1.07  --sup_fun_splitting                     false
% 3.22/1.07  --sup_smt_interval                      50000
% 3.22/1.07  
% 3.22/1.07  ------ Superposition Simplification Setup
% 3.22/1.07  
% 3.22/1.07  --sup_indices_passive                   []
% 3.22/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.07  --sup_full_bw                           [BwDemod]
% 3.22/1.07  --sup_immed_triv                        [TrivRules]
% 3.22/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.07  --sup_immed_bw_main                     []
% 3.22/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/1.07  
% 3.22/1.07  ------ Combination Options
% 3.22/1.07  
% 3.22/1.07  --comb_res_mult                         3
% 3.22/1.07  --comb_sup_mult                         2
% 3.22/1.07  --comb_inst_mult                        10
% 3.22/1.07  
% 3.22/1.07  ------ Debug Options
% 3.22/1.07  
% 3.22/1.07  --dbg_backtrace                         false
% 3.22/1.07  --dbg_dump_prop_clauses                 false
% 3.22/1.07  --dbg_dump_prop_clauses_file            -
% 3.22/1.07  --dbg_out_stat                          false
% 3.22/1.07  
% 3.22/1.07  
% 3.22/1.07  
% 3.22/1.07  
% 3.22/1.07  ------ Proving...
% 3.22/1.07  
% 3.22/1.07  
% 3.22/1.07  % SZS status Theorem for theBenchmark.p
% 3.22/1.07  
% 3.22/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/1.07  
% 3.22/1.07  fof(f10,axiom,(
% 3.22/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.22/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.07  
% 3.22/1.07  fof(f20,plain,(
% 3.22/1.07    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.07    inference(ennf_transformation,[],[f10])).
% 3.22/1.07  
% 3.22/1.07  fof(f21,plain,(
% 3.22/1.07    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.07    inference(flattening,[],[f20])).
% 3.22/1.07  
% 3.22/1.07  fof(f35,plain,(
% 3.22/1.07    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.07    inference(nnf_transformation,[],[f21])).
% 3.22/1.07  
% 3.22/1.07  fof(f57,plain,(
% 3.22/1.07    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.07    inference(cnf_transformation,[],[f35])).
% 3.22/1.07  
% 3.22/1.07  fof(f11,conjecture,(
% 3.22/1.07    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.22/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.07  
% 3.22/1.07  fof(f12,negated_conjecture,(
% 3.22/1.07    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.22/1.07    inference(negated_conjecture,[],[f11])).
% 3.22/1.07  
% 3.22/1.07  fof(f22,plain,(
% 3.22/1.07    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.22/1.07    inference(ennf_transformation,[],[f12])).
% 3.22/1.07  
% 3.22/1.07  fof(f23,plain,(
% 3.22/1.07    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.22/1.07    inference(flattening,[],[f22])).
% 3.22/1.07  
% 3.22/1.07  fof(f37,plain,(
% 3.22/1.07    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK6 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK6,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.22/1.07    introduced(choice_axiom,[])).
% 3.22/1.07  
% 3.22/1.07  fof(f36,plain,(
% 3.22/1.07    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK5,X5) != X4 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 3.22/1.07    introduced(choice_axiom,[])).
% 3.22/1.07  
% 3.22/1.07  fof(f38,plain,(
% 3.22/1.07    (! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)),
% 3.22/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f23,f37,f36])).
% 3.22/1.07  
% 3.22/1.07  fof(f64,plain,(
% 3.22/1.07    v1_funct_2(sK5,sK2,sK3)),
% 3.22/1.07    inference(cnf_transformation,[],[f38])).
% 3.22/1.07  
% 3.22/1.07  fof(f65,plain,(
% 3.22/1.07    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.22/1.07    inference(cnf_transformation,[],[f38])).
% 3.22/1.07  
% 3.22/1.07  fof(f8,axiom,(
% 3.22/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.22/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.07  
% 3.22/1.07  fof(f18,plain,(
% 3.22/1.07    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.07    inference(ennf_transformation,[],[f8])).
% 3.22/1.07  
% 3.22/1.07  fof(f55,plain,(
% 3.22/1.07    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.07    inference(cnf_transformation,[],[f18])).
% 3.22/1.07  
% 3.22/1.07  fof(f9,axiom,(
% 3.22/1.07    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.22/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.07  
% 3.22/1.07  fof(f19,plain,(
% 3.22/1.07    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.07    inference(ennf_transformation,[],[f9])).
% 3.22/1.07  
% 3.22/1.07  fof(f56,plain,(
% 3.22/1.07    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.07    inference(cnf_transformation,[],[f19])).
% 3.22/1.07  
% 3.22/1.07  fof(f66,plain,(
% 3.22/1.07    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))),
% 3.22/1.07    inference(cnf_transformation,[],[f38])).
% 3.22/1.07  
% 3.22/1.07  fof(f6,axiom,(
% 3.22/1.07    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.22/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.07  
% 3.22/1.07  fof(f15,plain,(
% 3.22/1.07    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.22/1.07    inference(ennf_transformation,[],[f6])).
% 3.22/1.07  
% 3.22/1.07  fof(f29,plain,(
% 3.22/1.07    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.22/1.07    inference(nnf_transformation,[],[f15])).
% 3.22/1.07  
% 3.22/1.07  fof(f30,plain,(
% 3.22/1.07    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.22/1.07    inference(rectify,[],[f29])).
% 3.22/1.07  
% 3.22/1.07  fof(f31,plain,(
% 3.22/1.07    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.22/1.07    introduced(choice_axiom,[])).
% 3.22/1.07  
% 3.22/1.07  fof(f32,plain,(
% 3.22/1.07    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.22/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.22/1.07  
% 3.22/1.07  fof(f49,plain,(
% 3.22/1.07    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.22/1.07    inference(cnf_transformation,[],[f32])).
% 3.22/1.07  
% 3.22/1.07  fof(f7,axiom,(
% 3.22/1.07    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.22/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.07  
% 3.22/1.07  fof(f16,plain,(
% 3.22/1.07    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.22/1.07    inference(ennf_transformation,[],[f7])).
% 3.22/1.07  
% 3.22/1.07  fof(f17,plain,(
% 3.22/1.07    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.22/1.07    inference(flattening,[],[f16])).
% 3.22/1.07  
% 3.22/1.07  fof(f33,plain,(
% 3.22/1.07    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.22/1.07    inference(nnf_transformation,[],[f17])).
% 3.22/1.07  
% 3.22/1.07  fof(f34,plain,(
% 3.22/1.07    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.22/1.07    inference(flattening,[],[f33])).
% 3.22/1.07  
% 3.22/1.07  fof(f53,plain,(
% 3.22/1.07    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.22/1.07    inference(cnf_transformation,[],[f34])).
% 3.22/1.07  
% 3.22/1.07  fof(f63,plain,(
% 3.22/1.07    v1_funct_1(sK5)),
% 3.22/1.07    inference(cnf_transformation,[],[f38])).
% 3.22/1.07  
% 3.22/1.07  fof(f4,axiom,(
% 3.22/1.07    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.22/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.07  
% 3.22/1.07  fof(f14,plain,(
% 3.22/1.07    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.22/1.07    inference(ennf_transformation,[],[f4])).
% 3.22/1.07  
% 3.22/1.07  fof(f46,plain,(
% 3.22/1.07    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.22/1.07    inference(cnf_transformation,[],[f14])).
% 3.22/1.07  
% 3.22/1.07  fof(f5,axiom,(
% 3.22/1.07    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.22/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.07  
% 3.22/1.07  fof(f47,plain,(
% 3.22/1.07    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.22/1.07    inference(cnf_transformation,[],[f5])).
% 3.22/1.07  
% 3.22/1.07  fof(f54,plain,(
% 3.22/1.07    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.22/1.07    inference(cnf_transformation,[],[f34])).
% 3.22/1.07  
% 3.22/1.07  fof(f68,plain,(
% 3.22/1.07    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.22/1.07    inference(equality_resolution,[],[f54])).
% 3.22/1.07  
% 3.22/1.07  fof(f3,axiom,(
% 3.22/1.07    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.22/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.07  
% 3.22/1.07  fof(f13,plain,(
% 3.22/1.07    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.22/1.07    inference(ennf_transformation,[],[f3])).
% 3.22/1.07  
% 3.22/1.07  fof(f28,plain,(
% 3.22/1.07    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.22/1.07    inference(nnf_transformation,[],[f13])).
% 3.22/1.07  
% 3.22/1.07  fof(f43,plain,(
% 3.22/1.07    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.22/1.07    inference(cnf_transformation,[],[f28])).
% 3.22/1.07  
% 3.22/1.07  fof(f1,axiom,(
% 3.22/1.07    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.22/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.07  
% 3.22/1.07  fof(f24,plain,(
% 3.22/1.07    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.22/1.08    inference(nnf_transformation,[],[f1])).
% 3.22/1.08  
% 3.22/1.08  fof(f25,plain,(
% 3.22/1.08    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.22/1.08    inference(rectify,[],[f24])).
% 3.22/1.08  
% 3.22/1.08  fof(f26,plain,(
% 3.22/1.08    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.22/1.08    introduced(choice_axiom,[])).
% 3.22/1.08  
% 3.22/1.08  fof(f27,plain,(
% 3.22/1.08    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.22/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.22/1.08  
% 3.22/1.08  fof(f39,plain,(
% 3.22/1.08    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.22/1.08    inference(cnf_transformation,[],[f27])).
% 3.22/1.08  
% 3.22/1.08  fof(f48,plain,(
% 3.22/1.08    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.22/1.08    inference(cnf_transformation,[],[f32])).
% 3.22/1.08  
% 3.22/1.08  fof(f42,plain,(
% 3.22/1.08    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.22/1.08    inference(cnf_transformation,[],[f28])).
% 3.22/1.08  
% 3.22/1.08  fof(f52,plain,(
% 3.22/1.08    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.22/1.08    inference(cnf_transformation,[],[f34])).
% 3.22/1.08  
% 3.22/1.08  fof(f51,plain,(
% 3.22/1.08    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.22/1.08    inference(cnf_transformation,[],[f32])).
% 3.22/1.08  
% 3.22/1.08  fof(f67,plain,(
% 3.22/1.08    ( ! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) )),
% 3.22/1.08    inference(cnf_transformation,[],[f38])).
% 3.22/1.08  
% 3.22/1.08  fof(f50,plain,(
% 3.22/1.08    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.22/1.08    inference(cnf_transformation,[],[f32])).
% 3.22/1.08  
% 3.22/1.08  fof(f61,plain,(
% 3.22/1.08    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.08    inference(cnf_transformation,[],[f35])).
% 3.22/1.08  
% 3.22/1.08  fof(f71,plain,(
% 3.22/1.08    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.22/1.08    inference(equality_resolution,[],[f61])).
% 3.22/1.08  
% 3.22/1.08  fof(f2,axiom,(
% 3.22/1.08    v1_xboole_0(k1_xboole_0)),
% 3.22/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/1.08  
% 3.22/1.08  fof(f41,plain,(
% 3.22/1.08    v1_xboole_0(k1_xboole_0)),
% 3.22/1.08    inference(cnf_transformation,[],[f2])).
% 3.22/1.08  
% 3.22/1.08  fof(f40,plain,(
% 3.22/1.08    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.22/1.08    inference(cnf_transformation,[],[f27])).
% 3.22/1.08  
% 3.22/1.08  fof(f44,plain,(
% 3.22/1.08    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.22/1.08    inference(cnf_transformation,[],[f28])).
% 3.22/1.08  
% 3.22/1.08  fof(f58,plain,(
% 3.22/1.08    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.08    inference(cnf_transformation,[],[f35])).
% 3.22/1.08  
% 3.22/1.08  fof(f73,plain,(
% 3.22/1.08    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.22/1.08    inference(equality_resolution,[],[f58])).
% 3.22/1.08  
% 3.22/1.08  cnf(c_23,plain,
% 3.22/1.08      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.08      | k1_relset_1(X1,X2,X0) = X1
% 3.22/1.08      | k1_xboole_0 = X2 ),
% 3.22/1.08      inference(cnf_transformation,[],[f57]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_27,negated_conjecture,
% 3.22/1.08      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.22/1.08      inference(cnf_transformation,[],[f64]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_431,plain,
% 3.22/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.08      | k1_relset_1(X1,X2,X0) = X1
% 3.22/1.08      | sK3 != X2
% 3.22/1.08      | sK2 != X1
% 3.22/1.08      | sK5 != X0
% 3.22/1.08      | k1_xboole_0 = X2 ),
% 3.22/1.08      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_432,plain,
% 3.22/1.08      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.22/1.08      | k1_relset_1(sK2,sK3,sK5) = sK2
% 3.22/1.08      | k1_xboole_0 = sK3 ),
% 3.22/1.08      inference(unflattening,[status(thm)],[c_431]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_26,negated_conjecture,
% 3.22/1.08      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.22/1.08      inference(cnf_transformation,[],[f65]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_434,plain,
% 3.22/1.08      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 3.22/1.08      inference(global_propositional_subsumption,
% 3.22/1.08                [status(thm)],
% 3.22/1.08                [c_432,c_26]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1695,plain,
% 3.22/1.08      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_16,plain,
% 3.22/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.08      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.22/1.08      inference(cnf_transformation,[],[f55]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1699,plain,
% 3.22/1.08      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.22/1.08      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2383,plain,
% 3.22/1.08      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_1695,c_1699]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2483,plain,
% 3.22/1.08      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_434,c_2383]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_17,plain,
% 3.22/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.08      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.22/1.08      inference(cnf_transformation,[],[f56]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1698,plain,
% 3.22/1.08      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.22/1.08      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2488,plain,
% 3.22/1.08      ( k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_1695,c_1698]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_25,negated_conjecture,
% 3.22/1.08      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
% 3.22/1.08      inference(cnf_transformation,[],[f66]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1696,plain,
% 3.22/1.08      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2767,plain,
% 3.22/1.08      ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) = iProver_top ),
% 3.22/1.08      inference(demodulation,[status(thm)],[c_2488,c_1696]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_11,plain,
% 3.22/1.08      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.22/1.08      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.22/1.08      | ~ v1_relat_1(X1) ),
% 3.22/1.08      inference(cnf_transformation,[],[f49]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1701,plain,
% 3.22/1.08      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.22/1.08      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.22/1.08      | v1_relat_1(X1) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_14,plain,
% 3.22/1.08      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.22/1.08      | ~ v1_funct_1(X2)
% 3.22/1.08      | ~ v1_relat_1(X2)
% 3.22/1.08      | k1_funct_1(X2,X0) = X1 ),
% 3.22/1.08      inference(cnf_transformation,[],[f53]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_28,negated_conjecture,
% 3.22/1.08      ( v1_funct_1(sK5) ),
% 3.22/1.08      inference(cnf_transformation,[],[f63]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_359,plain,
% 3.22/1.08      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.22/1.08      | ~ v1_relat_1(X2)
% 3.22/1.08      | k1_funct_1(X2,X0) = X1
% 3.22/1.08      | sK5 != X2 ),
% 3.22/1.08      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_360,plain,
% 3.22/1.08      ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 3.22/1.08      | ~ v1_relat_1(sK5)
% 3.22/1.08      | k1_funct_1(sK5,X0) = X1 ),
% 3.22/1.08      inference(unflattening,[status(thm)],[c_359]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1691,plain,
% 3.22/1.08      ( k1_funct_1(sK5,X0) = X1
% 3.22/1.08      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.22/1.08      | v1_relat_1(sK5) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3249,plain,
% 3.22/1.08      ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
% 3.22/1.08      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.22/1.08      | v1_relat_1(sK5) != iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_1701,c_1691]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_31,plain,
% 3.22/1.08      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_7,plain,
% 3.22/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/1.08      | ~ v1_relat_1(X1)
% 3.22/1.08      | v1_relat_1(X0) ),
% 3.22/1.08      inference(cnf_transformation,[],[f46]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1896,plain,
% 3.22/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.08      | v1_relat_1(X0)
% 3.22/1.08      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_7]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2050,plain,
% 3.22/1.08      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.22/1.08      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
% 3.22/1.08      | v1_relat_1(sK5) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_1896]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2051,plain,
% 3.22/1.08      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.22/1.08      | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 3.22/1.08      | v1_relat_1(sK5) = iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_2050]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_8,plain,
% 3.22/1.08      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.22/1.08      inference(cnf_transformation,[],[f47]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2103,plain,
% 3.22/1.08      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_8]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2104,plain,
% 3.22/1.08      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_2103]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3621,plain,
% 3.22/1.08      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.22/1.08      | k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0 ),
% 3.22/1.08      inference(global_propositional_subsumption,
% 3.22/1.08                [status(thm)],
% 3.22/1.08                [c_3249,c_31,c_2051,c_2104]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3622,plain,
% 3.22/1.08      ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
% 3.22/1.08      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
% 3.22/1.08      inference(renaming,[status(thm)],[c_3621]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3632,plain,
% 3.22/1.08      ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6 ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_2767,c_3622]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_13,plain,
% 3.22/1.08      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.22/1.08      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.22/1.08      | ~ v1_funct_1(X1)
% 3.22/1.08      | ~ v1_relat_1(X1) ),
% 3.22/1.08      inference(cnf_transformation,[],[f68]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_344,plain,
% 3.22/1.08      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.22/1.08      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.22/1.08      | ~ v1_relat_1(X1)
% 3.22/1.08      | sK5 != X1 ),
% 3.22/1.08      inference(resolution_lifted,[status(thm)],[c_13,c_28]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_345,plain,
% 3.22/1.08      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 3.22/1.08      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
% 3.22/1.08      | ~ v1_relat_1(sK5) ),
% 3.22/1.08      inference(unflattening,[status(thm)],[c_344]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1692,plain,
% 3.22/1.08      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.22/1.08      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.22/1.08      | v1_relat_1(sK5) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5,plain,
% 3.22/1.08      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.22/1.08      inference(cnf_transformation,[],[f43]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1,plain,
% 3.22/1.08      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.22/1.08      inference(cnf_transformation,[],[f39]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_182,plain,
% 3.22/1.08      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.22/1.08      inference(global_propositional_subsumption,[status(thm)],[c_5,c_1]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_183,plain,
% 3.22/1.08      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.22/1.08      inference(renaming,[status(thm)],[c_182]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1694,plain,
% 3.22/1.08      ( m1_subset_1(X0,X1) = iProver_top
% 3.22/1.08      | r2_hidden(X0,X1) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2283,plain,
% 3.22/1.08      ( m1_subset_1(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.22/1.08      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.22/1.08      | v1_relat_1(sK5) != iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_1692,c_1694]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2372,plain,
% 3.22/1.08      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.22/1.08      | m1_subset_1(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top ),
% 3.22/1.08      inference(global_propositional_subsumption,
% 3.22/1.08                [status(thm)],
% 3.22/1.08                [c_2283,c_31,c_2051,c_2104]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2373,plain,
% 3.22/1.08      ( m1_subset_1(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.22/1.08      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 3.22/1.08      inference(renaming,[status(thm)],[c_2372]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3661,plain,
% 3.22/1.08      ( m1_subset_1(k4_tarski(sK1(sK6,sK4,sK5),sK6),sK5) = iProver_top
% 3.22/1.08      | r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) != iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_3632,c_2373]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_12,plain,
% 3.22/1.08      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.22/1.08      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 3.22/1.08      | ~ v1_relat_1(X1) ),
% 3.22/1.08      inference(cnf_transformation,[],[f48]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_4447,plain,
% 3.22/1.08      ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5))
% 3.22/1.08      | ~ r2_hidden(sK6,k9_relat_1(sK5,sK4))
% 3.22/1.08      | ~ v1_relat_1(sK5) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_12]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_4451,plain,
% 3.22/1.08      ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) = iProver_top
% 3.22/1.08      | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
% 3.22/1.08      | v1_relat_1(sK5) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_4447]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_4502,plain,
% 3.22/1.08      ( m1_subset_1(k4_tarski(sK1(sK6,sK4,sK5),sK6),sK5) = iProver_top ),
% 3.22/1.08      inference(global_propositional_subsumption,
% 3.22/1.08                [status(thm)],
% 3.22/1.08                [c_3661,c_31,c_2051,c_2104,c_2767,c_4451]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_6,plain,
% 3.22/1.08      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.22/1.08      inference(cnf_transformation,[],[f42]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1706,plain,
% 3.22/1.08      ( m1_subset_1(X0,X1) != iProver_top
% 3.22/1.08      | r2_hidden(X0,X1) = iProver_top
% 3.22/1.08      | v1_xboole_0(X1) = iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_4508,plain,
% 3.22/1.08      ( r2_hidden(k4_tarski(sK1(sK6,sK4,sK5),sK6),sK5) = iProver_top
% 3.22/1.08      | v1_xboole_0(sK5) = iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_4502,c_1706]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3662,plain,
% 3.22/1.08      ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) != iProver_top
% 3.22/1.08      | r2_hidden(k4_tarski(sK1(sK6,sK4,sK5),sK6),sK5) = iProver_top
% 3.22/1.08      | v1_relat_1(sK5) != iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_3632,c_1692]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_4739,plain,
% 3.22/1.08      ( r2_hidden(k4_tarski(sK1(sK6,sK4,sK5),sK6),sK5) = iProver_top ),
% 3.22/1.08      inference(global_propositional_subsumption,
% 3.22/1.08                [status(thm)],
% 3.22/1.08                [c_4508,c_31,c_2051,c_2104,c_2767,c_3662,c_4451]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_15,plain,
% 3.22/1.08      ( r2_hidden(X0,k1_relat_1(X1))
% 3.22/1.08      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.22/1.08      | ~ v1_funct_1(X1)
% 3.22/1.08      | ~ v1_relat_1(X1) ),
% 3.22/1.08      inference(cnf_transformation,[],[f52]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_329,plain,
% 3.22/1.08      ( r2_hidden(X0,k1_relat_1(X1))
% 3.22/1.08      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.22/1.08      | ~ v1_relat_1(X1)
% 3.22/1.08      | sK5 != X1 ),
% 3.22/1.08      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_330,plain,
% 3.22/1.08      ( r2_hidden(X0,k1_relat_1(sK5))
% 3.22/1.08      | ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 3.22/1.08      | ~ v1_relat_1(sK5) ),
% 3.22/1.08      inference(unflattening,[status(thm)],[c_329]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1693,plain,
% 3.22/1.08      ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
% 3.22/1.08      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.22/1.08      | v1_relat_1(sK5) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_4747,plain,
% 3.22/1.08      ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) = iProver_top
% 3.22/1.08      | v1_relat_1(sK5) != iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_4739,c_1693]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_4975,plain,
% 3.22/1.08      ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) = iProver_top ),
% 3.22/1.08      inference(global_propositional_subsumption,
% 3.22/1.08                [status(thm)],
% 3.22/1.08                [c_4747,c_31,c_2051,c_2104,c_2767,c_4451]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_4980,plain,
% 3.22/1.08      ( sK3 = k1_xboole_0
% 3.22/1.08      | r2_hidden(sK1(sK6,sK4,sK5),sK2) = iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_2483,c_4975]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_9,plain,
% 3.22/1.08      ( ~ r2_hidden(X0,X1)
% 3.22/1.08      | r2_hidden(X2,k9_relat_1(X3,X1))
% 3.22/1.08      | ~ r2_hidden(X0,k1_relat_1(X3))
% 3.22/1.08      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 3.22/1.08      | ~ v1_relat_1(X3) ),
% 3.22/1.08      inference(cnf_transformation,[],[f51]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1703,plain,
% 3.22/1.08      ( r2_hidden(X0,X1) != iProver_top
% 3.22/1.08      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 3.22/1.08      | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
% 3.22/1.08      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 3.22/1.08      | v1_relat_1(X3) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3294,plain,
% 3.22/1.08      ( r2_hidden(X0,X1) != iProver_top
% 3.22/1.08      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.22/1.08      | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1)) = iProver_top
% 3.22/1.08      | v1_relat_1(sK5) != iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_1692,c_1703]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3887,plain,
% 3.22/1.08      ( r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1)) = iProver_top
% 3.22/1.08      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.22/1.08      | r2_hidden(X0,X1) != iProver_top ),
% 3.22/1.08      inference(global_propositional_subsumption,
% 3.22/1.08                [status(thm)],
% 3.22/1.08                [c_3294,c_31,c_2051,c_2104]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3888,plain,
% 3.22/1.08      ( r2_hidden(X0,X1) != iProver_top
% 3.22/1.08      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.22/1.08      | r2_hidden(k1_funct_1(sK5,X0),k9_relat_1(sK5,X1)) = iProver_top ),
% 3.22/1.08      inference(renaming,[status(thm)],[c_3887]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1710,plain,
% 3.22/1.08      ( r2_hidden(X0,X1) != iProver_top
% 3.22/1.08      | v1_xboole_0(X1) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3898,plain,
% 3.22/1.08      ( r2_hidden(X0,X1) != iProver_top
% 3.22/1.08      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.22/1.08      | v1_xboole_0(k9_relat_1(sK5,X1)) != iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_3888,c_1710]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_4983,plain,
% 3.22/1.08      ( r2_hidden(sK1(sK6,sK4,sK5),X0) != iProver_top
% 3.22/1.08      | v1_xboole_0(k9_relat_1(sK5,X0)) != iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_4975,c_3898]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5151,plain,
% 3.22/1.08      ( sK3 = k1_xboole_0
% 3.22/1.08      | v1_xboole_0(k9_relat_1(sK5,sK2)) != iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_4980,c_4983]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_24,negated_conjecture,
% 3.22/1.08      ( ~ m1_subset_1(X0,sK2)
% 3.22/1.08      | ~ r2_hidden(X0,sK4)
% 3.22/1.08      | k1_funct_1(sK5,X0) != sK6 ),
% 3.22/1.08      inference(cnf_transformation,[],[f67]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1697,plain,
% 3.22/1.08      ( k1_funct_1(sK5,X0) != sK6
% 3.22/1.08      | m1_subset_1(X0,sK2) != iProver_top
% 3.22/1.08      | r2_hidden(X0,sK4) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3663,plain,
% 3.22/1.08      ( m1_subset_1(sK1(sK6,sK4,sK5),sK2) != iProver_top
% 3.22/1.08      | r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_3632,c_1697]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_10,plain,
% 3.22/1.08      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.22/1.08      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.22/1.08      | ~ v1_relat_1(X1) ),
% 3.22/1.08      inference(cnf_transformation,[],[f50]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_4448,plain,
% 3.22/1.08      ( r2_hidden(sK1(sK6,sK4,sK5),sK4)
% 3.22/1.08      | ~ r2_hidden(sK6,k9_relat_1(sK5,sK4))
% 3.22/1.08      | ~ v1_relat_1(sK5) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_10]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_4449,plain,
% 3.22/1.08      ( r2_hidden(sK1(sK6,sK4,sK5),sK4) = iProver_top
% 3.22/1.08      | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
% 3.22/1.08      | v1_relat_1(sK5) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_4448]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5072,plain,
% 3.22/1.08      ( sK3 = k1_xboole_0
% 3.22/1.08      | m1_subset_1(sK1(sK6,sK4,sK5),sK2) = iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_4980,c_1694]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5227,plain,
% 3.22/1.08      ( sK3 = k1_xboole_0 ),
% 3.22/1.08      inference(global_propositional_subsumption,
% 3.22/1.08                [status(thm)],
% 3.22/1.08                [c_5151,c_31,c_2051,c_2104,c_2767,c_3663,c_4449,c_5072]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_19,plain,
% 3.22/1.08      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.22/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.22/1.08      | k1_xboole_0 = X1
% 3.22/1.08      | k1_xboole_0 = X0 ),
% 3.22/1.08      inference(cnf_transformation,[],[f71]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_398,plain,
% 3.22/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.22/1.08      | sK3 != k1_xboole_0
% 3.22/1.08      | sK2 != X1
% 3.22/1.08      | sK5 != X0
% 3.22/1.08      | k1_xboole_0 = X0
% 3.22/1.08      | k1_xboole_0 = X1 ),
% 3.22/1.08      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_399,plain,
% 3.22/1.08      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.22/1.08      | sK3 != k1_xboole_0
% 3.22/1.08      | k1_xboole_0 = sK2
% 3.22/1.08      | k1_xboole_0 = sK5 ),
% 3.22/1.08      inference(unflattening,[status(thm)],[c_398]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1690,plain,
% 3.22/1.08      ( sK3 != k1_xboole_0
% 3.22/1.08      | k1_xboole_0 = sK2
% 3.22/1.08      | k1_xboole_0 = sK5
% 3.22/1.08      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5234,plain,
% 3.22/1.08      ( sK2 = k1_xboole_0
% 3.22/1.08      | sK5 = k1_xboole_0
% 3.22/1.08      | k1_xboole_0 != k1_xboole_0
% 3.22/1.08      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.22/1.08      inference(demodulation,[status(thm)],[c_5227,c_1690]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5246,plain,
% 3.22/1.08      ( sK2 = k1_xboole_0
% 3.22/1.08      | sK5 = k1_xboole_0
% 3.22/1.08      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.22/1.08      inference(equality_resolution_simp,[status(thm)],[c_5234]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5237,plain,
% 3.22/1.08      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.22/1.08      inference(demodulation,[status(thm)],[c_5227,c_1695]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5250,plain,
% 3.22/1.08      ( sK2 = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 3.22/1.08      inference(forward_subsumption_resolution,
% 3.22/1.08                [status(thm)],
% 3.22/1.08                [c_5246,c_5237]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_32,plain,
% 3.22/1.08      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2,plain,
% 3.22/1.08      ( v1_xboole_0(k1_xboole_0) ),
% 3.22/1.08      inference(cnf_transformation,[],[f41]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_593,plain,
% 3.22/1.08      ( ~ r2_hidden(X0,X1)
% 3.22/1.08      | k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != X1
% 3.22/1.08      | sK3 != k1_xboole_0
% 3.22/1.08      | sK2 = k1_xboole_0
% 3.22/1.08      | sK5 != X0
% 3.22/1.08      | sK5 = k1_xboole_0 ),
% 3.22/1.08      inference(resolution_lifted,[status(thm)],[c_183,c_399]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_594,plain,
% 3.22/1.08      ( ~ r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.22/1.08      | sK3 != k1_xboole_0
% 3.22/1.08      | sK2 = k1_xboole_0
% 3.22/1.08      | sK5 = k1_xboole_0 ),
% 3.22/1.08      inference(unflattening,[status(thm)],[c_593]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_595,plain,
% 3.22/1.08      ( sK3 != k1_xboole_0
% 3.22/1.08      | sK2 = k1_xboole_0
% 3.22/1.08      | sK5 = k1_xboole_0
% 3.22/1.08      | r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1888,plain,
% 3.22/1.08      ( ~ r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))
% 3.22/1.08      | ~ v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4)) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_1]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1889,plain,
% 3.22/1.08      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) != iProver_top
% 3.22/1.08      | v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4)) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_1888]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1281,plain,
% 3.22/1.08      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.22/1.08      theory(equality) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1992,plain,
% 3.22/1.08      ( ~ v1_xboole_0(X0)
% 3.22/1.08      | v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4))
% 3.22/1.08      | k7_relset_1(sK2,sK3,sK5,sK4) != X0 ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_1281]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2177,plain,
% 3.22/1.08      ( v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4))
% 3.22/1.08      | ~ v1_xboole_0(k9_relat_1(sK5,sK4))
% 3.22/1.08      | k7_relset_1(sK2,sK3,sK5,sK4) != k9_relat_1(sK5,sK4) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_1992]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2179,plain,
% 3.22/1.08      ( k7_relset_1(sK2,sK3,sK5,sK4) != k9_relat_1(sK5,sK4)
% 3.22/1.08      | v1_xboole_0(k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top
% 3.22/1.08      | v1_xboole_0(k9_relat_1(sK5,sK4)) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_2177]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1972,plain,
% 3.22/1.08      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.22/1.08      | k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_17]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2178,plain,
% 3.22/1.08      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.22/1.08      | k7_relset_1(sK2,sK3,sK5,sK4) = k9_relat_1(sK5,sK4) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_1972]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_0,plain,
% 3.22/1.08      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.22/1.08      inference(cnf_transformation,[],[f40]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2413,plain,
% 3.22/1.08      ( r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4))
% 3.22/1.08      | v1_xboole_0(k9_relat_1(sK5,sK4)) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_0]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2414,plain,
% 3.22/1.08      ( r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4)) = iProver_top
% 3.22/1.08      | v1_xboole_0(k9_relat_1(sK5,sK4)) = iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_2413]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2814,plain,
% 3.22/1.08      ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5)
% 3.22/1.08      | ~ r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4))
% 3.22/1.08      | ~ v1_relat_1(sK5) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_11]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2821,plain,
% 3.22/1.08      ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5) = iProver_top
% 3.22/1.08      | r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4)) != iProver_top
% 3.22/1.08      | v1_relat_1(sK5) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_2814]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3335,plain,
% 3.22/1.08      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_1281]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3337,plain,
% 3.22/1.08      ( v1_xboole_0(sK5)
% 3.22/1.08      | ~ v1_xboole_0(k1_xboole_0)
% 3.22/1.08      | sK5 != k1_xboole_0 ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_3335]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3771,plain,
% 3.22/1.08      ( ~ r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5)
% 3.22/1.08      | ~ v1_xboole_0(sK5) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_1]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3772,plain,
% 3.22/1.08      ( r2_hidden(k4_tarski(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),sK0(k9_relat_1(sK5,sK4))),sK5) != iProver_top
% 3.22/1.08      | v1_xboole_0(sK5) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_3771]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2520,plain,
% 3.22/1.08      ( r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
% 3.22/1.08      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_1695,c_1706]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5230,plain,
% 3.22/1.08      ( r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top
% 3.22/1.08      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.22/1.08      inference(demodulation,[status(thm)],[c_5227,c_2520]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_4,plain,
% 3.22/1.08      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.22/1.08      inference(cnf_transformation,[],[f44]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1707,plain,
% 3.22/1.08      ( m1_subset_1(X0,X1) != iProver_top
% 3.22/1.08      | v1_xboole_0(X1) != iProver_top
% 3.22/1.08      | v1_xboole_0(X0) = iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2541,plain,
% 3.22/1.08      ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.22/1.08      | v1_xboole_0(sK5) = iProver_top ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_1695,c_1707]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5231,plain,
% 3.22/1.08      ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.22/1.08      | v1_xboole_0(sK5) = iProver_top ),
% 3.22/1.08      inference(demodulation,[status(thm)],[c_5227,c_2541]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5654,plain,
% 3.22/1.08      ( sK2 = k1_xboole_0 ),
% 3.22/1.08      inference(global_propositional_subsumption,
% 3.22/1.08                [status(thm)],
% 3.22/1.08                [c_5250,c_26,c_31,c_25,c_32,c_2,c_595,c_1888,c_1889,
% 3.22/1.08                 c_2050,c_2051,c_2103,c_2104,c_2177,c_2179,c_2178,c_2413,
% 3.22/1.08                 c_2414,c_2767,c_2814,c_2821,c_3337,c_3663,c_3771,c_3772,
% 3.22/1.08                 c_4449,c_5072,c_5230,c_5231]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5233,plain,
% 3.22/1.08      ( k1_relset_1(sK2,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
% 3.22/1.08      inference(demodulation,[status(thm)],[c_5227,c_2383]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5659,plain,
% 3.22/1.08      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
% 3.22/1.08      inference(demodulation,[status(thm)],[c_5654,c_5233]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5660,plain,
% 3.22/1.08      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.22/1.08      inference(demodulation,[status(thm)],[c_5654,c_5237]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_22,plain,
% 3.22/1.08      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.22/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.22/1.08      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.22/1.08      inference(cnf_transformation,[],[f73]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_418,plain,
% 3.22/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.22/1.08      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.22/1.08      | sK3 != X1
% 3.22/1.08      | sK2 != k1_xboole_0
% 3.22/1.08      | sK5 != X0 ),
% 3.22/1.08      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_419,plain,
% 3.22/1.08      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.22/1.08      | k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
% 3.22/1.08      | sK2 != k1_xboole_0 ),
% 3.22/1.08      inference(unflattening,[status(thm)],[c_418]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_1689,plain,
% 3.22/1.08      ( k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
% 3.22/1.08      | sK2 != k1_xboole_0
% 3.22/1.08      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.22/1.08      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5235,plain,
% 3.22/1.08      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 3.22/1.08      | sK2 != k1_xboole_0
% 3.22/1.08      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.22/1.08      inference(demodulation,[status(thm)],[c_5227,c_1689]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5647,plain,
% 3.22/1.08      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 3.22/1.08      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.22/1.08      inference(global_propositional_subsumption,
% 3.22/1.08                [status(thm)],
% 3.22/1.08                [c_5235,c_26,c_31,c_25,c_32,c_2,c_595,c_1888,c_1889,
% 3.22/1.08                 c_2050,c_2051,c_2103,c_2104,c_2177,c_2179,c_2178,c_2413,
% 3.22/1.08                 c_2414,c_2767,c_2814,c_2821,c_3337,c_3663,c_3771,c_3772,
% 3.22/1.08                 c_4449,c_5072,c_5230,c_5231]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5735,plain,
% 3.22/1.08      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
% 3.22/1.08      inference(superposition,[status(thm)],[c_5660,c_5647]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_6112,plain,
% 3.22/1.08      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 3.22/1.08      inference(light_normalisation,[status(thm)],[c_5659,c_5735]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5190,plain,
% 3.22/1.08      ( ~ v1_xboole_0(X0)
% 3.22/1.08      | v1_xboole_0(k1_relat_1(sK5))
% 3.22/1.08      | k1_relat_1(sK5) != X0 ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_1281]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_5192,plain,
% 3.22/1.08      ( v1_xboole_0(k1_relat_1(sK5))
% 3.22/1.08      | ~ v1_xboole_0(k1_xboole_0)
% 3.22/1.08      | k1_relat_1(sK5) != k1_xboole_0 ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_5190]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_3795,plain,
% 3.22/1.08      ( ~ r2_hidden(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),k1_relat_1(sK5))
% 3.22/1.08      | ~ v1_xboole_0(k1_relat_1(sK5)) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_1]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(c_2815,plain,
% 3.22/1.08      ( r2_hidden(sK1(sK0(k9_relat_1(sK5,sK4)),sK4,sK5),k1_relat_1(sK5))
% 3.22/1.08      | ~ r2_hidden(sK0(k9_relat_1(sK5,sK4)),k9_relat_1(sK5,sK4))
% 3.22/1.08      | ~ v1_relat_1(sK5) ),
% 3.22/1.08      inference(instantiation,[status(thm)],[c_12]) ).
% 3.22/1.08  
% 3.22/1.08  cnf(contradiction,plain,
% 3.22/1.08      ( $false ),
% 3.22/1.08      inference(minisat,
% 3.22/1.08                [status(thm)],
% 3.22/1.08                [c_6112,c_5192,c_3795,c_2815,c_2413,c_2178,c_2177,c_2103,
% 3.22/1.08                 c_2050,c_1888,c_2,c_25,c_26]) ).
% 3.22/1.08  
% 3.22/1.08  
% 3.22/1.08  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/1.08  
% 3.22/1.08  ------                               Statistics
% 3.22/1.08  
% 3.22/1.08  ------ General
% 3.22/1.08  
% 3.22/1.08  abstr_ref_over_cycles:                  0
% 3.22/1.08  abstr_ref_under_cycles:                 0
% 3.22/1.08  gc_basic_clause_elim:                   0
% 3.22/1.08  forced_gc_time:                         0
% 3.22/1.08  parsing_time:                           0.025
% 3.22/1.08  unif_index_cands_time:                  0.
% 3.22/1.08  unif_index_add_time:                    0.
% 3.22/1.08  orderings_time:                         0.
% 3.22/1.08  out_proof_time:                         0.012
% 3.22/1.08  total_time:                             0.188
% 3.22/1.08  num_of_symbols:                         53
% 3.22/1.08  num_of_terms:                           4355
% 3.22/1.08  
% 3.22/1.08  ------ Preprocessing
% 3.22/1.08  
% 3.22/1.08  num_of_splits:                          0
% 3.22/1.08  num_of_split_atoms:                     0
% 3.22/1.08  num_of_reused_defs:                     0
% 3.22/1.08  num_eq_ax_congr_red:                    24
% 3.22/1.08  num_of_sem_filtered_clauses:            1
% 3.22/1.08  num_of_subtypes:                        0
% 3.22/1.08  monotx_restored_types:                  0
% 3.22/1.08  sat_num_of_epr_types:                   0
% 3.22/1.08  sat_num_of_non_cyclic_types:            0
% 3.22/1.08  sat_guarded_non_collapsed_types:        0
% 3.22/1.08  num_pure_diseq_elim:                    0
% 3.22/1.08  simp_replaced_by:                       0
% 3.22/1.08  res_preprocessed:                       128
% 3.22/1.08  prep_upred:                             0
% 3.22/1.08  prep_unflattend:                        94
% 3.22/1.08  smt_new_axioms:                         0
% 3.22/1.08  pred_elim_cands:                        4
% 3.22/1.08  pred_elim:                              2
% 3.22/1.08  pred_elim_cl:                           5
% 3.22/1.08  pred_elim_cycles:                       4
% 3.22/1.08  merged_defs:                            0
% 3.22/1.08  merged_defs_ncl:                        0
% 3.22/1.08  bin_hyper_res:                          0
% 3.22/1.08  prep_cycles:                            4
% 3.22/1.08  pred_elim_time:                         0.015
% 3.22/1.08  splitting_time:                         0.
% 3.22/1.08  sem_filter_time:                        0.
% 3.22/1.08  monotx_time:                            0.
% 3.22/1.08  subtype_inf_time:                       0.
% 3.22/1.08  
% 3.22/1.08  ------ Problem properties
% 3.22/1.08  
% 3.22/1.08  clauses:                                24
% 3.22/1.08  conjectures:                            3
% 3.22/1.08  epr:                                    6
% 3.22/1.08  horn:                                   20
% 3.22/1.08  ground:                                 6
% 3.22/1.08  unary:                                  4
% 3.22/1.08  binary:                                 6
% 3.22/1.08  lits:                                   61
% 3.22/1.08  lits_eq:                                11
% 3.22/1.08  fd_pure:                                0
% 3.22/1.08  fd_pseudo:                              0
% 3.22/1.08  fd_cond:                                0
% 3.22/1.08  fd_pseudo_cond:                         1
% 3.22/1.08  ac_symbols:                             0
% 3.22/1.08  
% 3.22/1.08  ------ Propositional Solver
% 3.22/1.08  
% 3.22/1.08  prop_solver_calls:                      29
% 3.22/1.08  prop_fast_solver_calls:                 1087
% 3.22/1.08  smt_solver_calls:                       0
% 3.22/1.08  smt_fast_solver_calls:                  0
% 3.22/1.08  prop_num_of_clauses:                    1984
% 3.22/1.08  prop_preprocess_simplified:             5899
% 3.22/1.08  prop_fo_subsumed:                       32
% 3.22/1.08  prop_solver_time:                       0.
% 3.22/1.08  smt_solver_time:                        0.
% 3.22/1.08  smt_fast_solver_time:                   0.
% 3.22/1.08  prop_fast_solver_time:                  0.
% 3.22/1.08  prop_unsat_core_time:                   0.
% 3.22/1.08  
% 3.22/1.08  ------ QBF
% 3.22/1.08  
% 3.22/1.08  qbf_q_res:                              0
% 3.22/1.08  qbf_num_tautologies:                    0
% 3.22/1.08  qbf_prep_cycles:                        0
% 3.22/1.08  
% 3.22/1.08  ------ BMC1
% 3.22/1.08  
% 3.22/1.08  bmc1_current_bound:                     -1
% 3.22/1.08  bmc1_last_solved_bound:                 -1
% 3.22/1.08  bmc1_unsat_core_size:                   -1
% 3.22/1.08  bmc1_unsat_core_parents_size:           -1
% 3.22/1.08  bmc1_merge_next_fun:                    0
% 3.22/1.08  bmc1_unsat_core_clauses_time:           0.
% 3.22/1.08  
% 3.22/1.08  ------ Instantiation
% 3.22/1.08  
% 3.22/1.08  inst_num_of_clauses:                    557
% 3.22/1.08  inst_num_in_passive:                    133
% 3.22/1.08  inst_num_in_active:                     339
% 3.22/1.08  inst_num_in_unprocessed:                85
% 3.22/1.08  inst_num_of_loops:                      450
% 3.22/1.08  inst_num_of_learning_restarts:          0
% 3.22/1.08  inst_num_moves_active_passive:          107
% 3.22/1.08  inst_lit_activity:                      0
% 3.22/1.08  inst_lit_activity_moves:                0
% 3.22/1.08  inst_num_tautologies:                   0
% 3.22/1.08  inst_num_prop_implied:                  0
% 3.22/1.08  inst_num_existing_simplified:           0
% 3.22/1.08  inst_num_eq_res_simplified:             0
% 3.22/1.08  inst_num_child_elim:                    0
% 3.22/1.08  inst_num_of_dismatching_blockings:      93
% 3.22/1.08  inst_num_of_non_proper_insts:           556
% 3.22/1.08  inst_num_of_duplicates:                 0
% 3.22/1.08  inst_inst_num_from_inst_to_res:         0
% 3.22/1.08  inst_dismatching_checking_time:         0.
% 3.22/1.08  
% 3.22/1.08  ------ Resolution
% 3.22/1.08  
% 3.22/1.08  res_num_of_clauses:                     0
% 3.22/1.08  res_num_in_passive:                     0
% 3.22/1.08  res_num_in_active:                      0
% 3.22/1.08  res_num_of_loops:                       132
% 3.22/1.08  res_forward_subset_subsumed:            37
% 3.22/1.08  res_backward_subset_subsumed:           0
% 3.22/1.08  res_forward_subsumed:                   0
% 3.22/1.08  res_backward_subsumed:                  0
% 3.22/1.08  res_forward_subsumption_resolution:     0
% 3.22/1.08  res_backward_subsumption_resolution:    0
% 3.22/1.08  res_clause_to_clause_subsumption:       295
% 3.22/1.08  res_orphan_elimination:                 0
% 3.22/1.08  res_tautology_del:                      80
% 3.22/1.08  res_num_eq_res_simplified:              0
% 3.22/1.08  res_num_sel_changes:                    0
% 3.22/1.08  res_moves_from_active_to_pass:          0
% 3.22/1.08  
% 3.22/1.08  ------ Superposition
% 3.22/1.08  
% 3.22/1.08  sup_time_total:                         0.
% 3.22/1.08  sup_time_generating:                    0.
% 3.22/1.08  sup_time_sim_full:                      0.
% 3.22/1.08  sup_time_sim_immed:                     0.
% 3.22/1.08  
% 3.22/1.08  sup_num_of_clauses:                     89
% 3.22/1.08  sup_num_in_active:                      62
% 3.22/1.08  sup_num_in_passive:                     27
% 3.22/1.08  sup_num_of_loops:                       89
% 3.22/1.08  sup_fw_superposition:                   76
% 3.22/1.08  sup_bw_superposition:                   92
% 3.22/1.08  sup_immediate_simplified:               40
% 3.22/1.08  sup_given_eliminated:                   1
% 3.22/1.08  comparisons_done:                       0
% 3.22/1.08  comparisons_avoided:                    3
% 3.22/1.08  
% 3.22/1.08  ------ Simplifications
% 3.22/1.08  
% 3.22/1.08  
% 3.22/1.08  sim_fw_subset_subsumed:                 27
% 3.22/1.08  sim_bw_subset_subsumed:                 12
% 3.22/1.08  sim_fw_subsumed:                        12
% 3.22/1.08  sim_bw_subsumed:                        2
% 3.22/1.08  sim_fw_subsumption_res:                 1
% 3.22/1.08  sim_bw_subsumption_res:                 0
% 3.22/1.08  sim_tautology_del:                      8
% 3.22/1.08  sim_eq_tautology_del:                   3
% 3.22/1.08  sim_eq_res_simp:                        1
% 3.22/1.08  sim_fw_demodulated:                     0
% 3.22/1.08  sim_bw_demodulated:                     19
% 3.22/1.08  sim_light_normalised:                   2
% 3.22/1.08  sim_joinable_taut:                      0
% 3.22/1.08  sim_joinable_simp:                      0
% 3.22/1.08  sim_ac_normalised:                      0
% 3.22/1.08  sim_smt_subsumption:                    0
% 3.22/1.08  
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:08:10 EST 2020

% Result     : Theorem 7.13s
% Output     : CNFRefutation 7.13s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 447 expanded)
%              Number of clauses        :   68 ( 160 expanded)
%              Number of leaves         :   16 (  94 expanded)
%              Depth                    :   18
%              Number of atoms          :  408 (1830 expanded)
%              Number of equality atoms :  121 ( 374 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f40,plain,(
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

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK5,X5) != X4
              | ~ r2_hidden(X5,sK4)
              | ~ m1_subset_1(X5,sK2) )
          & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ! [X5] :
        ( k1_funct_1(sK5,X5) != sK6
        | ~ r2_hidden(X5,sK4)
        | ~ m1_subset_1(X5,sK2) )
    & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f26,f40,f39])).

fof(f65,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    ! [X5] :
      ( k1_funct_1(sK5,X5) != sK6
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1517,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1515,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1526,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2938,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X3) = iProver_top
    | r1_tarski(k1_relat_1(X1),X3) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_1526])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1523,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11376,plain,
    ( m1_subset_1(sK1(X0,X1,X2),X3) = iProver_top
    | r2_hidden(X0,k9_relat_1(X2,X1)) != iProver_top
    | r1_tarski(k1_relat_1(X2),X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_xboole_0(X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2938,c_1523])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1519,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1509,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1520,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1790,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1520])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_205,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_206,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_205])).

cnf(c_257,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_206])).

cnf(c_1507,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_257])).

cnf(c_3916,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_1507])).

cnf(c_4142,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_3916])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1512,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2156,plain,
    ( k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1509,c_1512])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1510,plain,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2545,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2156,c_1510])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1516,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_17,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_380,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_381,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_1504,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_2999,plain,
    ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_1504])).

cnf(c_3123,plain,
    ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2999])).

cnf(c_4219,plain,
    ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6 ),
    inference(superposition,[status(thm)],[c_4142,c_3123])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK5,X0) != sK6 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1511,plain,
    ( k1_funct_1(sK5,X0) != sK6
    | m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4225,plain,
    ( m1_subset_1(sK1(sK6,sK4,sK5),sK2) != iProver_top
    | r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4219,c_1511])).

cnf(c_26572,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top
    | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
    | r1_tarski(k1_relat_1(sK5),sK2) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_11376,c_4225])).

cnf(c_27,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1665,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1839,plain,
    ( ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(sK2))
    | r1_tarski(k1_relat_1(X0),sK2) ),
    inference(instantiation,[status(thm)],[c_1665])).

cnf(c_1845,plain,
    ( m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1839])).

cnf(c_1847,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(sK5),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1845])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1513,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1989,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1509,c_1513])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1514,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2830,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1989,c_1514])).

cnf(c_3109,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2830,c_27])).

cnf(c_3115,plain,
    ( r1_tarski(k1_relat_1(sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3109,c_1520])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_256,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_206])).

cnf(c_1508,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_2940,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X1),X3) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_1508])).

cnf(c_9763,plain,
    ( r1_tarski(k1_relat_1(sK5),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2940])).

cnf(c_9858,plain,
    ( r1_tarski(k1_relat_1(sK5),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9763,c_4142])).

cnf(c_9862,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3115,c_9858])).

cnf(c_26923,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26572,c_27,c_1847,c_2545,c_2830,c_4142,c_9862])).

cnf(c_26927,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_26923])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26927,c_4142,c_2545])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.07  % Command    : iproveropt_run.sh %d %s
% 0.06/0.25  % Computer   : n020.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 09:37:22 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  % Running in FOF mode
% 7.13/1.33  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.13/1.33  
% 7.13/1.33  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.13/1.33  
% 7.13/1.33  ------  iProver source info
% 7.13/1.33  
% 7.13/1.33  git: date: 2020-06-30 10:37:57 +0100
% 7.13/1.33  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.13/1.33  git: non_committed_changes: false
% 7.13/1.33  git: last_make_outside_of_git: false
% 7.13/1.33  
% 7.13/1.33  ------ 
% 7.13/1.33  
% 7.13/1.33  ------ Input Options
% 7.13/1.33  
% 7.13/1.33  --out_options                           all
% 7.13/1.33  --tptp_safe_out                         true
% 7.13/1.33  --problem_path                          ""
% 7.13/1.33  --include_path                          ""
% 7.13/1.33  --clausifier                            res/vclausify_rel
% 7.13/1.33  --clausifier_options                    ""
% 7.13/1.33  --stdin                                 false
% 7.13/1.33  --stats_out                             all
% 7.13/1.33  
% 7.13/1.33  ------ General Options
% 7.13/1.33  
% 7.13/1.33  --fof                                   false
% 7.13/1.33  --time_out_real                         305.
% 7.13/1.33  --time_out_virtual                      -1.
% 7.13/1.33  --symbol_type_check                     false
% 7.13/1.33  --clausify_out                          false
% 7.13/1.33  --sig_cnt_out                           false
% 7.13/1.33  --trig_cnt_out                          false
% 7.13/1.33  --trig_cnt_out_tolerance                1.
% 7.13/1.33  --trig_cnt_out_sk_spl                   false
% 7.13/1.33  --abstr_cl_out                          false
% 7.13/1.33  
% 7.13/1.33  ------ Global Options
% 7.13/1.33  
% 7.13/1.33  --schedule                              default
% 7.13/1.33  --add_important_lit                     false
% 7.13/1.33  --prop_solver_per_cl                    1000
% 7.13/1.33  --min_unsat_core                        false
% 7.13/1.33  --soft_assumptions                      false
% 7.13/1.33  --soft_lemma_size                       3
% 7.13/1.33  --prop_impl_unit_size                   0
% 7.13/1.33  --prop_impl_unit                        []
% 7.13/1.33  --share_sel_clauses                     true
% 7.13/1.33  --reset_solvers                         false
% 7.13/1.33  --bc_imp_inh                            [conj_cone]
% 7.13/1.33  --conj_cone_tolerance                   3.
% 7.13/1.33  --extra_neg_conj                        none
% 7.13/1.33  --large_theory_mode                     true
% 7.13/1.33  --prolific_symb_bound                   200
% 7.13/1.33  --lt_threshold                          2000
% 7.13/1.33  --clause_weak_htbl                      true
% 7.13/1.33  --gc_record_bc_elim                     false
% 7.13/1.33  
% 7.13/1.33  ------ Preprocessing Options
% 7.13/1.33  
% 7.13/1.33  --preprocessing_flag                    true
% 7.13/1.33  --time_out_prep_mult                    0.1
% 7.13/1.33  --splitting_mode                        input
% 7.13/1.33  --splitting_grd                         true
% 7.13/1.33  --splitting_cvd                         false
% 7.13/1.33  --splitting_cvd_svl                     false
% 7.13/1.33  --splitting_nvd                         32
% 7.13/1.33  --sub_typing                            true
% 7.13/1.33  --prep_gs_sim                           true
% 7.13/1.33  --prep_unflatten                        true
% 7.13/1.33  --prep_res_sim                          true
% 7.13/1.33  --prep_upred                            true
% 7.13/1.33  --prep_sem_filter                       exhaustive
% 7.13/1.33  --prep_sem_filter_out                   false
% 7.13/1.33  --pred_elim                             true
% 7.13/1.33  --res_sim_input                         true
% 7.13/1.33  --eq_ax_congr_red                       true
% 7.13/1.33  --pure_diseq_elim                       true
% 7.13/1.33  --brand_transform                       false
% 7.13/1.33  --non_eq_to_eq                          false
% 7.13/1.33  --prep_def_merge                        true
% 7.13/1.33  --prep_def_merge_prop_impl              false
% 7.13/1.33  --prep_def_merge_mbd                    true
% 7.13/1.33  --prep_def_merge_tr_red                 false
% 7.13/1.33  --prep_def_merge_tr_cl                  false
% 7.13/1.33  --smt_preprocessing                     true
% 7.13/1.33  --smt_ac_axioms                         fast
% 7.13/1.33  --preprocessed_out                      false
% 7.13/1.33  --preprocessed_stats                    false
% 7.13/1.33  
% 7.13/1.33  ------ Abstraction refinement Options
% 7.13/1.33  
% 7.13/1.33  --abstr_ref                             []
% 7.13/1.33  --abstr_ref_prep                        false
% 7.13/1.33  --abstr_ref_until_sat                   false
% 7.13/1.33  --abstr_ref_sig_restrict                funpre
% 7.13/1.33  --abstr_ref_af_restrict_to_split_sk     false
% 7.13/1.33  --abstr_ref_under                       []
% 7.13/1.33  
% 7.13/1.33  ------ SAT Options
% 7.13/1.33  
% 7.13/1.33  --sat_mode                              false
% 7.13/1.33  --sat_fm_restart_options                ""
% 7.13/1.33  --sat_gr_def                            false
% 7.13/1.33  --sat_epr_types                         true
% 7.13/1.33  --sat_non_cyclic_types                  false
% 7.13/1.33  --sat_finite_models                     false
% 7.13/1.33  --sat_fm_lemmas                         false
% 7.13/1.33  --sat_fm_prep                           false
% 7.13/1.33  --sat_fm_uc_incr                        true
% 7.13/1.33  --sat_out_model                         small
% 7.13/1.33  --sat_out_clauses                       false
% 7.13/1.33  
% 7.13/1.33  ------ QBF Options
% 7.13/1.33  
% 7.13/1.33  --qbf_mode                              false
% 7.13/1.33  --qbf_elim_univ                         false
% 7.13/1.33  --qbf_dom_inst                          none
% 7.13/1.33  --qbf_dom_pre_inst                      false
% 7.13/1.33  --qbf_sk_in                             false
% 7.13/1.33  --qbf_pred_elim                         true
% 7.13/1.33  --qbf_split                             512
% 7.13/1.33  
% 7.13/1.33  ------ BMC1 Options
% 7.13/1.33  
% 7.13/1.33  --bmc1_incremental                      false
% 7.13/1.33  --bmc1_axioms                           reachable_all
% 7.13/1.33  --bmc1_min_bound                        0
% 7.13/1.33  --bmc1_max_bound                        -1
% 7.13/1.33  --bmc1_max_bound_default                -1
% 7.13/1.33  --bmc1_symbol_reachability              true
% 7.13/1.33  --bmc1_property_lemmas                  false
% 7.13/1.33  --bmc1_k_induction                      false
% 7.13/1.33  --bmc1_non_equiv_states                 false
% 7.13/1.33  --bmc1_deadlock                         false
% 7.13/1.33  --bmc1_ucm                              false
% 7.13/1.33  --bmc1_add_unsat_core                   none
% 7.13/1.33  --bmc1_unsat_core_children              false
% 7.13/1.33  --bmc1_unsat_core_extrapolate_axioms    false
% 7.13/1.33  --bmc1_out_stat                         full
% 7.13/1.33  --bmc1_ground_init                      false
% 7.13/1.33  --bmc1_pre_inst_next_state              false
% 7.13/1.33  --bmc1_pre_inst_state                   false
% 7.13/1.33  --bmc1_pre_inst_reach_state             false
% 7.13/1.33  --bmc1_out_unsat_core                   false
% 7.13/1.33  --bmc1_aig_witness_out                  false
% 7.13/1.33  --bmc1_verbose                          false
% 7.13/1.33  --bmc1_dump_clauses_tptp                false
% 7.13/1.33  --bmc1_dump_unsat_core_tptp             false
% 7.13/1.33  --bmc1_dump_file                        -
% 7.13/1.33  --bmc1_ucm_expand_uc_limit              128
% 7.13/1.33  --bmc1_ucm_n_expand_iterations          6
% 7.13/1.33  --bmc1_ucm_extend_mode                  1
% 7.13/1.33  --bmc1_ucm_init_mode                    2
% 7.13/1.33  --bmc1_ucm_cone_mode                    none
% 7.13/1.33  --bmc1_ucm_reduced_relation_type        0
% 7.13/1.33  --bmc1_ucm_relax_model                  4
% 7.13/1.33  --bmc1_ucm_full_tr_after_sat            true
% 7.13/1.33  --bmc1_ucm_expand_neg_assumptions       false
% 7.13/1.33  --bmc1_ucm_layered_model                none
% 7.13/1.33  --bmc1_ucm_max_lemma_size               10
% 7.13/1.33  
% 7.13/1.33  ------ AIG Options
% 7.13/1.33  
% 7.13/1.33  --aig_mode                              false
% 7.13/1.33  
% 7.13/1.33  ------ Instantiation Options
% 7.13/1.33  
% 7.13/1.33  --instantiation_flag                    true
% 7.13/1.33  --inst_sos_flag                         true
% 7.13/1.33  --inst_sos_phase                        true
% 7.13/1.33  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.13/1.33  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.13/1.33  --inst_lit_sel_side                     num_symb
% 7.13/1.33  --inst_solver_per_active                1400
% 7.13/1.33  --inst_solver_calls_frac                1.
% 7.13/1.33  --inst_passive_queue_type               priority_queues
% 7.13/1.33  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.13/1.33  --inst_passive_queues_freq              [25;2]
% 7.13/1.33  --inst_dismatching                      true
% 7.13/1.33  --inst_eager_unprocessed_to_passive     true
% 7.13/1.33  --inst_prop_sim_given                   true
% 7.13/1.33  --inst_prop_sim_new                     false
% 7.13/1.33  --inst_subs_new                         false
% 7.13/1.33  --inst_eq_res_simp                      false
% 7.13/1.33  --inst_subs_given                       false
% 7.13/1.33  --inst_orphan_elimination               true
% 7.13/1.33  --inst_learning_loop_flag               true
% 7.13/1.33  --inst_learning_start                   3000
% 7.13/1.33  --inst_learning_factor                  2
% 7.13/1.33  --inst_start_prop_sim_after_learn       3
% 7.13/1.33  --inst_sel_renew                        solver
% 7.13/1.33  --inst_lit_activity_flag                true
% 7.13/1.33  --inst_restr_to_given                   false
% 7.13/1.33  --inst_activity_threshold               500
% 7.13/1.33  --inst_out_proof                        true
% 7.13/1.33  
% 7.13/1.33  ------ Resolution Options
% 7.13/1.33  
% 7.13/1.33  --resolution_flag                       true
% 7.13/1.33  --res_lit_sel                           adaptive
% 7.13/1.33  --res_lit_sel_side                      none
% 7.13/1.33  --res_ordering                          kbo
% 7.13/1.33  --res_to_prop_solver                    active
% 7.13/1.33  --res_prop_simpl_new                    false
% 7.13/1.33  --res_prop_simpl_given                  true
% 7.13/1.33  --res_passive_queue_type                priority_queues
% 7.13/1.33  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.13/1.33  --res_passive_queues_freq               [15;5]
% 7.13/1.33  --res_forward_subs                      full
% 7.13/1.33  --res_backward_subs                     full
% 7.13/1.33  --res_forward_subs_resolution           true
% 7.13/1.33  --res_backward_subs_resolution          true
% 7.13/1.33  --res_orphan_elimination                true
% 7.13/1.33  --res_time_limit                        2.
% 7.13/1.33  --res_out_proof                         true
% 7.13/1.33  
% 7.13/1.33  ------ Superposition Options
% 7.13/1.33  
% 7.13/1.33  --superposition_flag                    true
% 7.13/1.33  --sup_passive_queue_type                priority_queues
% 7.13/1.33  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.13/1.33  --sup_passive_queues_freq               [8;1;4]
% 7.13/1.33  --demod_completeness_check              fast
% 7.13/1.33  --demod_use_ground                      true
% 7.13/1.33  --sup_to_prop_solver                    passive
% 7.13/1.33  --sup_prop_simpl_new                    true
% 7.13/1.33  --sup_prop_simpl_given                  true
% 7.13/1.33  --sup_fun_splitting                     true
% 7.13/1.33  --sup_smt_interval                      50000
% 7.13/1.33  
% 7.13/1.33  ------ Superposition Simplification Setup
% 7.13/1.33  
% 7.13/1.33  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.13/1.33  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.13/1.33  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.13/1.33  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.13/1.33  --sup_full_triv                         [TrivRules;PropSubs]
% 7.13/1.33  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.13/1.33  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.13/1.33  --sup_immed_triv                        [TrivRules]
% 7.13/1.33  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.13/1.33  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.13/1.33  --sup_immed_bw_main                     []
% 7.13/1.33  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.13/1.33  --sup_input_triv                        [Unflattening;TrivRules]
% 7.13/1.33  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.13/1.33  --sup_input_bw                          []
% 7.13/1.33  
% 7.13/1.33  ------ Combination Options
% 7.13/1.33  
% 7.13/1.33  --comb_res_mult                         3
% 7.13/1.33  --comb_sup_mult                         2
% 7.13/1.33  --comb_inst_mult                        10
% 7.13/1.33  
% 7.13/1.33  ------ Debug Options
% 7.13/1.33  
% 7.13/1.33  --dbg_backtrace                         false
% 7.13/1.33  --dbg_dump_prop_clauses                 false
% 7.13/1.33  --dbg_dump_prop_clauses_file            -
% 7.13/1.33  --dbg_out_stat                          false
% 7.13/1.33  ------ Parsing...
% 7.13/1.33  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.13/1.33  
% 7.13/1.33  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.13/1.33  
% 7.13/1.33  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.13/1.33  
% 7.13/1.33  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.13/1.33  ------ Proving...
% 7.13/1.33  ------ Problem Properties 
% 7.13/1.33  
% 7.13/1.33  
% 7.13/1.33  clauses                                 25
% 7.13/1.33  conjectures                             3
% 7.13/1.33  EPR                                     7
% 7.13/1.33  Horn                                    22
% 7.13/1.33  unary                                   3
% 7.13/1.33  binary                                  7
% 7.13/1.33  lits                                    64
% 7.13/1.33  lits eq                                 4
% 7.13/1.33  fd_pure                                 0
% 7.13/1.33  fd_pseudo                               0
% 7.13/1.33  fd_cond                                 0
% 7.13/1.33  fd_pseudo_cond                          1
% 7.13/1.33  AC symbols                              0
% 7.13/1.33  
% 7.13/1.33  ------ Schedule dynamic 5 is on 
% 7.13/1.33  
% 7.13/1.33  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.13/1.33  
% 7.13/1.33  
% 7.13/1.33  ------ 
% 7.13/1.33  Current options:
% 7.13/1.33  ------ 
% 7.13/1.33  
% 7.13/1.33  ------ Input Options
% 7.13/1.33  
% 7.13/1.33  --out_options                           all
% 7.13/1.33  --tptp_safe_out                         true
% 7.13/1.33  --problem_path                          ""
% 7.13/1.33  --include_path                          ""
% 7.13/1.33  --clausifier                            res/vclausify_rel
% 7.13/1.33  --clausifier_options                    ""
% 7.13/1.33  --stdin                                 false
% 7.13/1.33  --stats_out                             all
% 7.13/1.33  
% 7.13/1.33  ------ General Options
% 7.13/1.33  
% 7.13/1.33  --fof                                   false
% 7.13/1.33  --time_out_real                         305.
% 7.13/1.33  --time_out_virtual                      -1.
% 7.13/1.33  --symbol_type_check                     false
% 7.13/1.33  --clausify_out                          false
% 7.13/1.33  --sig_cnt_out                           false
% 7.13/1.33  --trig_cnt_out                          false
% 7.13/1.33  --trig_cnt_out_tolerance                1.
% 7.13/1.33  --trig_cnt_out_sk_spl                   false
% 7.13/1.33  --abstr_cl_out                          false
% 7.13/1.33  
% 7.13/1.33  ------ Global Options
% 7.13/1.33  
% 7.13/1.33  --schedule                              default
% 7.13/1.33  --add_important_lit                     false
% 7.13/1.33  --prop_solver_per_cl                    1000
% 7.13/1.33  --min_unsat_core                        false
% 7.13/1.33  --soft_assumptions                      false
% 7.13/1.33  --soft_lemma_size                       3
% 7.13/1.33  --prop_impl_unit_size                   0
% 7.13/1.33  --prop_impl_unit                        []
% 7.13/1.33  --share_sel_clauses                     true
% 7.13/1.33  --reset_solvers                         false
% 7.13/1.33  --bc_imp_inh                            [conj_cone]
% 7.13/1.33  --conj_cone_tolerance                   3.
% 7.13/1.33  --extra_neg_conj                        none
% 7.13/1.33  --large_theory_mode                     true
% 7.13/1.33  --prolific_symb_bound                   200
% 7.13/1.33  --lt_threshold                          2000
% 7.13/1.33  --clause_weak_htbl                      true
% 7.13/1.33  --gc_record_bc_elim                     false
% 7.13/1.33  
% 7.13/1.33  ------ Preprocessing Options
% 7.13/1.33  
% 7.13/1.33  --preprocessing_flag                    true
% 7.13/1.33  --time_out_prep_mult                    0.1
% 7.13/1.33  --splitting_mode                        input
% 7.13/1.33  --splitting_grd                         true
% 7.13/1.33  --splitting_cvd                         false
% 7.13/1.33  --splitting_cvd_svl                     false
% 7.13/1.33  --splitting_nvd                         32
% 7.13/1.33  --sub_typing                            true
% 7.13/1.33  --prep_gs_sim                           true
% 7.13/1.33  --prep_unflatten                        true
% 7.13/1.33  --prep_res_sim                          true
% 7.13/1.33  --prep_upred                            true
% 7.13/1.33  --prep_sem_filter                       exhaustive
% 7.13/1.33  --prep_sem_filter_out                   false
% 7.13/1.33  --pred_elim                             true
% 7.13/1.33  --res_sim_input                         true
% 7.13/1.33  --eq_ax_congr_red                       true
% 7.13/1.33  --pure_diseq_elim                       true
% 7.13/1.33  --brand_transform                       false
% 7.13/1.33  --non_eq_to_eq                          false
% 7.13/1.33  --prep_def_merge                        true
% 7.13/1.33  --prep_def_merge_prop_impl              false
% 7.13/1.33  --prep_def_merge_mbd                    true
% 7.13/1.33  --prep_def_merge_tr_red                 false
% 7.13/1.33  --prep_def_merge_tr_cl                  false
% 7.13/1.33  --smt_preprocessing                     true
% 7.13/1.33  --smt_ac_axioms                         fast
% 7.13/1.33  --preprocessed_out                      false
% 7.13/1.33  --preprocessed_stats                    false
% 7.13/1.33  
% 7.13/1.33  ------ Abstraction refinement Options
% 7.13/1.33  
% 7.13/1.33  --abstr_ref                             []
% 7.13/1.33  --abstr_ref_prep                        false
% 7.13/1.33  --abstr_ref_until_sat                   false
% 7.13/1.33  --abstr_ref_sig_restrict                funpre
% 7.13/1.33  --abstr_ref_af_restrict_to_split_sk     false
% 7.13/1.33  --abstr_ref_under                       []
% 7.13/1.33  
% 7.13/1.33  ------ SAT Options
% 7.13/1.33  
% 7.13/1.33  --sat_mode                              false
% 7.13/1.33  --sat_fm_restart_options                ""
% 7.13/1.33  --sat_gr_def                            false
% 7.13/1.33  --sat_epr_types                         true
% 7.13/1.33  --sat_non_cyclic_types                  false
% 7.13/1.33  --sat_finite_models                     false
% 7.13/1.33  --sat_fm_lemmas                         false
% 7.13/1.33  --sat_fm_prep                           false
% 7.13/1.33  --sat_fm_uc_incr                        true
% 7.13/1.33  --sat_out_model                         small
% 7.13/1.33  --sat_out_clauses                       false
% 7.13/1.33  
% 7.13/1.33  ------ QBF Options
% 7.13/1.33  
% 7.13/1.33  --qbf_mode                              false
% 7.13/1.33  --qbf_elim_univ                         false
% 7.13/1.33  --qbf_dom_inst                          none
% 7.13/1.33  --qbf_dom_pre_inst                      false
% 7.13/1.33  --qbf_sk_in                             false
% 7.13/1.33  --qbf_pred_elim                         true
% 7.13/1.33  --qbf_split                             512
% 7.13/1.33  
% 7.13/1.33  ------ BMC1 Options
% 7.13/1.33  
% 7.13/1.33  --bmc1_incremental                      false
% 7.13/1.33  --bmc1_axioms                           reachable_all
% 7.13/1.33  --bmc1_min_bound                        0
% 7.13/1.33  --bmc1_max_bound                        -1
% 7.13/1.33  --bmc1_max_bound_default                -1
% 7.13/1.33  --bmc1_symbol_reachability              true
% 7.13/1.33  --bmc1_property_lemmas                  false
% 7.13/1.33  --bmc1_k_induction                      false
% 7.13/1.33  --bmc1_non_equiv_states                 false
% 7.13/1.33  --bmc1_deadlock                         false
% 7.13/1.33  --bmc1_ucm                              false
% 7.13/1.33  --bmc1_add_unsat_core                   none
% 7.13/1.33  --bmc1_unsat_core_children              false
% 7.13/1.33  --bmc1_unsat_core_extrapolate_axioms    false
% 7.13/1.33  --bmc1_out_stat                         full
% 7.13/1.33  --bmc1_ground_init                      false
% 7.13/1.33  --bmc1_pre_inst_next_state              false
% 7.13/1.33  --bmc1_pre_inst_state                   false
% 7.13/1.33  --bmc1_pre_inst_reach_state             false
% 7.13/1.33  --bmc1_out_unsat_core                   false
% 7.13/1.33  --bmc1_aig_witness_out                  false
% 7.13/1.33  --bmc1_verbose                          false
% 7.13/1.33  --bmc1_dump_clauses_tptp                false
% 7.13/1.33  --bmc1_dump_unsat_core_tptp             false
% 7.13/1.33  --bmc1_dump_file                        -
% 7.13/1.33  --bmc1_ucm_expand_uc_limit              128
% 7.13/1.33  --bmc1_ucm_n_expand_iterations          6
% 7.13/1.33  --bmc1_ucm_extend_mode                  1
% 7.13/1.33  --bmc1_ucm_init_mode                    2
% 7.13/1.33  --bmc1_ucm_cone_mode                    none
% 7.13/1.33  --bmc1_ucm_reduced_relation_type        0
% 7.13/1.33  --bmc1_ucm_relax_model                  4
% 7.13/1.33  --bmc1_ucm_full_tr_after_sat            true
% 7.13/1.33  --bmc1_ucm_expand_neg_assumptions       false
% 7.13/1.33  --bmc1_ucm_layered_model                none
% 7.13/1.33  --bmc1_ucm_max_lemma_size               10
% 7.13/1.33  
% 7.13/1.33  ------ AIG Options
% 7.13/1.33  
% 7.13/1.33  --aig_mode                              false
% 7.13/1.33  
% 7.13/1.33  ------ Instantiation Options
% 7.13/1.33  
% 7.13/1.33  --instantiation_flag                    true
% 7.13/1.33  --inst_sos_flag                         true
% 7.13/1.33  --inst_sos_phase                        true
% 7.13/1.33  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.13/1.33  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.13/1.33  --inst_lit_sel_side                     none
% 7.13/1.33  --inst_solver_per_active                1400
% 7.13/1.33  --inst_solver_calls_frac                1.
% 7.13/1.33  --inst_passive_queue_type               priority_queues
% 7.13/1.33  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.13/1.33  --inst_passive_queues_freq              [25;2]
% 7.13/1.33  --inst_dismatching                      true
% 7.13/1.33  --inst_eager_unprocessed_to_passive     true
% 7.13/1.33  --inst_prop_sim_given                   true
% 7.13/1.33  --inst_prop_sim_new                     false
% 7.13/1.33  --inst_subs_new                         false
% 7.13/1.33  --inst_eq_res_simp                      false
% 7.13/1.33  --inst_subs_given                       false
% 7.13/1.33  --inst_orphan_elimination               true
% 7.13/1.33  --inst_learning_loop_flag               true
% 7.13/1.33  --inst_learning_start                   3000
% 7.13/1.33  --inst_learning_factor                  2
% 7.13/1.33  --inst_start_prop_sim_after_learn       3
% 7.13/1.33  --inst_sel_renew                        solver
% 7.13/1.33  --inst_lit_activity_flag                true
% 7.13/1.33  --inst_restr_to_given                   false
% 7.13/1.33  --inst_activity_threshold               500
% 7.13/1.33  --inst_out_proof                        true
% 7.13/1.33  
% 7.13/1.33  ------ Resolution Options
% 7.13/1.33  
% 7.13/1.33  --resolution_flag                       false
% 7.13/1.33  --res_lit_sel                           adaptive
% 7.13/1.33  --res_lit_sel_side                      none
% 7.13/1.33  --res_ordering                          kbo
% 7.13/1.33  --res_to_prop_solver                    active
% 7.13/1.33  --res_prop_simpl_new                    false
% 7.13/1.33  --res_prop_simpl_given                  true
% 7.13/1.33  --res_passive_queue_type                priority_queues
% 7.13/1.33  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.13/1.33  --res_passive_queues_freq               [15;5]
% 7.13/1.33  --res_forward_subs                      full
% 7.13/1.33  --res_backward_subs                     full
% 7.13/1.33  --res_forward_subs_resolution           true
% 7.13/1.33  --res_backward_subs_resolution          true
% 7.13/1.33  --res_orphan_elimination                true
% 7.13/1.33  --res_time_limit                        2.
% 7.13/1.33  --res_out_proof                         true
% 7.13/1.33  
% 7.13/1.33  ------ Superposition Options
% 7.13/1.33  
% 7.13/1.33  --superposition_flag                    true
% 7.13/1.33  --sup_passive_queue_type                priority_queues
% 7.13/1.33  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.13/1.33  --sup_passive_queues_freq               [8;1;4]
% 7.13/1.33  --demod_completeness_check              fast
% 7.13/1.33  --demod_use_ground                      true
% 7.13/1.33  --sup_to_prop_solver                    passive
% 7.13/1.33  --sup_prop_simpl_new                    true
% 7.13/1.33  --sup_prop_simpl_given                  true
% 7.13/1.33  --sup_fun_splitting                     true
% 7.13/1.33  --sup_smt_interval                      50000
% 7.13/1.33  
% 7.13/1.33  ------ Superposition Simplification Setup
% 7.13/1.33  
% 7.13/1.33  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.13/1.33  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.13/1.33  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.13/1.33  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.13/1.33  --sup_full_triv                         [TrivRules;PropSubs]
% 7.13/1.33  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.13/1.33  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.13/1.33  --sup_immed_triv                        [TrivRules]
% 7.13/1.33  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.13/1.33  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.13/1.33  --sup_immed_bw_main                     []
% 7.13/1.33  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.13/1.33  --sup_input_triv                        [Unflattening;TrivRules]
% 7.13/1.33  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.13/1.33  --sup_input_bw                          []
% 7.13/1.33  
% 7.13/1.33  ------ Combination Options
% 7.13/1.33  
% 7.13/1.33  --comb_res_mult                         3
% 7.13/1.33  --comb_sup_mult                         2
% 7.13/1.33  --comb_inst_mult                        10
% 7.13/1.33  
% 7.13/1.33  ------ Debug Options
% 7.13/1.33  
% 7.13/1.33  --dbg_backtrace                         false
% 7.13/1.33  --dbg_dump_prop_clauses                 false
% 7.13/1.33  --dbg_dump_prop_clauses_file            -
% 7.13/1.33  --dbg_out_stat                          false
% 7.13/1.33  
% 7.13/1.33  
% 7.13/1.33  
% 7.13/1.33  
% 7.13/1.33  ------ Proving...
% 7.13/1.33  
% 7.13/1.33  
% 7.13/1.33  % SZS status Theorem for theBenchmark.p
% 7.13/1.33  
% 7.13/1.33  % SZS output start CNFRefutation for theBenchmark.p
% 7.13/1.33  
% 7.13/1.33  fof(f7,axiom,(
% 7.13/1.33    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 7.13/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.13/1.33  
% 7.13/1.33  fof(f19,plain,(
% 7.13/1.33    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.13/1.33    inference(ennf_transformation,[],[f7])).
% 7.13/1.33  
% 7.13/1.33  fof(f33,plain,(
% 7.13/1.33    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.13/1.33    inference(nnf_transformation,[],[f19])).
% 7.13/1.33  
% 7.13/1.33  fof(f34,plain,(
% 7.13/1.33    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.13/1.33    inference(rectify,[],[f33])).
% 7.13/1.33  
% 7.13/1.33  fof(f35,plain,(
% 7.13/1.33    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 7.13/1.33    introduced(choice_axiom,[])).
% 7.13/1.33  
% 7.13/1.33  fof(f36,plain,(
% 7.13/1.33    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.13/1.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 7.13/1.33  
% 7.13/1.33  fof(f56,plain,(
% 7.13/1.33    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.13/1.33    inference(cnf_transformation,[],[f36])).
% 7.13/1.33  
% 7.13/1.33  fof(f54,plain,(
% 7.13/1.33    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.13/1.33    inference(cnf_transformation,[],[f36])).
% 7.13/1.33  
% 7.13/1.33  fof(f1,axiom,(
% 7.13/1.33    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.13/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.13/1.33  
% 7.13/1.33  fof(f15,plain,(
% 7.13/1.33    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.13/1.33    inference(ennf_transformation,[],[f1])).
% 7.13/1.33  
% 7.13/1.33  fof(f27,plain,(
% 7.13/1.33    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.13/1.33    inference(nnf_transformation,[],[f15])).
% 7.13/1.33  
% 7.13/1.33  fof(f28,plain,(
% 7.13/1.33    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.13/1.33    inference(rectify,[],[f27])).
% 7.13/1.33  
% 7.13/1.33  fof(f29,plain,(
% 7.13/1.33    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.13/1.33    introduced(choice_axiom,[])).
% 7.13/1.33  
% 7.13/1.33  fof(f30,plain,(
% 7.13/1.33    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.13/1.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 7.13/1.33  
% 7.13/1.33  fof(f42,plain,(
% 7.13/1.33    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.13/1.33    inference(cnf_transformation,[],[f30])).
% 7.13/1.33  
% 7.13/1.33  fof(f2,axiom,(
% 7.13/1.33    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.13/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.13/1.33  
% 7.13/1.33  fof(f16,plain,(
% 7.13/1.33    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.13/1.33    inference(ennf_transformation,[],[f2])).
% 7.13/1.33  
% 7.13/1.33  fof(f31,plain,(
% 7.13/1.33    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.13/1.33    inference(nnf_transformation,[],[f16])).
% 7.13/1.33  
% 7.13/1.33  fof(f46,plain,(
% 7.13/1.33    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 7.13/1.33    inference(cnf_transformation,[],[f31])).
% 7.13/1.33  
% 7.13/1.33  fof(f6,axiom,(
% 7.13/1.33    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.13/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.13/1.33  
% 7.13/1.33  fof(f53,plain,(
% 7.13/1.33    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.13/1.33    inference(cnf_transformation,[],[f6])).
% 7.13/1.33  
% 7.13/1.33  fof(f12,conjecture,(
% 7.13/1.33    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.13/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.13/1.33  
% 7.13/1.33  fof(f13,negated_conjecture,(
% 7.13/1.33    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.13/1.33    inference(negated_conjecture,[],[f12])).
% 7.13/1.33  
% 7.13/1.33  fof(f14,plain,(
% 7.13/1.33    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.13/1.33    inference(pure_predicate_removal,[],[f13])).
% 7.13/1.33  
% 7.13/1.33  fof(f25,plain,(
% 7.13/1.33    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 7.13/1.33    inference(ennf_transformation,[],[f14])).
% 7.13/1.33  
% 7.13/1.33  fof(f26,plain,(
% 7.13/1.33    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 7.13/1.33    inference(flattening,[],[f25])).
% 7.13/1.33  
% 7.13/1.33  fof(f40,plain,(
% 7.13/1.33    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK6 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK6,k7_relset_1(X0,X1,X3,X2)))) )),
% 7.13/1.33    introduced(choice_axiom,[])).
% 7.13/1.33  
% 7.13/1.33  fof(f39,plain,(
% 7.13/1.33    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK5,X5) != X4 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK5))),
% 7.13/1.33    introduced(choice_axiom,[])).
% 7.13/1.33  
% 7.13/1.33  fof(f41,plain,(
% 7.13/1.33    (! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK5)),
% 7.13/1.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f26,f40,f39])).
% 7.13/1.33  
% 7.13/1.33  fof(f65,plain,(
% 7.13/1.33    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 7.13/1.33    inference(cnf_transformation,[],[f41])).
% 7.13/1.33  
% 7.13/1.33  fof(f3,axiom,(
% 7.13/1.33    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.13/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.13/1.33  
% 7.13/1.33  fof(f32,plain,(
% 7.13/1.33    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.13/1.33    inference(nnf_transformation,[],[f3])).
% 7.13/1.33  
% 7.13/1.33  fof(f49,plain,(
% 7.13/1.33    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.13/1.33    inference(cnf_transformation,[],[f32])).
% 7.13/1.33  
% 7.13/1.33  fof(f5,axiom,(
% 7.13/1.33    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.13/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.13/1.33  
% 7.13/1.33  fof(f18,plain,(
% 7.13/1.33    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.13/1.33    inference(ennf_transformation,[],[f5])).
% 7.13/1.33  
% 7.13/1.33  fof(f52,plain,(
% 7.13/1.33    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.13/1.33    inference(cnf_transformation,[],[f18])).
% 7.13/1.33  
% 7.13/1.33  fof(f50,plain,(
% 7.13/1.33    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.13/1.33    inference(cnf_transformation,[],[f32])).
% 7.13/1.33  
% 7.13/1.33  fof(f11,axiom,(
% 7.13/1.33    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.13/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.13/1.33  
% 7.13/1.33  fof(f24,plain,(
% 7.13/1.33    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.13/1.33    inference(ennf_transformation,[],[f11])).
% 7.13/1.33  
% 7.13/1.33  fof(f63,plain,(
% 7.13/1.33    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.13/1.33    inference(cnf_transformation,[],[f24])).
% 7.13/1.33  
% 7.13/1.33  fof(f66,plain,(
% 7.13/1.33    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))),
% 7.13/1.33    inference(cnf_transformation,[],[f41])).
% 7.13/1.33  
% 7.13/1.33  fof(f55,plain,(
% 7.13/1.33    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.13/1.33    inference(cnf_transformation,[],[f36])).
% 7.13/1.33  
% 7.13/1.33  fof(f8,axiom,(
% 7.13/1.33    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 7.13/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.13/1.33  
% 7.13/1.33  fof(f20,plain,(
% 7.13/1.33    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.13/1.33    inference(ennf_transformation,[],[f8])).
% 7.13/1.33  
% 7.13/1.33  fof(f21,plain,(
% 7.13/1.33    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.13/1.33    inference(flattening,[],[f20])).
% 7.13/1.33  
% 7.13/1.33  fof(f37,plain,(
% 7.13/1.33    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.13/1.33    inference(nnf_transformation,[],[f21])).
% 7.13/1.33  
% 7.13/1.33  fof(f38,plain,(
% 7.13/1.33    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.13/1.33    inference(flattening,[],[f37])).
% 7.13/1.33  
% 7.13/1.33  fof(f59,plain,(
% 7.13/1.33    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.13/1.33    inference(cnf_transformation,[],[f38])).
% 7.13/1.33  
% 7.13/1.33  fof(f64,plain,(
% 7.13/1.33    v1_funct_1(sK5)),
% 7.13/1.33    inference(cnf_transformation,[],[f41])).
% 7.13/1.33  
% 7.13/1.33  fof(f67,plain,(
% 7.13/1.33    ( ! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) )),
% 7.13/1.33    inference(cnf_transformation,[],[f41])).
% 7.13/1.33  
% 7.13/1.33  fof(f10,axiom,(
% 7.13/1.33    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.13/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.13/1.33  
% 7.13/1.33  fof(f23,plain,(
% 7.13/1.33    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.13/1.33    inference(ennf_transformation,[],[f10])).
% 7.13/1.33  
% 7.13/1.33  fof(f62,plain,(
% 7.13/1.33    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.13/1.33    inference(cnf_transformation,[],[f23])).
% 7.13/1.33  
% 7.13/1.33  fof(f9,axiom,(
% 7.13/1.33    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.13/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.13/1.33  
% 7.13/1.33  fof(f22,plain,(
% 7.13/1.33    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.13/1.33    inference(ennf_transformation,[],[f9])).
% 7.13/1.33  
% 7.13/1.33  fof(f61,plain,(
% 7.13/1.33    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.13/1.33    inference(cnf_transformation,[],[f22])).
% 7.13/1.33  
% 7.13/1.33  fof(f4,axiom,(
% 7.13/1.33    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.13/1.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.13/1.33  
% 7.13/1.33  fof(f17,plain,(
% 7.13/1.33    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.13/1.33    inference(ennf_transformation,[],[f4])).
% 7.13/1.33  
% 7.13/1.33  fof(f51,plain,(
% 7.13/1.33    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.13/1.33    inference(cnf_transformation,[],[f17])).
% 7.13/1.33  
% 7.13/1.33  cnf(c_13,plain,
% 7.13/1.33      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.13/1.33      | r2_hidden(sK1(X0,X2,X1),X2)
% 7.13/1.33      | ~ v1_relat_1(X1) ),
% 7.13/1.33      inference(cnf_transformation,[],[f56]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1517,plain,
% 7.13/1.33      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.13/1.33      | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
% 7.13/1.33      | v1_relat_1(X1) != iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_15,plain,
% 7.13/1.33      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.13/1.33      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 7.13/1.33      | ~ v1_relat_1(X1) ),
% 7.13/1.33      inference(cnf_transformation,[],[f54]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1515,plain,
% 7.13/1.33      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.13/1.33      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 7.13/1.33      | v1_relat_1(X1) != iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_2,plain,
% 7.13/1.33      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.13/1.33      inference(cnf_transformation,[],[f42]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1526,plain,
% 7.13/1.33      ( r2_hidden(X0,X1) != iProver_top
% 7.13/1.33      | r2_hidden(X0,X2) = iProver_top
% 7.13/1.33      | r1_tarski(X1,X2) != iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_2938,plain,
% 7.13/1.33      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.13/1.33      | r2_hidden(sK1(X0,X2,X1),X3) = iProver_top
% 7.13/1.33      | r1_tarski(k1_relat_1(X1),X3) != iProver_top
% 7.13/1.33      | v1_relat_1(X1) != iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_1515,c_1526]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_5,plain,
% 7.13/1.33      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.13/1.33      inference(cnf_transformation,[],[f46]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1523,plain,
% 7.13/1.33      ( m1_subset_1(X0,X1) = iProver_top
% 7.13/1.33      | r2_hidden(X0,X1) != iProver_top
% 7.13/1.33      | v1_xboole_0(X1) = iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_11376,plain,
% 7.13/1.33      ( m1_subset_1(sK1(X0,X1,X2),X3) = iProver_top
% 7.13/1.33      | r2_hidden(X0,k9_relat_1(X2,X1)) != iProver_top
% 7.13/1.33      | r1_tarski(k1_relat_1(X2),X3) != iProver_top
% 7.13/1.33      | v1_relat_1(X2) != iProver_top
% 7.13/1.33      | v1_xboole_0(X3) = iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_2938,c_1523]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_11,plain,
% 7.13/1.33      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.13/1.33      inference(cnf_transformation,[],[f53]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1519,plain,
% 7.13/1.33      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_24,negated_conjecture,
% 7.13/1.33      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 7.13/1.33      inference(cnf_transformation,[],[f65]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1509,plain,
% 7.13/1.33      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_8,plain,
% 7.13/1.33      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.13/1.33      inference(cnf_transformation,[],[f49]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1520,plain,
% 7.13/1.33      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.13/1.33      | r1_tarski(X0,X1) = iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1790,plain,
% 7.13/1.33      ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_1509,c_1520]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_10,plain,
% 7.13/1.33      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.13/1.33      | ~ v1_relat_1(X1)
% 7.13/1.33      | v1_relat_1(X0) ),
% 7.13/1.33      inference(cnf_transformation,[],[f52]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_7,plain,
% 7.13/1.33      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.13/1.33      inference(cnf_transformation,[],[f50]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_205,plain,
% 7.13/1.33      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.13/1.33      inference(prop_impl,[status(thm)],[c_7]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_206,plain,
% 7.13/1.33      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.13/1.33      inference(renaming,[status(thm)],[c_205]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_257,plain,
% 7.13/1.33      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.13/1.33      inference(bin_hyper_res,[status(thm)],[c_10,c_206]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1507,plain,
% 7.13/1.33      ( r1_tarski(X0,X1) != iProver_top
% 7.13/1.33      | v1_relat_1(X1) != iProver_top
% 7.13/1.33      | v1_relat_1(X0) = iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_257]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_3916,plain,
% 7.13/1.33      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 7.13/1.33      | v1_relat_1(sK5) = iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_1790,c_1507]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_4142,plain,
% 7.13/1.33      ( v1_relat_1(sK5) = iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_1519,c_3916]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_21,plain,
% 7.13/1.33      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.13/1.33      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.13/1.33      inference(cnf_transformation,[],[f63]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1512,plain,
% 7.13/1.33      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.13/1.33      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_2156,plain,
% 7.13/1.33      ( k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_1509,c_1512]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_23,negated_conjecture,
% 7.13/1.33      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
% 7.13/1.33      inference(cnf_transformation,[],[f66]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1510,plain,
% 7.13/1.33      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_2545,plain,
% 7.13/1.33      ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) = iProver_top ),
% 7.13/1.33      inference(demodulation,[status(thm)],[c_2156,c_1510]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_14,plain,
% 7.13/1.33      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.13/1.33      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 7.13/1.33      | ~ v1_relat_1(X1) ),
% 7.13/1.33      inference(cnf_transformation,[],[f55]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1516,plain,
% 7.13/1.33      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.13/1.33      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 7.13/1.33      | v1_relat_1(X1) != iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_17,plain,
% 7.13/1.33      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.13/1.33      | ~ v1_funct_1(X2)
% 7.13/1.33      | ~ v1_relat_1(X2)
% 7.13/1.33      | k1_funct_1(X2,X0) = X1 ),
% 7.13/1.33      inference(cnf_transformation,[],[f59]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_25,negated_conjecture,
% 7.13/1.33      ( v1_funct_1(sK5) ),
% 7.13/1.33      inference(cnf_transformation,[],[f64]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_380,plain,
% 7.13/1.33      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.13/1.33      | ~ v1_relat_1(X2)
% 7.13/1.33      | k1_funct_1(X2,X0) = X1
% 7.13/1.33      | sK5 != X2 ),
% 7.13/1.33      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_381,plain,
% 7.13/1.33      ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 7.13/1.33      | ~ v1_relat_1(sK5)
% 7.13/1.33      | k1_funct_1(sK5,X0) = X1 ),
% 7.13/1.33      inference(unflattening,[status(thm)],[c_380]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1504,plain,
% 7.13/1.33      ( k1_funct_1(sK5,X0) = X1
% 7.13/1.33      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 7.13/1.33      | v1_relat_1(sK5) != iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_2999,plain,
% 7.13/1.33      ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
% 7.13/1.33      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 7.13/1.33      | v1_relat_1(sK5) != iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_1516,c_1504]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_3123,plain,
% 7.13/1.33      ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6
% 7.13/1.33      | v1_relat_1(sK5) != iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_2545,c_2999]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_4219,plain,
% 7.13/1.33      ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6 ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_4142,c_3123]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_22,negated_conjecture,
% 7.13/1.33      ( ~ m1_subset_1(X0,sK2)
% 7.13/1.33      | ~ r2_hidden(X0,sK4)
% 7.13/1.33      | k1_funct_1(sK5,X0) != sK6 ),
% 7.13/1.33      inference(cnf_transformation,[],[f67]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1511,plain,
% 7.13/1.33      ( k1_funct_1(sK5,X0) != sK6
% 7.13/1.33      | m1_subset_1(X0,sK2) != iProver_top
% 7.13/1.33      | r2_hidden(X0,sK4) != iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_4225,plain,
% 7.13/1.33      ( m1_subset_1(sK1(sK6,sK4,sK5),sK2) != iProver_top
% 7.13/1.33      | r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_4219,c_1511]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_26572,plain,
% 7.13/1.33      ( r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top
% 7.13/1.33      | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
% 7.13/1.33      | r1_tarski(k1_relat_1(sK5),sK2) != iProver_top
% 7.13/1.33      | v1_relat_1(sK5) != iProver_top
% 7.13/1.33      | v1_xboole_0(sK2) = iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_11376,c_4225]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_27,plain,
% 7.13/1.33      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1665,plain,
% 7.13/1.33      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | r1_tarski(X0,sK2) ),
% 7.13/1.33      inference(instantiation,[status(thm)],[c_8]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1839,plain,
% 7.13/1.33      ( ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(sK2))
% 7.13/1.33      | r1_tarski(k1_relat_1(X0),sK2) ),
% 7.13/1.33      inference(instantiation,[status(thm)],[c_1665]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1845,plain,
% 7.13/1.33      ( m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(sK2)) != iProver_top
% 7.13/1.33      | r1_tarski(k1_relat_1(X0),sK2) = iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_1839]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1847,plain,
% 7.13/1.33      ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) != iProver_top
% 7.13/1.33      | r1_tarski(k1_relat_1(sK5),sK2) = iProver_top ),
% 7.13/1.33      inference(instantiation,[status(thm)],[c_1845]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_20,plain,
% 7.13/1.33      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.13/1.33      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.13/1.33      inference(cnf_transformation,[],[f62]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1513,plain,
% 7.13/1.33      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.13/1.33      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1989,plain,
% 7.13/1.33      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_1509,c_1513]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_19,plain,
% 7.13/1.33      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.13/1.33      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.13/1.33      inference(cnf_transformation,[],[f61]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1514,plain,
% 7.13/1.33      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.13/1.33      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_2830,plain,
% 7.13/1.33      ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top
% 7.13/1.33      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_1989,c_1514]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_3109,plain,
% 7.13/1.33      ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top ),
% 7.13/1.33      inference(global_propositional_subsumption,
% 7.13/1.33                [status(thm)],
% 7.13/1.33                [c_2830,c_27]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_3115,plain,
% 7.13/1.33      ( r1_tarski(k1_relat_1(sK5),sK2) = iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_3109,c_1520]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_9,plain,
% 7.13/1.33      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.13/1.33      | ~ r2_hidden(X2,X0)
% 7.13/1.33      | ~ v1_xboole_0(X1) ),
% 7.13/1.33      inference(cnf_transformation,[],[f51]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_256,plain,
% 7.13/1.33      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 7.13/1.33      inference(bin_hyper_res,[status(thm)],[c_9,c_206]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_1508,plain,
% 7.13/1.33      ( r2_hidden(X0,X1) != iProver_top
% 7.13/1.33      | r1_tarski(X1,X2) != iProver_top
% 7.13/1.33      | v1_xboole_0(X2) != iProver_top ),
% 7.13/1.33      inference(predicate_to_equality,[status(thm)],[c_256]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_2940,plain,
% 7.13/1.33      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.13/1.33      | r1_tarski(k1_relat_1(X1),X3) != iProver_top
% 7.13/1.33      | v1_relat_1(X1) != iProver_top
% 7.13/1.33      | v1_xboole_0(X3) != iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_1515,c_1508]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_9763,plain,
% 7.13/1.33      ( r1_tarski(k1_relat_1(sK5),X0) != iProver_top
% 7.13/1.33      | v1_relat_1(sK5) != iProver_top
% 7.13/1.33      | v1_xboole_0(X0) != iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_2545,c_2940]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_9858,plain,
% 7.13/1.33      ( r1_tarski(k1_relat_1(sK5),X0) != iProver_top
% 7.13/1.33      | v1_xboole_0(X0) != iProver_top ),
% 7.13/1.33      inference(global_propositional_subsumption,
% 7.13/1.33                [status(thm)],
% 7.13/1.33                [c_9763,c_4142]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_9862,plain,
% 7.13/1.33      ( v1_xboole_0(sK2) != iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_3115,c_9858]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_26923,plain,
% 7.13/1.33      ( r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
% 7.13/1.33      inference(global_propositional_subsumption,
% 7.13/1.33                [status(thm)],
% 7.13/1.33                [c_26572,c_27,c_1847,c_2545,c_2830,c_4142,c_9862]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(c_26927,plain,
% 7.13/1.33      ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
% 7.13/1.33      | v1_relat_1(sK5) != iProver_top ),
% 7.13/1.33      inference(superposition,[status(thm)],[c_1517,c_26923]) ).
% 7.13/1.33  
% 7.13/1.33  cnf(contradiction,plain,
% 7.13/1.33      ( $false ),
% 7.13/1.33      inference(minisat,[status(thm)],[c_26927,c_4142,c_2545]) ).
% 7.13/1.33  
% 7.13/1.33  
% 7.13/1.33  % SZS output end CNFRefutation for theBenchmark.p
% 7.13/1.33  
% 7.13/1.33  ------                               Statistics
% 7.13/1.33  
% 7.13/1.33  ------ General
% 7.13/1.33  
% 7.13/1.33  abstr_ref_over_cycles:                  0
% 7.13/1.33  abstr_ref_under_cycles:                 0
% 7.13/1.33  gc_basic_clause_elim:                   0
% 7.13/1.33  forced_gc_time:                         0
% 7.13/1.33  parsing_time:                           0.006
% 7.13/1.33  unif_index_cands_time:                  0.
% 7.13/1.33  unif_index_add_time:                    0.
% 7.13/1.33  orderings_time:                         0.
% 7.13/1.33  out_proof_time:                         0.01
% 7.13/1.33  total_time:                             0.808
% 7.13/1.33  num_of_symbols:                         52
% 7.13/1.33  num_of_terms:                           22060
% 7.13/1.33  
% 7.13/1.33  ------ Preprocessing
% 7.13/1.33  
% 7.13/1.33  num_of_splits:                          0
% 7.13/1.33  num_of_split_atoms:                     0
% 7.13/1.33  num_of_reused_defs:                     0
% 7.13/1.33  num_eq_ax_congr_red:                    43
% 7.13/1.33  num_of_sem_filtered_clauses:            1
% 7.13/1.33  num_of_subtypes:                        0
% 7.13/1.33  monotx_restored_types:                  0
% 7.13/1.33  sat_num_of_epr_types:                   0
% 7.13/1.33  sat_num_of_non_cyclic_types:            0
% 7.13/1.33  sat_guarded_non_collapsed_types:        0
% 7.13/1.33  num_pure_diseq_elim:                    0
% 7.13/1.33  simp_replaced_by:                       0
% 7.13/1.33  res_preprocessed:                       124
% 7.13/1.33  prep_upred:                             0
% 7.13/1.33  prep_unflattend:                        27
% 7.13/1.33  smt_new_axioms:                         0
% 7.13/1.33  pred_elim_cands:                        5
% 7.13/1.33  pred_elim:                              1
% 7.13/1.33  pred_elim_cl:                           1
% 7.13/1.33  pred_elim_cycles:                       3
% 7.13/1.33  merged_defs:                            8
% 7.13/1.33  merged_defs_ncl:                        0
% 7.13/1.33  bin_hyper_res:                          10
% 7.13/1.33  prep_cycles:                            4
% 7.13/1.33  pred_elim_time:                         0.003
% 7.13/1.33  splitting_time:                         0.
% 7.13/1.33  sem_filter_time:                        0.
% 7.13/1.33  monotx_time:                            0.
% 7.13/1.33  subtype_inf_time:                       0.
% 7.13/1.33  
% 7.13/1.33  ------ Problem properties
% 7.13/1.33  
% 7.13/1.33  clauses:                                25
% 7.13/1.33  conjectures:                            3
% 7.13/1.33  epr:                                    7
% 7.13/1.33  horn:                                   22
% 7.13/1.33  ground:                                 2
% 7.13/1.33  unary:                                  3
% 7.13/1.33  binary:                                 7
% 7.13/1.33  lits:                                   64
% 7.13/1.33  lits_eq:                                4
% 7.13/1.33  fd_pure:                                0
% 7.13/1.33  fd_pseudo:                              0
% 7.13/1.33  fd_cond:                                0
% 7.13/1.33  fd_pseudo_cond:                         1
% 7.13/1.33  ac_symbols:                             0
% 7.13/1.33  
% 7.13/1.33  ------ Propositional Solver
% 7.13/1.33  
% 7.13/1.33  prop_solver_calls:                      35
% 7.13/1.33  prop_fast_solver_calls:                 2053
% 7.13/1.33  smt_solver_calls:                       0
% 7.13/1.33  smt_fast_solver_calls:                  0
% 7.13/1.33  prop_num_of_clauses:                    11456
% 7.13/1.33  prop_preprocess_simplified:             22265
% 7.13/1.33  prop_fo_subsumed:                       106
% 7.13/1.33  prop_solver_time:                       0.
% 7.13/1.33  smt_solver_time:                        0.
% 7.13/1.33  smt_fast_solver_time:                   0.
% 7.13/1.33  prop_fast_solver_time:                  0.
% 7.13/1.33  prop_unsat_core_time:                   0.
% 7.13/1.33  
% 7.13/1.33  ------ QBF
% 7.13/1.33  
% 7.13/1.33  qbf_q_res:                              0
% 7.13/1.33  qbf_num_tautologies:                    0
% 7.13/1.33  qbf_prep_cycles:                        0
% 7.13/1.33  
% 7.13/1.33  ------ BMC1
% 7.13/1.33  
% 7.13/1.33  bmc1_current_bound:                     -1
% 7.13/1.33  bmc1_last_solved_bound:                 -1
% 7.13/1.33  bmc1_unsat_core_size:                   -1
% 7.13/1.33  bmc1_unsat_core_parents_size:           -1
% 7.13/1.33  bmc1_merge_next_fun:                    0
% 7.13/1.33  bmc1_unsat_core_clauses_time:           0.
% 7.13/1.33  
% 7.13/1.33  ------ Instantiation
% 7.13/1.33  
% 7.13/1.33  inst_num_of_clauses:                    2409
% 7.13/1.33  inst_num_in_passive:                    1257
% 7.13/1.33  inst_num_in_active:                     1081
% 7.13/1.33  inst_num_in_unprocessed:                71
% 7.13/1.33  inst_num_of_loops:                      1410
% 7.13/1.33  inst_num_of_learning_restarts:          0
% 7.13/1.33  inst_num_moves_active_passive:          322
% 7.13/1.33  inst_lit_activity:                      0
% 7.13/1.33  inst_lit_activity_moves:                0
% 7.13/1.33  inst_num_tautologies:                   0
% 7.13/1.33  inst_num_prop_implied:                  0
% 7.13/1.33  inst_num_existing_simplified:           0
% 7.13/1.33  inst_num_eq_res_simplified:             0
% 7.13/1.33  inst_num_child_elim:                    0
% 7.13/1.33  inst_num_of_dismatching_blockings:      1853
% 7.13/1.33  inst_num_of_non_proper_insts:           2571
% 7.13/1.33  inst_num_of_duplicates:                 0
% 7.13/1.33  inst_inst_num_from_inst_to_res:         0
% 7.13/1.33  inst_dismatching_checking_time:         0.
% 7.13/1.33  
% 7.13/1.33  ------ Resolution
% 7.13/1.33  
% 7.13/1.33  res_num_of_clauses:                     0
% 7.13/1.33  res_num_in_passive:                     0
% 7.13/1.33  res_num_in_active:                      0
% 7.13/1.33  res_num_of_loops:                       128
% 7.13/1.33  res_forward_subset_subsumed:            100
% 7.13/1.33  res_backward_subset_subsumed:           0
% 7.13/1.33  res_forward_subsumed:                   0
% 7.13/1.33  res_backward_subsumed:                  0
% 7.13/1.33  res_forward_subsumption_resolution:     0
% 7.13/1.33  res_backward_subsumption_resolution:    0
% 7.13/1.33  res_clause_to_clause_subsumption:       4924
% 7.13/1.33  res_orphan_elimination:                 0
% 7.13/1.33  res_tautology_del:                      332
% 7.13/1.33  res_num_eq_res_simplified:              0
% 7.13/1.33  res_num_sel_changes:                    0
% 7.13/1.33  res_moves_from_active_to_pass:          0
% 7.13/1.33  
% 7.13/1.33  ------ Superposition
% 7.13/1.33  
% 7.13/1.33  sup_time_total:                         0.
% 7.13/1.33  sup_time_generating:                    0.
% 7.13/1.33  sup_time_sim_full:                      0.
% 7.13/1.33  sup_time_sim_immed:                     0.
% 7.13/1.33  
% 7.13/1.33  sup_num_of_clauses:                     1004
% 7.13/1.33  sup_num_in_active:                      254
% 7.13/1.33  sup_num_in_passive:                     750
% 7.13/1.33  sup_num_of_loops:                       280
% 7.13/1.33  sup_fw_superposition:                   738
% 7.13/1.33  sup_bw_superposition:                   576
% 7.13/1.33  sup_immediate_simplified:               176
% 7.13/1.33  sup_given_eliminated:                   1
% 7.13/1.33  comparisons_done:                       0
% 7.13/1.33  comparisons_avoided:                    0
% 7.13/1.33  
% 7.13/1.33  ------ Simplifications
% 7.13/1.33  
% 7.13/1.33  
% 7.13/1.33  sim_fw_subset_subsumed:                 65
% 7.13/1.33  sim_bw_subset_subsumed:                 19
% 7.13/1.33  sim_fw_subsumed:                        73
% 7.13/1.33  sim_bw_subsumed:                        53
% 7.13/1.33  sim_fw_subsumption_res:                 0
% 7.13/1.33  sim_bw_subsumption_res:                 0
% 7.13/1.33  sim_tautology_del:                      28
% 7.13/1.33  sim_eq_tautology_del:                   5
% 7.13/1.33  sim_eq_res_simp:                        0
% 7.13/1.33  sim_fw_demodulated:                     1
% 7.13/1.33  sim_bw_demodulated:                     3
% 7.13/1.33  sim_light_normalised:                   17
% 7.13/1.33  sim_joinable_taut:                      0
% 7.13/1.33  sim_joinable_simp:                      0
% 7.13/1.33  sim_ac_normalised:                      0
% 7.13/1.33  sim_smt_subsumption:                    0
% 7.13/1.33  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:58 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  158 (3830 expanded)
%              Number of clauses        :  102 (1261 expanded)
%              Number of leaves         :   17 ( 914 expanded)
%              Depth                    :   28
%              Number of atoms          :  503 (18919 expanded)
%              Number of equality atoms :  236 (4441 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f33,plain,
    ( ! [X5] :
        ( k1_funct_1(sK4,X5) != sK5
        | ~ r2_hidden(X5,sK3)
        | ~ r2_hidden(X5,sK1) )
    & r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f23,f32,f31])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f30,plain,(
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

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
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

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X5] :
      ( k1_funct_1(sK4,X5) != sK5
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f44])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_643,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_646,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1091,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_646])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1092,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1091])).

cnf(c_1544,plain,
    ( sK2 = k1_xboole_0
    | k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1091,c_22,c_1092])).

cnf(c_1545,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1544])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_653,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1096,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_643,c_653])).

cnf(c_1546,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1545,c_1096])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_657,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1687,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1546,c_657])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_921,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_2,c_21])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_945,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_921,c_3])).

cnf(c_946,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_945])).

cnf(c_2060,plain,
    ( r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1687,c_946])).

cnf(c_2061,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2060])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_652,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1202,plain,
    ( k7_relset_1(sK1,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_643,c_652])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_644,plain,
    ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1372,plain,
    ( r2_hidden(sK5,k9_relat_1(sK4,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1202,c_644])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_658,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_655,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2483,plain,
    ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
    | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_658,c_655])).

cnf(c_3298,plain,
    ( k1_funct_1(sK4,sK0(sK5,sK3,sK4)) = sK5
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_2483])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3348,plain,
    ( k1_funct_1(sK4,sK0(sK5,sK3,sK4)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3298,c_24,c_946])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,X0) != sK5 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_645,plain,
    ( k1_funct_1(sK4,X0) != sK5
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3352,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),sK1) != iProver_top
    | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3348,c_645])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2133,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),sK3)
    | ~ r2_hidden(sK5,k9_relat_1(sK4,sK3))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2134,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),sK3) = iProver_top
    | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2133])).

cnf(c_3510,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3352,c_946,c_1372,c_2134])).

cnf(c_3515,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2061,c_3510])).

cnf(c_3968,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3515,c_1372])).

cnf(c_3973,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3968,c_643])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_650,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4098,plain,
    ( sK1 = k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_funct_2(sK4,sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3973,c_650])).

cnf(c_25,plain,
    ( v1_funct_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_223,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_250,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_1052,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_236,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_966,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | X2 != sK2
    | X1 != sK1
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_236])).

cnf(c_1126,plain,
    ( v1_funct_2(sK4,X0,X1)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | X1 != sK2
    | X0 != sK1
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_1284,plain,
    ( v1_funct_2(sK4,sK1,X0)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | X0 != sK2
    | sK1 != sK1
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_1286,plain,
    ( X0 != sK2
    | sK1 != sK1
    | sK4 != sK4
    | v1_funct_2(sK4,sK1,X0) = iProver_top
    | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1284])).

cnf(c_1288,plain,
    ( sK1 != sK1
    | sK4 != sK4
    | k1_xboole_0 != sK2
    | v1_funct_2(sK4,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK1,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1286])).

cnf(c_1285,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_224,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1505,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_1506,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1505])).

cnf(c_4163,plain,
    ( sK4 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4098,c_25,c_250,c_1052,c_1288,c_1285,c_1372,c_1506,c_3515])).

cnf(c_4164,plain,
    ( sK1 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4163])).

cnf(c_4169,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4164,c_3973])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_664,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1811,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_658,c_664])).

cnf(c_2238,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_1811])).

cnf(c_2261,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2238])).

cnf(c_226,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4657,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_4659,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4657])).

cnf(c_5036,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4169,c_1,c_945,c_2261,c_4659])).

cnf(c_5043,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_5036,c_653])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_647,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5045,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5036,c_647])).

cnf(c_5052,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5043,c_5045])).

cnf(c_642,plain,
    ( v1_funct_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3974,plain,
    ( v1_funct_2(sK4,sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3968,c_642])).

cnf(c_4170,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4164,c_3974])).

cnf(c_5229,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5052,c_1,c_945,c_2261,c_4170,c_4659])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_656,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3351,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK5,sK3,sK4),sK5),sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3348,c_656])).

cnf(c_2131,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,sK3,sK4),sK5),sK4)
    | ~ r2_hidden(sK5,k9_relat_1(sK4,sK3))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2138,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,sK3,sK4),sK5),sK4) = iProver_top
    | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2131])).

cnf(c_3888,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,sK3,sK4),sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3351,c_946,c_1372,c_2138])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_654,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3895,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3888,c_654])).

cnf(c_2132,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),k1_relat_1(sK4))
    | ~ r2_hidden(sK5,k9_relat_1(sK4,sK3))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2136,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2132])).

cnf(c_4597,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3895,c_946,c_1372,c_2136])).

cnf(c_5233,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5229,c_4597])).

cnf(c_4171,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK0(sK5,sK3,sK4),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4164,c_3510])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5233,c_4659,c_4171,c_2261,c_945,c_1])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:10:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.57/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/0.98  
% 3.57/0.98  ------  iProver source info
% 3.57/0.98  
% 3.57/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.57/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/0.98  git: non_committed_changes: false
% 3.57/0.98  git: last_make_outside_of_git: false
% 3.57/0.98  
% 3.57/0.98  ------ 
% 3.57/0.98  ------ Parsing...
% 3.57/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/0.98  ------ Proving...
% 3.57/0.98  ------ Problem Properties 
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  clauses                                 24
% 3.57/0.98  conjectures                             5
% 3.57/0.98  EPR                                     4
% 3.57/0.98  Horn                                    20
% 3.57/0.98  unary                                   6
% 3.57/0.98  binary                                  3
% 3.57/0.98  lits                                    65
% 3.57/0.98  lits eq                                 13
% 3.57/0.98  fd_pure                                 0
% 3.57/0.98  fd_pseudo                               0
% 3.57/0.98  fd_cond                                 3
% 3.57/0.98  fd_pseudo_cond                          1
% 3.57/0.98  AC symbols                              0
% 3.57/0.98  
% 3.57/0.98  ------ Input Options Time Limit: Unbounded
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  ------ 
% 3.57/0.98  Current options:
% 3.57/0.98  ------ 
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  ------ Proving...
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  % SZS status Theorem for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  fof(f10,conjecture,(
% 3.57/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f11,negated_conjecture,(
% 3.57/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.57/0.98    inference(negated_conjecture,[],[f10])).
% 3.57/0.98  
% 3.57/0.98  fof(f22,plain,(
% 3.57/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.57/0.98    inference(ennf_transformation,[],[f11])).
% 3.57/0.98  
% 3.57/0.98  fof(f23,plain,(
% 3.57/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.57/0.98    inference(flattening,[],[f22])).
% 3.57/0.98  
% 3.57/0.98  fof(f32,plain,(
% 3.57/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK5 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK5,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f31,plain,(
% 3.57/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK4,X5) != X4 | ~r2_hidden(X5,sK3) | ~r2_hidden(X5,sK1)) & r2_hidden(X4,k7_relset_1(sK1,sK2,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f33,plain,(
% 3.57/0.98    (! [X5] : (k1_funct_1(sK4,X5) != sK5 | ~r2_hidden(X5,sK3) | ~r2_hidden(X5,sK1)) & r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f23,f32,f31])).
% 3.57/0.98  
% 3.57/0.98  fof(f55,plain,(
% 3.57/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.57/0.98    inference(cnf_transformation,[],[f33])).
% 3.57/0.98  
% 3.57/0.98  fof(f9,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f20,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.98    inference(ennf_transformation,[],[f9])).
% 3.57/0.98  
% 3.57/0.98  fof(f21,plain,(
% 3.57/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.98    inference(flattening,[],[f20])).
% 3.57/0.98  
% 3.57/0.98  fof(f30,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.98    inference(nnf_transformation,[],[f21])).
% 3.57/0.98  
% 3.57/0.98  fof(f47,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f30])).
% 3.57/0.98  
% 3.57/0.98  fof(f54,plain,(
% 3.57/0.98    v1_funct_2(sK4,sK1,sK2)),
% 3.57/0.98    inference(cnf_transformation,[],[f33])).
% 3.57/0.98  
% 3.57/0.98  fof(f7,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f18,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.98    inference(ennf_transformation,[],[f7])).
% 3.57/0.98  
% 3.57/0.98  fof(f45,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f18])).
% 3.57/0.98  
% 3.57/0.98  fof(f5,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f15,plain,(
% 3.57/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.57/0.98    inference(ennf_transformation,[],[f5])).
% 3.57/0.98  
% 3.57/0.98  fof(f24,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.57/0.98    inference(nnf_transformation,[],[f15])).
% 3.57/0.98  
% 3.57/0.98  fof(f25,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.57/0.98    inference(rectify,[],[f24])).
% 3.57/0.98  
% 3.57/0.98  fof(f26,plain,(
% 3.57/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f27,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.57/0.98  
% 3.57/0.98  fof(f38,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f27])).
% 3.57/0.98  
% 3.57/0.98  fof(f3,axiom,(
% 3.57/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f14,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.57/0.98    inference(ennf_transformation,[],[f3])).
% 3.57/0.98  
% 3.57/0.98  fof(f36,plain,(
% 3.57/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f14])).
% 3.57/0.98  
% 3.57/0.98  fof(f4,axiom,(
% 3.57/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f37,plain,(
% 3.57/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f4])).
% 3.57/0.98  
% 3.57/0.98  fof(f8,axiom,(
% 3.57/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f19,plain,(
% 3.57/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.98    inference(ennf_transformation,[],[f8])).
% 3.57/0.98  
% 3.57/0.98  fof(f46,plain,(
% 3.57/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f19])).
% 3.57/0.98  
% 3.57/0.98  fof(f56,plain,(
% 3.57/0.98    r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))),
% 3.57/0.98    inference(cnf_transformation,[],[f33])).
% 3.57/0.98  
% 3.57/0.98  fof(f39,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f27])).
% 3.57/0.98  
% 3.57/0.98  fof(f6,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f16,plain,(
% 3.57/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.57/0.98    inference(ennf_transformation,[],[f6])).
% 3.57/0.98  
% 3.57/0.98  fof(f17,plain,(
% 3.57/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.57/0.98    inference(flattening,[],[f16])).
% 3.57/0.98  
% 3.57/0.98  fof(f28,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.57/0.98    inference(nnf_transformation,[],[f17])).
% 3.57/0.98  
% 3.57/0.98  fof(f29,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.57/0.98    inference(flattening,[],[f28])).
% 3.57/0.98  
% 3.57/0.98  fof(f43,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f29])).
% 3.57/0.98  
% 3.57/0.98  fof(f53,plain,(
% 3.57/0.98    v1_funct_1(sK4)),
% 3.57/0.98    inference(cnf_transformation,[],[f33])).
% 3.57/0.98  
% 3.57/0.98  fof(f57,plain,(
% 3.57/0.98    ( ! [X5] : (k1_funct_1(sK4,X5) != sK5 | ~r2_hidden(X5,sK3) | ~r2_hidden(X5,sK1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f33])).
% 3.57/0.98  
% 3.57/0.98  fof(f40,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f27])).
% 3.57/0.98  
% 3.57/0.98  fof(f51,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f30])).
% 3.57/0.98  
% 3.57/0.98  fof(f61,plain,(
% 3.57/0.98    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.57/0.98    inference(equality_resolution,[],[f51])).
% 3.57/0.98  
% 3.57/0.98  fof(f2,axiom,(
% 3.57/0.98    v1_xboole_0(k1_xboole_0)),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f35,plain,(
% 3.57/0.98    v1_xboole_0(k1_xboole_0)),
% 3.57/0.98    inference(cnf_transformation,[],[f2])).
% 3.57/0.98  
% 3.57/0.98  fof(f1,axiom,(
% 3.57/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f12,plain,(
% 3.57/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.57/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 3.57/0.98  
% 3.57/0.98  fof(f13,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.57/0.98    inference(ennf_transformation,[],[f12])).
% 3.57/0.98  
% 3.57/0.98  fof(f34,plain,(
% 3.57/0.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f13])).
% 3.57/0.98  
% 3.57/0.98  fof(f48,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f30])).
% 3.57/0.98  
% 3.57/0.98  fof(f63,plain,(
% 3.57/0.98    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.57/0.98    inference(equality_resolution,[],[f48])).
% 3.57/0.98  
% 3.57/0.98  fof(f44,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f29])).
% 3.57/0.98  
% 3.57/0.98  fof(f58,plain,(
% 3.57/0.98    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.57/0.98    inference(equality_resolution,[],[f44])).
% 3.57/0.98  
% 3.57/0.98  fof(f42,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f29])).
% 3.57/0.98  
% 3.57/0.98  cnf(c_21,negated_conjecture,
% 3.57/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.57/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_643,plain,
% 3.57/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_18,plain,
% 3.57/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.57/0.98      | k1_xboole_0 = X2 ),
% 3.57/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_646,plain,
% 3.57/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.57/0.98      | k1_xboole_0 = X1
% 3.57/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1091,plain,
% 3.57/0.98      ( k1_relset_1(sK1,sK2,sK4) = sK1
% 3.57/0.98      | sK2 = k1_xboole_0
% 3.57/0.98      | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_643,c_646]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_22,negated_conjecture,
% 3.57/0.98      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.57/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1092,plain,
% 3.57/0.98      ( ~ v1_funct_2(sK4,sK1,sK2)
% 3.57/0.98      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.57/0.98      | sK2 = k1_xboole_0 ),
% 3.57/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1091]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1544,plain,
% 3.57/0.98      ( sK2 = k1_xboole_0 | k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_1091,c_22,c_1092]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1545,plain,
% 3.57/0.98      ( k1_relset_1(sK1,sK2,sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.57/0.98      inference(renaming,[status(thm)],[c_1544]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_11,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.57/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_653,plain,
% 3.57/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1096,plain,
% 3.57/0.98      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_643,c_653]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1546,plain,
% 3.57/0.98      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.57/0.98      inference(demodulation,[status(thm)],[c_1545,c_1096]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_7,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.57/0.98      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 3.57/0.98      | ~ v1_relat_1(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_657,plain,
% 3.57/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.57/0.98      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.57/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1687,plain,
% 3.57/0.98      ( sK2 = k1_xboole_0
% 3.57/0.98      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.57/0.98      | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
% 3.57/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1546,c_657]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.57/0.98      | ~ v1_relat_1(X1)
% 3.57/0.98      | v1_relat_1(X0) ),
% 3.57/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_921,plain,
% 3.57/0.98      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK4) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_2,c_21]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3,plain,
% 3.57/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_945,plain,
% 3.57/0.98      ( v1_relat_1(sK4) ),
% 3.57/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_921,c_3]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_946,plain,
% 3.57/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_945]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2060,plain,
% 3.57/0.98      ( r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
% 3.57/0.98      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.57/0.98      | sK2 = k1_xboole_0 ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_1687,c_946]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2061,plain,
% 3.57/0.98      ( sK2 = k1_xboole_0
% 3.57/0.98      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 3.57/0.98      | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top ),
% 3.57/0.98      inference(renaming,[status(thm)],[c_2060]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_12,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.57/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_652,plain,
% 3.57/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1202,plain,
% 3.57/0.98      ( k7_relset_1(sK1,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_643,c_652]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_20,negated_conjecture,
% 3.57/0.98      ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_644,plain,
% 3.57/0.98      ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1372,plain,
% 3.57/0.98      ( r2_hidden(sK5,k9_relat_1(sK4,sK3)) = iProver_top ),
% 3.57/0.98      inference(demodulation,[status(thm)],[c_1202,c_644]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_6,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.57/0.98      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.57/0.98      | ~ v1_relat_1(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_658,plain,
% 3.57/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.57/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_9,plain,
% 3.57/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.57/0.98      | ~ v1_funct_1(X2)
% 3.57/0.98      | ~ v1_relat_1(X2)
% 3.57/0.98      | k1_funct_1(X2,X0) = X1 ),
% 3.57/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_655,plain,
% 3.57/0.98      ( k1_funct_1(X0,X1) = X2
% 3.57/0.98      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 3.57/0.98      | v1_funct_1(X0) != iProver_top
% 3.57/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2483,plain,
% 3.57/0.98      ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
% 3.57/0.98      | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
% 3.57/0.98      | v1_funct_1(X0) != iProver_top
% 3.57/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_658,c_655]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3298,plain,
% 3.57/0.98      ( k1_funct_1(sK4,sK0(sK5,sK3,sK4)) = sK5
% 3.57/0.98      | v1_funct_1(sK4) != iProver_top
% 3.57/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1372,c_2483]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_23,negated_conjecture,
% 3.57/0.98      ( v1_funct_1(sK4) ),
% 3.57/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_24,plain,
% 3.57/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3348,plain,
% 3.57/0.98      ( k1_funct_1(sK4,sK0(sK5,sK3,sK4)) = sK5 ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_3298,c_24,c_946]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_19,negated_conjecture,
% 3.57/0.98      ( ~ r2_hidden(X0,sK1)
% 3.57/0.98      | ~ r2_hidden(X0,sK3)
% 3.57/0.98      | k1_funct_1(sK4,X0) != sK5 ),
% 3.57/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_645,plain,
% 3.57/0.98      ( k1_funct_1(sK4,X0) != sK5
% 3.57/0.98      | r2_hidden(X0,sK1) != iProver_top
% 3.57/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3352,plain,
% 3.57/0.98      ( r2_hidden(sK0(sK5,sK3,sK4),sK1) != iProver_top
% 3.57/0.98      | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3348,c_645]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.57/0.98      | r2_hidden(sK0(X0,X2,X1),X2)
% 3.57/0.98      | ~ v1_relat_1(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2133,plain,
% 3.57/0.98      ( r2_hidden(sK0(sK5,sK3,sK4),sK3)
% 3.57/0.98      | ~ r2_hidden(sK5,k9_relat_1(sK4,sK3))
% 3.57/0.98      | ~ v1_relat_1(sK4) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2134,plain,
% 3.57/0.98      ( r2_hidden(sK0(sK5,sK3,sK4),sK3) = iProver_top
% 3.57/0.98      | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top
% 3.57/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2133]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3510,plain,
% 3.57/0.98      ( r2_hidden(sK0(sK5,sK3,sK4),sK1) != iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_3352,c_946,c_1372,c_2134]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3515,plain,
% 3.57/0.98      ( sK2 = k1_xboole_0
% 3.57/0.98      | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_2061,c_3510]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3968,plain,
% 3.57/0.98      ( sK2 = k1_xboole_0 ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_3515,c_1372]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3973,plain,
% 3.57/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.57/0.98      inference(demodulation,[status(thm)],[c_3968,c_643]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_14,plain,
% 3.57/0.98      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.57/0.98      | k1_xboole_0 = X1
% 3.57/0.98      | k1_xboole_0 = X0 ),
% 3.57/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_650,plain,
% 3.57/0.98      ( k1_xboole_0 = X0
% 3.57/0.98      | k1_xboole_0 = X1
% 3.57/0.98      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 3.57/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4098,plain,
% 3.57/0.98      ( sK1 = k1_xboole_0
% 3.57/0.98      | sK4 = k1_xboole_0
% 3.57/0.98      | v1_funct_2(sK4,sK1,k1_xboole_0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3973,c_650]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_25,plain,
% 3.57/0.98      ( v1_funct_2(sK4,sK1,sK2) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_223,plain,( X0 = X0 ),theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_250,plain,
% 3.57/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_223]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1052,plain,
% 3.57/0.98      ( sK4 = sK4 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_223]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_236,plain,
% 3.57/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.57/0.98      | v1_funct_2(X3,X4,X5)
% 3.57/0.98      | X3 != X0
% 3.57/0.98      | X4 != X1
% 3.57/0.98      | X5 != X2 ),
% 3.57/0.98      theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_966,plain,
% 3.57/0.98      ( v1_funct_2(X0,X1,X2)
% 3.57/0.98      | ~ v1_funct_2(sK4,sK1,sK2)
% 3.57/0.98      | X2 != sK2
% 3.57/0.98      | X1 != sK1
% 3.57/0.98      | X0 != sK4 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_236]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1126,plain,
% 3.57/0.98      ( v1_funct_2(sK4,X0,X1)
% 3.57/0.98      | ~ v1_funct_2(sK4,sK1,sK2)
% 3.57/0.98      | X1 != sK2
% 3.57/0.98      | X0 != sK1
% 3.57/0.98      | sK4 != sK4 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_966]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1284,plain,
% 3.57/0.98      ( v1_funct_2(sK4,sK1,X0)
% 3.57/0.98      | ~ v1_funct_2(sK4,sK1,sK2)
% 3.57/0.98      | X0 != sK2
% 3.57/0.98      | sK1 != sK1
% 3.57/0.98      | sK4 != sK4 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1126]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1286,plain,
% 3.57/0.98      ( X0 != sK2
% 3.57/0.98      | sK1 != sK1
% 3.57/0.98      | sK4 != sK4
% 3.57/0.98      | v1_funct_2(sK4,sK1,X0) = iProver_top
% 3.57/0.98      | v1_funct_2(sK4,sK1,sK2) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1284]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1288,plain,
% 3.57/0.98      ( sK1 != sK1
% 3.57/0.98      | sK4 != sK4
% 3.57/0.98      | k1_xboole_0 != sK2
% 3.57/0.98      | v1_funct_2(sK4,sK1,sK2) != iProver_top
% 3.57/0.98      | v1_funct_2(sK4,sK1,k1_xboole_0) = iProver_top ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1286]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1285,plain,
% 3.57/0.98      ( sK1 = sK1 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_223]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_224,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1505,plain,
% 3.57/0.98      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_224]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1506,plain,
% 3.57/0.98      ( sK2 != k1_xboole_0
% 3.57/0.98      | k1_xboole_0 = sK2
% 3.57/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1505]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4163,plain,
% 3.57/0.98      ( sK4 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_4098,c_25,c_250,c_1052,c_1288,c_1285,c_1372,c_1506,
% 3.57/0.98                 c_3515]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4164,plain,
% 3.57/0.98      ( sK1 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.57/0.98      inference(renaming,[status(thm)],[c_4163]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4169,plain,
% 3.57/0.98      ( sK4 = k1_xboole_0
% 3.57/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_4164,c_3973]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1,plain,
% 3.57/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.57/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_0,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_664,plain,
% 3.57/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.57/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1811,plain,
% 3.57/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.57/0.98      | v1_relat_1(X1) != iProver_top
% 3.57/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_658,c_664]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2238,plain,
% 3.57/0.98      ( v1_relat_1(sK4) != iProver_top
% 3.57/0.98      | v1_xboole_0(sK4) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1372,c_1811]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2261,plain,
% 3.57/0.98      ( ~ v1_relat_1(sK4) | ~ v1_xboole_0(sK4) ),
% 3.57/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2238]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_226,plain,
% 3.57/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.57/0.98      theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4657,plain,
% 3.57/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_226]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4659,plain,
% 3.57/0.98      ( v1_xboole_0(sK4)
% 3.57/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 3.57/0.98      | sK4 != k1_xboole_0 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_4657]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5036,plain,
% 3.57/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_4169,c_1,c_945,c_2261,c_4659]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5043,plain,
% 3.57/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_5036,c_653]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_17,plain,
% 3.57/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.57/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.57/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.57/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_647,plain,
% 3.57/0.98      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 3.57/0.98      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 3.57/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5045,plain,
% 3.57/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 3.57/0.98      | v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_5036,c_647]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5052,plain,
% 3.57/0.98      ( k1_relat_1(sK4) = k1_xboole_0
% 3.57/0.98      | v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.57/0.98      inference(demodulation,[status(thm)],[c_5043,c_5045]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_642,plain,
% 3.57/0.98      ( v1_funct_2(sK4,sK1,sK2) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3974,plain,
% 3.57/0.98      ( v1_funct_2(sK4,sK1,k1_xboole_0) = iProver_top ),
% 3.57/0.98      inference(demodulation,[status(thm)],[c_3968,c_642]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4170,plain,
% 3.57/0.98      ( sK4 = k1_xboole_0
% 3.57/0.98      | v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_4164,c_3974]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5229,plain,
% 3.57/0.98      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_5052,c_1,c_945,c_2261,c_4170,c_4659]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_8,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.57/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.57/0.98      | ~ v1_funct_1(X1)
% 3.57/0.98      | ~ v1_relat_1(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_656,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 3.57/0.98      | v1_funct_1(X1) != iProver_top
% 3.57/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3351,plain,
% 3.57/0.98      ( r2_hidden(sK0(sK5,sK3,sK4),k1_relat_1(sK4)) != iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(sK0(sK5,sK3,sK4),sK5),sK4) = iProver_top
% 3.57/0.98      | v1_funct_1(sK4) != iProver_top
% 3.57/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3348,c_656]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2131,plain,
% 3.57/0.98      ( r2_hidden(k4_tarski(sK0(sK5,sK3,sK4),sK5),sK4)
% 3.57/0.98      | ~ r2_hidden(sK5,k9_relat_1(sK4,sK3))
% 3.57/0.98      | ~ v1_relat_1(sK4) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2138,plain,
% 3.57/0.98      ( r2_hidden(k4_tarski(sK0(sK5,sK3,sK4),sK5),sK4) = iProver_top
% 3.57/0.98      | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top
% 3.57/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2131]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3888,plain,
% 3.57/0.98      ( r2_hidden(k4_tarski(sK0(sK5,sK3,sK4),sK5),sK4) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_3351,c_946,c_1372,c_2138]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_10,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(X1))
% 3.57/0.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.57/0.98      | ~ v1_funct_1(X1)
% 3.57/0.98      | ~ v1_relat_1(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_654,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 3.57/0.98      | v1_funct_1(X1) != iProver_top
% 3.57/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3895,plain,
% 3.57/0.98      ( r2_hidden(sK0(sK5,sK3,sK4),k1_relat_1(sK4)) = iProver_top
% 3.57/0.98      | v1_funct_1(sK4) != iProver_top
% 3.57/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3888,c_654]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2132,plain,
% 3.57/0.98      ( r2_hidden(sK0(sK5,sK3,sK4),k1_relat_1(sK4))
% 3.57/0.98      | ~ r2_hidden(sK5,k9_relat_1(sK4,sK3))
% 3.57/0.98      | ~ v1_relat_1(sK4) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2136,plain,
% 3.57/0.98      ( r2_hidden(sK0(sK5,sK3,sK4),k1_relat_1(sK4)) = iProver_top
% 3.57/0.98      | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top
% 3.57/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2132]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4597,plain,
% 3.57/0.98      ( r2_hidden(sK0(sK5,sK3,sK4),k1_relat_1(sK4)) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_3895,c_946,c_1372,c_2136]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5233,plain,
% 3.57/0.98      ( r2_hidden(sK0(sK5,sK3,sK4),k1_xboole_0) = iProver_top ),
% 3.57/0.98      inference(demodulation,[status(thm)],[c_5229,c_4597]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4171,plain,
% 3.57/0.98      ( sK4 = k1_xboole_0
% 3.57/0.98      | r2_hidden(sK0(sK5,sK3,sK4),k1_xboole_0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_4164,c_3510]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(contradiction,plain,
% 3.57/0.98      ( $false ),
% 3.57/0.98      inference(minisat,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_5233,c_4659,c_4171,c_2261,c_945,c_1]) ).
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  ------                               Statistics
% 3.57/0.98  
% 3.57/0.98  ------ Selected
% 3.57/0.98  
% 3.57/0.98  total_time:                             0.168
% 3.57/0.98  
%------------------------------------------------------------------------------

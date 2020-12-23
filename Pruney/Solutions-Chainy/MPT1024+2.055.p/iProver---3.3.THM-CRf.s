%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:58 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 467 expanded)
%              Number of clauses        :  100 ( 178 expanded)
%              Number of leaves         :   18 ( 104 expanded)
%              Depth                    :   19
%              Number of atoms          :  483 (2005 expanded)
%              Number of equality atoms :  161 ( 392 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

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
    inference(nnf_transformation,[],[f20])).

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
    inference(flattening,[],[f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f37,plain,
    ( ! [X5] :
        ( k1_funct_1(sK4,X5) != sK5
        | ~ r2_hidden(X5,sK3)
        | ~ r2_hidden(X5,sK1) )
    & r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f27,f36,f35])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    ! [X5] :
      ( k1_funct_1(sK4,X5) != sK5
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12730,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(sK5,X0,X2),X0)
    | r2_hidden(sK0(sK5,X0,X2),X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_37628,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK0(sK5,X0,X1),X0)
    | r2_hidden(sK0(sK5,X0,X1),sK3) ),
    inference(instantiation,[status(thm)],[c_12730])).

cnf(c_37630,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3))
    | r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),sK3)
    | ~ r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_37628])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_293,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_294,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_34898,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_338,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_339,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_21334,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK5,X0,X1),sK5),sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(sK5,X0,X1)) = sK5 ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_21345,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK5,k1_xboole_0,k1_xboole_0),sK5),sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(sK5,k1_xboole_0,k1_xboole_0)) = sK5 ),
    inference(instantiation,[status(thm)],[c_21334])).

cnf(c_13716,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(k4_tarski(sK0(sK5,X2,X0),sK5),X0)
    | r2_hidden(k4_tarski(sK0(sK5,X2,X0),sK5),X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_21333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | ~ r2_hidden(k4_tarski(sK0(sK5,X1,X0),sK5),X0)
    | r2_hidden(k4_tarski(sK0(sK5,X1,X0),sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_13716])).

cnf(c_21337,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4))
    | r2_hidden(k4_tarski(sK0(sK5,k1_xboole_0,k1_xboole_0),sK5),sK4)
    | ~ r2_hidden(k4_tarski(sK0(sK5,k1_xboole_0,k1_xboole_0),sK5),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_21333])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,X0) != sK5 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_17940,plain,
    ( ~ r2_hidden(sK0(sK5,X0,X1),sK1)
    | ~ r2_hidden(sK0(sK5,X0,X1),sK3)
    | k1_funct_1(sK4,sK0(sK5,X0,X1)) != sK5 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_17946,plain,
    ( ~ r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),sK1)
    | ~ r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),sK3)
    | k1_funct_1(sK4,sK0(sK5,k1_xboole_0,k1_xboole_0)) != sK5 ),
    inference(instantiation,[status(thm)],[c_17940])).

cnf(c_17939,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK0(sK5,X0,X1),X0)
    | r2_hidden(sK0(sK5,X0,X1),sK1) ),
    inference(instantiation,[status(thm)],[c_12730])).

cnf(c_17942,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),sK1)
    | ~ r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_17939])).

cnf(c_16976,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_5470,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k9_relat_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_5474,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k9_relat_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_5470])).

cnf(c_5284,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2927,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,X0,X1),sK5),X1)
    | ~ r2_hidden(sK5,k9_relat_1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2943,plain,
    ( r2_hidden(k4_tarski(sK0(sK5,k1_xboole_0,k1_xboole_0),sK5),k1_xboole_0)
    | ~ r2_hidden(sK5,k9_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2927])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2929,plain,
    ( r2_hidden(sK0(sK5,X0,X1),X0)
    | ~ r2_hidden(sK5,k9_relat_1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2935,plain,
    ( r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK5,k9_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2929])).

cnf(c_1160,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK5,X0)
    | r2_hidden(sK5,X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2926,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k9_relat_1(X1,X2)))
    | ~ r2_hidden(sK5,X0)
    | r2_hidden(sK5,k9_relat_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_2931,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k9_relat_1(k1_xboole_0,k1_xboole_0)))
    | r2_hidden(sK5,k9_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2926])).

cnf(c_912,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_411,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_413,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_23])).

cnf(c_904,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_908,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1292,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_904,c_908])).

cnf(c_1336,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_413,c_1292])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_910,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1737,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1336,c_910])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_915,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1297,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_904,c_915])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_914,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1489,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1297,c_914])).

cnf(c_2239,plain,
    ( r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1737,c_1489])).

cnf(c_2240,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2239])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_907,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1333,plain,
    ( k7_relset_1(sK1,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_904,c_907])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_905,plain,
    ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1430,plain,
    ( r2_hidden(sK5,k9_relat_1(sK4,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1333,c_905])).

cnf(c_911,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_900,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_1746,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_900])).

cnf(c_2003,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1746,c_1489])).

cnf(c_2004,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2003])).

cnf(c_2013,plain,
    ( k1_funct_1(sK4,sK0(sK5,sK3,sK4)) = sK5 ),
    inference(superposition,[status(thm)],[c_1430,c_2004])).

cnf(c_906,plain,
    ( k1_funct_1(sK4,X0) != sK5
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2036,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),sK1) != iProver_top
    | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_906])).

cnf(c_2248,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top
    | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_2036])).

cnf(c_2251,plain,
    ( r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2248,c_1430])).

cnf(c_2252,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2251])).

cnf(c_2257,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_2252])).

cnf(c_565,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1163,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,X2)
    | X1 != X2
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_1451,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,sK2)
    | X1 != sK2
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_1692,plain,
    ( r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,sK2)
    | X0 != sK2
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_1694,plain,
    ( ~ r2_hidden(sK5,sK2)
    | r2_hidden(sK5,k1_xboole_0)
    | sK5 != sK5
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_1490,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1489])).

cnf(c_564,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1279,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_1280,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1108,plain,
    ( m1_subset_1(k7_relset_1(sK1,sK2,sK4,X0),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1214,plain,
    ( m1_subset_1(k7_relset_1(sK1,sK2,sK4,sK3),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_1074,plain,
    ( ~ m1_subset_1(k7_relset_1(sK1,sK2,sK4,sK3),k1_zfmisc_1(X0))
    | r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1213,plain,
    ( ~ m1_subset_1(k7_relset_1(sK1,sK2,sK4,sK3),k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))
    | r2_hidden(sK5,sK2) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_563,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1175,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_1085,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_1089,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_1064,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1066,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1064])).

cnf(c_586,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_82,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37630,c_34898,c_21345,c_21337,c_17946,c_17942,c_16976,c_5474,c_5284,c_2943,c_2935,c_2931,c_2257,c_1694,c_1490,c_1489,c_1430,c_1280,c_1214,c_1213,c_1175,c_1089,c_1066,c_586,c_82,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.73/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.49  
% 7.73/1.49  ------  iProver source info
% 7.73/1.49  
% 7.73/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.49  git: non_committed_changes: false
% 7.73/1.49  git: last_make_outside_of_git: false
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options
% 7.73/1.49  
% 7.73/1.49  --out_options                           all
% 7.73/1.49  --tptp_safe_out                         true
% 7.73/1.49  --problem_path                          ""
% 7.73/1.49  --include_path                          ""
% 7.73/1.49  --clausifier                            res/vclausify_rel
% 7.73/1.49  --clausifier_options                    --mode clausify
% 7.73/1.49  --stdin                                 false
% 7.73/1.49  --stats_out                             all
% 7.73/1.49  
% 7.73/1.49  ------ General Options
% 7.73/1.49  
% 7.73/1.49  --fof                                   false
% 7.73/1.49  --time_out_real                         305.
% 7.73/1.49  --time_out_virtual                      -1.
% 7.73/1.49  --symbol_type_check                     false
% 7.73/1.49  --clausify_out                          false
% 7.73/1.49  --sig_cnt_out                           false
% 7.73/1.49  --trig_cnt_out                          false
% 7.73/1.49  --trig_cnt_out_tolerance                1.
% 7.73/1.49  --trig_cnt_out_sk_spl                   false
% 7.73/1.49  --abstr_cl_out                          false
% 7.73/1.49  
% 7.73/1.49  ------ Global Options
% 7.73/1.49  
% 7.73/1.49  --schedule                              default
% 7.73/1.49  --add_important_lit                     false
% 7.73/1.49  --prop_solver_per_cl                    1000
% 7.73/1.49  --min_unsat_core                        false
% 7.73/1.49  --soft_assumptions                      false
% 7.73/1.49  --soft_lemma_size                       3
% 7.73/1.49  --prop_impl_unit_size                   0
% 7.73/1.49  --prop_impl_unit                        []
% 7.73/1.49  --share_sel_clauses                     true
% 7.73/1.49  --reset_solvers                         false
% 7.73/1.49  --bc_imp_inh                            [conj_cone]
% 7.73/1.49  --conj_cone_tolerance                   3.
% 7.73/1.49  --extra_neg_conj                        none
% 7.73/1.49  --large_theory_mode                     true
% 7.73/1.49  --prolific_symb_bound                   200
% 7.73/1.49  --lt_threshold                          2000
% 7.73/1.49  --clause_weak_htbl                      true
% 7.73/1.49  --gc_record_bc_elim                     false
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing Options
% 7.73/1.49  
% 7.73/1.49  --preprocessing_flag                    true
% 7.73/1.49  --time_out_prep_mult                    0.1
% 7.73/1.49  --splitting_mode                        input
% 7.73/1.49  --splitting_grd                         true
% 7.73/1.49  --splitting_cvd                         false
% 7.73/1.49  --splitting_cvd_svl                     false
% 7.73/1.49  --splitting_nvd                         32
% 7.73/1.49  --sub_typing                            true
% 7.73/1.49  --prep_gs_sim                           true
% 7.73/1.49  --prep_unflatten                        true
% 7.73/1.49  --prep_res_sim                          true
% 7.73/1.49  --prep_upred                            true
% 7.73/1.49  --prep_sem_filter                       exhaustive
% 7.73/1.49  --prep_sem_filter_out                   false
% 7.73/1.49  --pred_elim                             true
% 7.73/1.49  --res_sim_input                         true
% 7.73/1.49  --eq_ax_congr_red                       true
% 7.73/1.49  --pure_diseq_elim                       true
% 7.73/1.49  --brand_transform                       false
% 7.73/1.49  --non_eq_to_eq                          false
% 7.73/1.49  --prep_def_merge                        true
% 7.73/1.49  --prep_def_merge_prop_impl              false
% 7.73/1.49  --prep_def_merge_mbd                    true
% 7.73/1.49  --prep_def_merge_tr_red                 false
% 7.73/1.49  --prep_def_merge_tr_cl                  false
% 7.73/1.49  --smt_preprocessing                     true
% 7.73/1.49  --smt_ac_axioms                         fast
% 7.73/1.49  --preprocessed_out                      false
% 7.73/1.49  --preprocessed_stats                    false
% 7.73/1.49  
% 7.73/1.49  ------ Abstraction refinement Options
% 7.73/1.49  
% 7.73/1.49  --abstr_ref                             []
% 7.73/1.49  --abstr_ref_prep                        false
% 7.73/1.49  --abstr_ref_until_sat                   false
% 7.73/1.49  --abstr_ref_sig_restrict                funpre
% 7.73/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.49  --abstr_ref_under                       []
% 7.73/1.49  
% 7.73/1.49  ------ SAT Options
% 7.73/1.49  
% 7.73/1.49  --sat_mode                              false
% 7.73/1.49  --sat_fm_restart_options                ""
% 7.73/1.49  --sat_gr_def                            false
% 7.73/1.49  --sat_epr_types                         true
% 7.73/1.49  --sat_non_cyclic_types                  false
% 7.73/1.49  --sat_finite_models                     false
% 7.73/1.49  --sat_fm_lemmas                         false
% 7.73/1.49  --sat_fm_prep                           false
% 7.73/1.49  --sat_fm_uc_incr                        true
% 7.73/1.49  --sat_out_model                         small
% 7.73/1.49  --sat_out_clauses                       false
% 7.73/1.49  
% 7.73/1.49  ------ QBF Options
% 7.73/1.49  
% 7.73/1.49  --qbf_mode                              false
% 7.73/1.49  --qbf_elim_univ                         false
% 7.73/1.49  --qbf_dom_inst                          none
% 7.73/1.49  --qbf_dom_pre_inst                      false
% 7.73/1.49  --qbf_sk_in                             false
% 7.73/1.49  --qbf_pred_elim                         true
% 7.73/1.49  --qbf_split                             512
% 7.73/1.49  
% 7.73/1.49  ------ BMC1 Options
% 7.73/1.49  
% 7.73/1.49  --bmc1_incremental                      false
% 7.73/1.49  --bmc1_axioms                           reachable_all
% 7.73/1.49  --bmc1_min_bound                        0
% 7.73/1.49  --bmc1_max_bound                        -1
% 7.73/1.49  --bmc1_max_bound_default                -1
% 7.73/1.49  --bmc1_symbol_reachability              true
% 7.73/1.49  --bmc1_property_lemmas                  false
% 7.73/1.49  --bmc1_k_induction                      false
% 7.73/1.49  --bmc1_non_equiv_states                 false
% 7.73/1.49  --bmc1_deadlock                         false
% 7.73/1.49  --bmc1_ucm                              false
% 7.73/1.49  --bmc1_add_unsat_core                   none
% 7.73/1.49  --bmc1_unsat_core_children              false
% 7.73/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.49  --bmc1_out_stat                         full
% 7.73/1.49  --bmc1_ground_init                      false
% 7.73/1.49  --bmc1_pre_inst_next_state              false
% 7.73/1.49  --bmc1_pre_inst_state                   false
% 7.73/1.49  --bmc1_pre_inst_reach_state             false
% 7.73/1.49  --bmc1_out_unsat_core                   false
% 7.73/1.49  --bmc1_aig_witness_out                  false
% 7.73/1.49  --bmc1_verbose                          false
% 7.73/1.49  --bmc1_dump_clauses_tptp                false
% 7.73/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.49  --bmc1_dump_file                        -
% 7.73/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.49  --bmc1_ucm_extend_mode                  1
% 7.73/1.49  --bmc1_ucm_init_mode                    2
% 7.73/1.49  --bmc1_ucm_cone_mode                    none
% 7.73/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.49  --bmc1_ucm_relax_model                  4
% 7.73/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.49  --bmc1_ucm_layered_model                none
% 7.73/1.49  --bmc1_ucm_max_lemma_size               10
% 7.73/1.49  
% 7.73/1.49  ------ AIG Options
% 7.73/1.49  
% 7.73/1.49  --aig_mode                              false
% 7.73/1.49  
% 7.73/1.49  ------ Instantiation Options
% 7.73/1.49  
% 7.73/1.49  --instantiation_flag                    true
% 7.73/1.49  --inst_sos_flag                         false
% 7.73/1.49  --inst_sos_phase                        true
% 7.73/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel_side                     num_symb
% 7.73/1.49  --inst_solver_per_active                1400
% 7.73/1.49  --inst_solver_calls_frac                1.
% 7.73/1.49  --inst_passive_queue_type               priority_queues
% 7.73/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.49  --inst_passive_queues_freq              [25;2]
% 7.73/1.49  --inst_dismatching                      true
% 7.73/1.49  --inst_eager_unprocessed_to_passive     true
% 7.73/1.49  --inst_prop_sim_given                   true
% 7.73/1.49  --inst_prop_sim_new                     false
% 7.73/1.49  --inst_subs_new                         false
% 7.73/1.49  --inst_eq_res_simp                      false
% 7.73/1.49  --inst_subs_given                       false
% 7.73/1.49  --inst_orphan_elimination               true
% 7.73/1.49  --inst_learning_loop_flag               true
% 7.73/1.49  --inst_learning_start                   3000
% 7.73/1.49  --inst_learning_factor                  2
% 7.73/1.49  --inst_start_prop_sim_after_learn       3
% 7.73/1.49  --inst_sel_renew                        solver
% 7.73/1.49  --inst_lit_activity_flag                true
% 7.73/1.49  --inst_restr_to_given                   false
% 7.73/1.49  --inst_activity_threshold               500
% 7.73/1.49  --inst_out_proof                        true
% 7.73/1.49  
% 7.73/1.49  ------ Resolution Options
% 7.73/1.49  
% 7.73/1.49  --resolution_flag                       true
% 7.73/1.49  --res_lit_sel                           adaptive
% 7.73/1.49  --res_lit_sel_side                      none
% 7.73/1.49  --res_ordering                          kbo
% 7.73/1.49  --res_to_prop_solver                    active
% 7.73/1.49  --res_prop_simpl_new                    false
% 7.73/1.49  --res_prop_simpl_given                  true
% 7.73/1.49  --res_passive_queue_type                priority_queues
% 7.73/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.49  --res_passive_queues_freq               [15;5]
% 7.73/1.49  --res_forward_subs                      full
% 7.73/1.49  --res_backward_subs                     full
% 7.73/1.49  --res_forward_subs_resolution           true
% 7.73/1.49  --res_backward_subs_resolution          true
% 7.73/1.49  --res_orphan_elimination                true
% 7.73/1.49  --res_time_limit                        2.
% 7.73/1.49  --res_out_proof                         true
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Options
% 7.73/1.49  
% 7.73/1.49  --superposition_flag                    true
% 7.73/1.49  --sup_passive_queue_type                priority_queues
% 7.73/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.49  --demod_completeness_check              fast
% 7.73/1.49  --demod_use_ground                      true
% 7.73/1.49  --sup_to_prop_solver                    passive
% 7.73/1.49  --sup_prop_simpl_new                    true
% 7.73/1.49  --sup_prop_simpl_given                  true
% 7.73/1.49  --sup_fun_splitting                     false
% 7.73/1.49  --sup_smt_interval                      50000
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Simplification Setup
% 7.73/1.49  
% 7.73/1.49  --sup_indices_passive                   []
% 7.73/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.49  --sup_full_bw                           [BwDemod]
% 7.73/1.49  --sup_immed_triv                        [TrivRules]
% 7.73/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.49  --sup_immed_bw_main                     []
% 7.73/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.49  
% 7.73/1.49  ------ Combination Options
% 7.73/1.49  
% 7.73/1.49  --comb_res_mult                         3
% 7.73/1.49  --comb_sup_mult                         2
% 7.73/1.49  --comb_inst_mult                        10
% 7.73/1.49  
% 7.73/1.49  ------ Debug Options
% 7.73/1.49  
% 7.73/1.49  --dbg_backtrace                         false
% 7.73/1.49  --dbg_dump_prop_clauses                 false
% 7.73/1.49  --dbg_dump_prop_clauses_file            -
% 7.73/1.49  --dbg_out_stat                          false
% 7.73/1.49  ------ Parsing...
% 7.73/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  ------ Proving...
% 7.73/1.49  ------ Problem Properties 
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  clauses                                 20
% 7.73/1.49  conjectures                             3
% 7.73/1.49  EPR                                     0
% 7.73/1.49  Horn                                    18
% 7.73/1.49  unary                                   4
% 7.73/1.49  binary                                  4
% 7.73/1.49  lits                                    51
% 7.73/1.49  lits eq                                 11
% 7.73/1.49  fd_pure                                 0
% 7.73/1.49  fd_pseudo                               0
% 7.73/1.49  fd_cond                                 0
% 7.73/1.49  fd_pseudo_cond                          1
% 7.73/1.49  AC symbols                              0
% 7.73/1.49  
% 7.73/1.49  ------ Schedule dynamic 5 is on 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  Current options:
% 7.73/1.49  ------ 
% 7.73/1.49  
% 7.73/1.49  ------ Input Options
% 7.73/1.49  
% 7.73/1.49  --out_options                           all
% 7.73/1.49  --tptp_safe_out                         true
% 7.73/1.49  --problem_path                          ""
% 7.73/1.49  --include_path                          ""
% 7.73/1.49  --clausifier                            res/vclausify_rel
% 7.73/1.49  --clausifier_options                    --mode clausify
% 7.73/1.49  --stdin                                 false
% 7.73/1.49  --stats_out                             all
% 7.73/1.49  
% 7.73/1.49  ------ General Options
% 7.73/1.49  
% 7.73/1.49  --fof                                   false
% 7.73/1.49  --time_out_real                         305.
% 7.73/1.49  --time_out_virtual                      -1.
% 7.73/1.49  --symbol_type_check                     false
% 7.73/1.49  --clausify_out                          false
% 7.73/1.49  --sig_cnt_out                           false
% 7.73/1.49  --trig_cnt_out                          false
% 7.73/1.49  --trig_cnt_out_tolerance                1.
% 7.73/1.49  --trig_cnt_out_sk_spl                   false
% 7.73/1.49  --abstr_cl_out                          false
% 7.73/1.49  
% 7.73/1.49  ------ Global Options
% 7.73/1.49  
% 7.73/1.49  --schedule                              default
% 7.73/1.49  --add_important_lit                     false
% 7.73/1.49  --prop_solver_per_cl                    1000
% 7.73/1.49  --min_unsat_core                        false
% 7.73/1.49  --soft_assumptions                      false
% 7.73/1.49  --soft_lemma_size                       3
% 7.73/1.49  --prop_impl_unit_size                   0
% 7.73/1.49  --prop_impl_unit                        []
% 7.73/1.49  --share_sel_clauses                     true
% 7.73/1.49  --reset_solvers                         false
% 7.73/1.49  --bc_imp_inh                            [conj_cone]
% 7.73/1.49  --conj_cone_tolerance                   3.
% 7.73/1.49  --extra_neg_conj                        none
% 7.73/1.49  --large_theory_mode                     true
% 7.73/1.49  --prolific_symb_bound                   200
% 7.73/1.49  --lt_threshold                          2000
% 7.73/1.49  --clause_weak_htbl                      true
% 7.73/1.49  --gc_record_bc_elim                     false
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing Options
% 7.73/1.49  
% 7.73/1.49  --preprocessing_flag                    true
% 7.73/1.49  --time_out_prep_mult                    0.1
% 7.73/1.49  --splitting_mode                        input
% 7.73/1.49  --splitting_grd                         true
% 7.73/1.49  --splitting_cvd                         false
% 7.73/1.49  --splitting_cvd_svl                     false
% 7.73/1.49  --splitting_nvd                         32
% 7.73/1.49  --sub_typing                            true
% 7.73/1.49  --prep_gs_sim                           true
% 7.73/1.49  --prep_unflatten                        true
% 7.73/1.49  --prep_res_sim                          true
% 7.73/1.49  --prep_upred                            true
% 7.73/1.49  --prep_sem_filter                       exhaustive
% 7.73/1.49  --prep_sem_filter_out                   false
% 7.73/1.49  --pred_elim                             true
% 7.73/1.49  --res_sim_input                         true
% 7.73/1.49  --eq_ax_congr_red                       true
% 7.73/1.49  --pure_diseq_elim                       true
% 7.73/1.49  --brand_transform                       false
% 7.73/1.49  --non_eq_to_eq                          false
% 7.73/1.49  --prep_def_merge                        true
% 7.73/1.49  --prep_def_merge_prop_impl              false
% 7.73/1.49  --prep_def_merge_mbd                    true
% 7.73/1.49  --prep_def_merge_tr_red                 false
% 7.73/1.49  --prep_def_merge_tr_cl                  false
% 7.73/1.49  --smt_preprocessing                     true
% 7.73/1.49  --smt_ac_axioms                         fast
% 7.73/1.49  --preprocessed_out                      false
% 7.73/1.49  --preprocessed_stats                    false
% 7.73/1.49  
% 7.73/1.49  ------ Abstraction refinement Options
% 7.73/1.49  
% 7.73/1.49  --abstr_ref                             []
% 7.73/1.49  --abstr_ref_prep                        false
% 7.73/1.49  --abstr_ref_until_sat                   false
% 7.73/1.49  --abstr_ref_sig_restrict                funpre
% 7.73/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.49  --abstr_ref_under                       []
% 7.73/1.49  
% 7.73/1.49  ------ SAT Options
% 7.73/1.49  
% 7.73/1.49  --sat_mode                              false
% 7.73/1.49  --sat_fm_restart_options                ""
% 7.73/1.49  --sat_gr_def                            false
% 7.73/1.49  --sat_epr_types                         true
% 7.73/1.49  --sat_non_cyclic_types                  false
% 7.73/1.49  --sat_finite_models                     false
% 7.73/1.49  --sat_fm_lemmas                         false
% 7.73/1.49  --sat_fm_prep                           false
% 7.73/1.49  --sat_fm_uc_incr                        true
% 7.73/1.49  --sat_out_model                         small
% 7.73/1.49  --sat_out_clauses                       false
% 7.73/1.49  
% 7.73/1.49  ------ QBF Options
% 7.73/1.49  
% 7.73/1.49  --qbf_mode                              false
% 7.73/1.49  --qbf_elim_univ                         false
% 7.73/1.49  --qbf_dom_inst                          none
% 7.73/1.49  --qbf_dom_pre_inst                      false
% 7.73/1.49  --qbf_sk_in                             false
% 7.73/1.49  --qbf_pred_elim                         true
% 7.73/1.49  --qbf_split                             512
% 7.73/1.49  
% 7.73/1.49  ------ BMC1 Options
% 7.73/1.49  
% 7.73/1.49  --bmc1_incremental                      false
% 7.73/1.49  --bmc1_axioms                           reachable_all
% 7.73/1.49  --bmc1_min_bound                        0
% 7.73/1.49  --bmc1_max_bound                        -1
% 7.73/1.49  --bmc1_max_bound_default                -1
% 7.73/1.49  --bmc1_symbol_reachability              true
% 7.73/1.49  --bmc1_property_lemmas                  false
% 7.73/1.49  --bmc1_k_induction                      false
% 7.73/1.49  --bmc1_non_equiv_states                 false
% 7.73/1.49  --bmc1_deadlock                         false
% 7.73/1.49  --bmc1_ucm                              false
% 7.73/1.49  --bmc1_add_unsat_core                   none
% 7.73/1.49  --bmc1_unsat_core_children              false
% 7.73/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.49  --bmc1_out_stat                         full
% 7.73/1.49  --bmc1_ground_init                      false
% 7.73/1.49  --bmc1_pre_inst_next_state              false
% 7.73/1.49  --bmc1_pre_inst_state                   false
% 7.73/1.49  --bmc1_pre_inst_reach_state             false
% 7.73/1.49  --bmc1_out_unsat_core                   false
% 7.73/1.49  --bmc1_aig_witness_out                  false
% 7.73/1.49  --bmc1_verbose                          false
% 7.73/1.49  --bmc1_dump_clauses_tptp                false
% 7.73/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.49  --bmc1_dump_file                        -
% 7.73/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.49  --bmc1_ucm_extend_mode                  1
% 7.73/1.49  --bmc1_ucm_init_mode                    2
% 7.73/1.49  --bmc1_ucm_cone_mode                    none
% 7.73/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.49  --bmc1_ucm_relax_model                  4
% 7.73/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.49  --bmc1_ucm_layered_model                none
% 7.73/1.49  --bmc1_ucm_max_lemma_size               10
% 7.73/1.49  
% 7.73/1.49  ------ AIG Options
% 7.73/1.49  
% 7.73/1.49  --aig_mode                              false
% 7.73/1.49  
% 7.73/1.49  ------ Instantiation Options
% 7.73/1.49  
% 7.73/1.49  --instantiation_flag                    true
% 7.73/1.49  --inst_sos_flag                         false
% 7.73/1.49  --inst_sos_phase                        true
% 7.73/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.49  --inst_lit_sel_side                     none
% 7.73/1.49  --inst_solver_per_active                1400
% 7.73/1.49  --inst_solver_calls_frac                1.
% 7.73/1.49  --inst_passive_queue_type               priority_queues
% 7.73/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.49  --inst_passive_queues_freq              [25;2]
% 7.73/1.49  --inst_dismatching                      true
% 7.73/1.49  --inst_eager_unprocessed_to_passive     true
% 7.73/1.49  --inst_prop_sim_given                   true
% 7.73/1.49  --inst_prop_sim_new                     false
% 7.73/1.49  --inst_subs_new                         false
% 7.73/1.49  --inst_eq_res_simp                      false
% 7.73/1.49  --inst_subs_given                       false
% 7.73/1.49  --inst_orphan_elimination               true
% 7.73/1.49  --inst_learning_loop_flag               true
% 7.73/1.49  --inst_learning_start                   3000
% 7.73/1.49  --inst_learning_factor                  2
% 7.73/1.49  --inst_start_prop_sim_after_learn       3
% 7.73/1.49  --inst_sel_renew                        solver
% 7.73/1.49  --inst_lit_activity_flag                true
% 7.73/1.49  --inst_restr_to_given                   false
% 7.73/1.49  --inst_activity_threshold               500
% 7.73/1.49  --inst_out_proof                        true
% 7.73/1.49  
% 7.73/1.49  ------ Resolution Options
% 7.73/1.49  
% 7.73/1.49  --resolution_flag                       false
% 7.73/1.49  --res_lit_sel                           adaptive
% 7.73/1.49  --res_lit_sel_side                      none
% 7.73/1.49  --res_ordering                          kbo
% 7.73/1.49  --res_to_prop_solver                    active
% 7.73/1.49  --res_prop_simpl_new                    false
% 7.73/1.49  --res_prop_simpl_given                  true
% 7.73/1.49  --res_passive_queue_type                priority_queues
% 7.73/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.49  --res_passive_queues_freq               [15;5]
% 7.73/1.49  --res_forward_subs                      full
% 7.73/1.49  --res_backward_subs                     full
% 7.73/1.49  --res_forward_subs_resolution           true
% 7.73/1.49  --res_backward_subs_resolution          true
% 7.73/1.49  --res_orphan_elimination                true
% 7.73/1.49  --res_time_limit                        2.
% 7.73/1.49  --res_out_proof                         true
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Options
% 7.73/1.49  
% 7.73/1.49  --superposition_flag                    true
% 7.73/1.49  --sup_passive_queue_type                priority_queues
% 7.73/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.49  --demod_completeness_check              fast
% 7.73/1.49  --demod_use_ground                      true
% 7.73/1.49  --sup_to_prop_solver                    passive
% 7.73/1.49  --sup_prop_simpl_new                    true
% 7.73/1.49  --sup_prop_simpl_given                  true
% 7.73/1.49  --sup_fun_splitting                     false
% 7.73/1.49  --sup_smt_interval                      50000
% 7.73/1.49  
% 7.73/1.49  ------ Superposition Simplification Setup
% 7.73/1.49  
% 7.73/1.49  --sup_indices_passive                   []
% 7.73/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.49  --sup_full_bw                           [BwDemod]
% 7.73/1.49  --sup_immed_triv                        [TrivRules]
% 7.73/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.49  --sup_immed_bw_main                     []
% 7.73/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.49  
% 7.73/1.49  ------ Combination Options
% 7.73/1.49  
% 7.73/1.49  --comb_res_mult                         3
% 7.73/1.49  --comb_sup_mult                         2
% 7.73/1.49  --comb_inst_mult                        10
% 7.73/1.49  
% 7.73/1.49  ------ Debug Options
% 7.73/1.49  
% 7.73/1.49  --dbg_backtrace                         false
% 7.73/1.49  --dbg_dump_prop_clauses                 false
% 7.73/1.49  --dbg_dump_prop_clauses_file            -
% 7.73/1.49  --dbg_out_stat                          false
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  % SZS status Theorem for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  fof(f2,axiom,(
% 7.73/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.73/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f15,plain,(
% 7.73/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f2])).
% 7.73/1.49  
% 7.73/1.49  fof(f39,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f15])).
% 7.73/1.49  
% 7.73/1.49  fof(f1,axiom,(
% 7.73/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.73/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f38,plain,(
% 7.73/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f1])).
% 7.73/1.49  
% 7.73/1.49  fof(f3,axiom,(
% 7.73/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.73/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f14,plain,(
% 7.73/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 7.73/1.49    inference(unused_predicate_definition_removal,[],[f3])).
% 7.73/1.49  
% 7.73/1.49  fof(f16,plain,(
% 7.73/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 7.73/1.49    inference(ennf_transformation,[],[f14])).
% 7.73/1.49  
% 7.73/1.49  fof(f40,plain,(
% 7.73/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f16])).
% 7.73/1.49  
% 7.73/1.49  fof(f7,axiom,(
% 7.73/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 7.73/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f19,plain,(
% 7.73/1.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.73/1.49    inference(ennf_transformation,[],[f7])).
% 7.73/1.49  
% 7.73/1.49  fof(f20,plain,(
% 7.73/1.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(flattening,[],[f19])).
% 7.73/1.49  
% 7.73/1.49  fof(f32,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(nnf_transformation,[],[f20])).
% 7.73/1.49  
% 7.73/1.49  fof(f33,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(flattening,[],[f32])).
% 7.73/1.49  
% 7.73/1.49  fof(f48,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f33])).
% 7.73/1.49  
% 7.73/1.49  fof(f12,conjecture,(
% 7.73/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.73/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f13,negated_conjecture,(
% 7.73/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.73/1.49    inference(negated_conjecture,[],[f12])).
% 7.73/1.49  
% 7.73/1.49  fof(f26,plain,(
% 7.73/1.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.73/1.49    inference(ennf_transformation,[],[f13])).
% 7.73/1.49  
% 7.73/1.49  fof(f27,plain,(
% 7.73/1.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.73/1.49    inference(flattening,[],[f26])).
% 7.73/1.49  
% 7.73/1.49  fof(f36,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK5 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK5,k7_relset_1(X0,X1,X3,X2)))) )),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f35,plain,(
% 7.73/1.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK4,X5) != X4 | ~r2_hidden(X5,sK3) | ~r2_hidden(X5,sK1)) & r2_hidden(X4,k7_relset_1(sK1,sK2,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f37,plain,(
% 7.73/1.49    (! [X5] : (k1_funct_1(sK4,X5) != sK5 | ~r2_hidden(X5,sK3) | ~r2_hidden(X5,sK1)) & r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f27,f36,f35])).
% 7.73/1.49  
% 7.73/1.49  fof(f59,plain,(
% 7.73/1.49    v1_funct_1(sK4)),
% 7.73/1.49    inference(cnf_transformation,[],[f37])).
% 7.73/1.49  
% 7.73/1.49  fof(f63,plain,(
% 7.73/1.49    ( ! [X5] : (k1_funct_1(sK4,X5) != sK5 | ~r2_hidden(X5,sK3) | ~r2_hidden(X5,sK1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f37])).
% 7.73/1.49  
% 7.73/1.49  fof(f6,axiom,(
% 7.73/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 7.73/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f18,plain,(
% 7.73/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(ennf_transformation,[],[f6])).
% 7.73/1.49  
% 7.73/1.49  fof(f28,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(nnf_transformation,[],[f18])).
% 7.73/1.49  
% 7.73/1.49  fof(f29,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(rectify,[],[f28])).
% 7.73/1.49  
% 7.73/1.49  fof(f30,plain,(
% 7.73/1.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f31,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 7.73/1.49  
% 7.73/1.49  fof(f44,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f31])).
% 7.73/1.49  
% 7.73/1.49  fof(f45,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f31])).
% 7.73/1.49  
% 7.73/1.49  fof(f11,axiom,(
% 7.73/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.73/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f24,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.49    inference(ennf_transformation,[],[f11])).
% 7.73/1.49  
% 7.73/1.49  fof(f25,plain,(
% 7.73/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.49    inference(flattening,[],[f24])).
% 7.73/1.49  
% 7.73/1.49  fof(f34,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.49    inference(nnf_transformation,[],[f25])).
% 7.73/1.49  
% 7.73/1.49  fof(f53,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f34])).
% 7.73/1.49  
% 7.73/1.49  fof(f60,plain,(
% 7.73/1.49    v1_funct_2(sK4,sK1,sK2)),
% 7.73/1.49    inference(cnf_transformation,[],[f37])).
% 7.73/1.49  
% 7.73/1.49  fof(f61,plain,(
% 7.73/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.73/1.49    inference(cnf_transformation,[],[f37])).
% 7.73/1.49  
% 7.73/1.49  fof(f9,axiom,(
% 7.73/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.73/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f22,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.49    inference(ennf_transformation,[],[f9])).
% 7.73/1.49  
% 7.73/1.49  fof(f51,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f22])).
% 7.73/1.49  
% 7.73/1.49  fof(f43,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f31])).
% 7.73/1.49  
% 7.73/1.49  fof(f4,axiom,(
% 7.73/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.73/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f17,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f4])).
% 7.73/1.49  
% 7.73/1.49  fof(f41,plain,(
% 7.73/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f17])).
% 7.73/1.49  
% 7.73/1.49  fof(f5,axiom,(
% 7.73/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.73/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f42,plain,(
% 7.73/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f5])).
% 7.73/1.49  
% 7.73/1.49  fof(f10,axiom,(
% 7.73/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.73/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f23,plain,(
% 7.73/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.49    inference(ennf_transformation,[],[f10])).
% 7.73/1.49  
% 7.73/1.49  fof(f52,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f23])).
% 7.73/1.49  
% 7.73/1.49  fof(f62,plain,(
% 7.73/1.49    r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))),
% 7.73/1.49    inference(cnf_transformation,[],[f37])).
% 7.73/1.49  
% 7.73/1.49  fof(f8,axiom,(
% 7.73/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 7.73/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f21,plain,(
% 7.73/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.49    inference(ennf_transformation,[],[f8])).
% 7.73/1.49  
% 7.73/1.49  fof(f50,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f21])).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.73/1.49      | ~ r2_hidden(X2,X0)
% 7.73/1.49      | r2_hidden(X2,X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12730,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.73/1.49      | ~ r2_hidden(sK0(sK5,X0,X2),X0)
% 7.73/1.49      | r2_hidden(sK0(sK5,X0,X2),X1) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_37628,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 7.73/1.49      | ~ r2_hidden(sK0(sK5,X0,X1),X0)
% 7.73/1.49      | r2_hidden(sK0(sK5,X0,X1),sK3) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_12730]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_37630,plain,
% 7.73/1.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3))
% 7.73/1.49      | r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),sK3)
% 7.73/1.49      | ~ r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_37628]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_0,plain,
% 7.73/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2,plain,
% 7.73/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_293,plain,
% 7.73/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | X1 != X2 | k1_xboole_0 != X0 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_2]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_294,plain,
% 7.73/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_293]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_34898,plain,
% 7.73/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_294]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10,plain,
% 7.73/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.73/1.49      | ~ v1_funct_1(X2)
% 7.73/1.49      | ~ v1_relat_1(X2)
% 7.73/1.49      | k1_funct_1(X2,X0) = X1 ),
% 7.73/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_25,negated_conjecture,
% 7.73/1.49      ( v1_funct_1(sK4) ),
% 7.73/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_338,plain,
% 7.73/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.73/1.49      | ~ v1_relat_1(X2)
% 7.73/1.49      | k1_funct_1(X2,X0) = X1
% 7.73/1.49      | sK4 != X2 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_339,plain,
% 7.73/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 7.73/1.49      | ~ v1_relat_1(sK4)
% 7.73/1.49      | k1_funct_1(sK4,X0) = X1 ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_338]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_21334,plain,
% 7.73/1.49      ( ~ r2_hidden(k4_tarski(sK0(sK5,X0,X1),sK5),sK4)
% 7.73/1.49      | ~ v1_relat_1(sK4)
% 7.73/1.49      | k1_funct_1(sK4,sK0(sK5,X0,X1)) = sK5 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_339]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_21345,plain,
% 7.73/1.49      ( ~ r2_hidden(k4_tarski(sK0(sK5,k1_xboole_0,k1_xboole_0),sK5),sK4)
% 7.73/1.49      | ~ v1_relat_1(sK4)
% 7.73/1.49      | k1_funct_1(sK4,sK0(sK5,k1_xboole_0,k1_xboole_0)) = sK5 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_21334]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_13716,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.73/1.49      | ~ r2_hidden(k4_tarski(sK0(sK5,X2,X0),sK5),X0)
% 7.73/1.49      | r2_hidden(k4_tarski(sK0(sK5,X2,X0),sK5),X1) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_21333,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
% 7.73/1.49      | ~ r2_hidden(k4_tarski(sK0(sK5,X1,X0),sK5),X0)
% 7.73/1.49      | r2_hidden(k4_tarski(sK0(sK5,X1,X0),sK5),sK4) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_13716]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_21337,plain,
% 7.73/1.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4))
% 7.73/1.49      | r2_hidden(k4_tarski(sK0(sK5,k1_xboole_0,k1_xboole_0),sK5),sK4)
% 7.73/1.49      | ~ r2_hidden(k4_tarski(sK0(sK5,k1_xboole_0,k1_xboole_0),sK5),k1_xboole_0) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_21333]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_21,negated_conjecture,
% 7.73/1.49      ( ~ r2_hidden(X0,sK1)
% 7.73/1.49      | ~ r2_hidden(X0,sK3)
% 7.73/1.49      | k1_funct_1(sK4,X0) != sK5 ),
% 7.73/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_17940,plain,
% 7.73/1.49      ( ~ r2_hidden(sK0(sK5,X0,X1),sK1)
% 7.73/1.49      | ~ r2_hidden(sK0(sK5,X0,X1),sK3)
% 7.73/1.49      | k1_funct_1(sK4,sK0(sK5,X0,X1)) != sK5 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_21]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_17946,plain,
% 7.73/1.49      ( ~ r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),sK1)
% 7.73/1.49      | ~ r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),sK3)
% 7.73/1.49      | k1_funct_1(sK4,sK0(sK5,k1_xboole_0,k1_xboole_0)) != sK5 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_17940]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_17939,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
% 7.73/1.49      | ~ r2_hidden(sK0(sK5,X0,X1),X0)
% 7.73/1.49      | r2_hidden(sK0(sK5,X0,X1),sK1) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_12730]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_17942,plain,
% 7.73/1.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
% 7.73/1.49      | r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),sK1)
% 7.73/1.49      | ~ r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_17939]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_16976,plain,
% 7.73/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_294]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5470,plain,
% 7.73/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k9_relat_1(X0,X1))) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_294]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5474,plain,
% 7.73/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k9_relat_1(k1_xboole_0,k1_xboole_0))) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_5470]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5284,plain,
% 7.73/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_294]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_7,plain,
% 7.73/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.73/1.49      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 7.73/1.49      | ~ v1_relat_1(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2927,plain,
% 7.73/1.49      ( r2_hidden(k4_tarski(sK0(sK5,X0,X1),sK5),X1)
% 7.73/1.49      | ~ r2_hidden(sK5,k9_relat_1(X1,X0))
% 7.73/1.49      | ~ v1_relat_1(X1) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2943,plain,
% 7.73/1.49      ( r2_hidden(k4_tarski(sK0(sK5,k1_xboole_0,k1_xboole_0),sK5),k1_xboole_0)
% 7.73/1.49      | ~ r2_hidden(sK5,k9_relat_1(k1_xboole_0,k1_xboole_0))
% 7.73/1.49      | ~ v1_relat_1(k1_xboole_0) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2927]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6,plain,
% 7.73/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.73/1.49      | r2_hidden(sK0(X0,X2,X1),X2)
% 7.73/1.49      | ~ v1_relat_1(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2929,plain,
% 7.73/1.49      ( r2_hidden(sK0(sK5,X0,X1),X0)
% 7.73/1.49      | ~ r2_hidden(sK5,k9_relat_1(X1,X0))
% 7.73/1.49      | ~ v1_relat_1(X1) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2935,plain,
% 7.73/1.49      ( r2_hidden(sK0(sK5,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 7.73/1.49      | ~ r2_hidden(sK5,k9_relat_1(k1_xboole_0,k1_xboole_0))
% 7.73/1.49      | ~ v1_relat_1(k1_xboole_0) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2929]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1160,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.73/1.49      | ~ r2_hidden(sK5,X0)
% 7.73/1.49      | r2_hidden(sK5,X1) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2926,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k9_relat_1(X1,X2)))
% 7.73/1.49      | ~ r2_hidden(sK5,X0)
% 7.73/1.49      | r2_hidden(sK5,k9_relat_1(X1,X2)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1160]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2931,plain,
% 7.73/1.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k9_relat_1(k1_xboole_0,k1_xboole_0)))
% 7.73/1.49      | r2_hidden(sK5,k9_relat_1(k1_xboole_0,k1_xboole_0))
% 7.73/1.49      | ~ r2_hidden(sK5,k1_xboole_0) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2926]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_912,plain,
% 7.73/1.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.73/1.49      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 7.73/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_20,plain,
% 7.73/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.73/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.73/1.49      | k1_xboole_0 = X2 ),
% 7.73/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_24,negated_conjecture,
% 7.73/1.49      ( v1_funct_2(sK4,sK1,sK2) ),
% 7.73/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_410,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.73/1.49      | sK2 != X2
% 7.73/1.49      | sK1 != X1
% 7.73/1.49      | sK4 != X0
% 7.73/1.49      | k1_xboole_0 = X2 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_411,plain,
% 7.73/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.73/1.49      | k1_relset_1(sK1,sK2,sK4) = sK1
% 7.73/1.49      | k1_xboole_0 = sK2 ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_410]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_23,negated_conjecture,
% 7.73/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.73/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_413,plain,
% 7.73/1.49      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_411,c_23]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_904,plain,
% 7.73/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_13,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_908,plain,
% 7.73/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.73/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1292,plain,
% 7.73/1.49      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_904,c_908]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1336,plain,
% 7.73/1.49      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_413,c_1292]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_8,plain,
% 7.73/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.73/1.49      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 7.73/1.49      | ~ v1_relat_1(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_910,plain,
% 7.73/1.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.73/1.49      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 7.73/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1737,plain,
% 7.73/1.49      ( sK2 = k1_xboole_0
% 7.73/1.49      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 7.73/1.49      | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
% 7.73/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_1336,c_910]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.73/1.49      | ~ v1_relat_1(X1)
% 7.73/1.49      | v1_relat_1(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_915,plain,
% 7.73/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.73/1.49      | v1_relat_1(X1) != iProver_top
% 7.73/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1297,plain,
% 7.73/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 7.73/1.49      | v1_relat_1(sK4) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_904,c_915]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4,plain,
% 7.73/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_914,plain,
% 7.73/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1489,plain,
% 7.73/1.49      ( v1_relat_1(sK4) = iProver_top ),
% 7.73/1.49      inference(forward_subsumption_resolution,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_1297,c_914]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2239,plain,
% 7.73/1.49      ( r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top
% 7.73/1.49      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 7.73/1.49      | sK2 = k1_xboole_0 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_1737,c_1489]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2240,plain,
% 7.73/1.49      ( sK2 = k1_xboole_0
% 7.73/1.49      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 7.73/1.49      | r2_hidden(sK0(X0,X1,sK4),sK1) = iProver_top ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_2239]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_14,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.73/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_907,plain,
% 7.73/1.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.73/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1333,plain,
% 7.73/1.49      ( k7_relset_1(sK1,sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_904,c_907]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_22,negated_conjecture,
% 7.73/1.49      ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_905,plain,
% 7.73/1.49      ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1430,plain,
% 7.73/1.49      ( r2_hidden(sK5,k9_relat_1(sK4,sK3)) = iProver_top ),
% 7.73/1.49      inference(demodulation,[status(thm)],[c_1333,c_905]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_911,plain,
% 7.73/1.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.73/1.49      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 7.73/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_900,plain,
% 7.73/1.49      ( k1_funct_1(sK4,X0) = X1
% 7.73/1.49      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 7.73/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1746,plain,
% 7.73/1.49      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 7.73/1.49      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 7.73/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_911,c_900]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2003,plain,
% 7.73/1.49      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 7.73/1.49      | k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_1746,c_1489]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2004,plain,
% 7.73/1.49      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 7.73/1.49      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_2003]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2013,plain,
% 7.73/1.49      ( k1_funct_1(sK4,sK0(sK5,sK3,sK4)) = sK5 ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_1430,c_2004]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_906,plain,
% 7.73/1.49      ( k1_funct_1(sK4,X0) != sK5
% 7.73/1.49      | r2_hidden(X0,sK1) != iProver_top
% 7.73/1.49      | r2_hidden(X0,sK3) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2036,plain,
% 7.73/1.49      ( r2_hidden(sK0(sK5,sK3,sK4),sK1) != iProver_top
% 7.73/1.49      | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_2013,c_906]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2248,plain,
% 7.73/1.49      ( sK2 = k1_xboole_0
% 7.73/1.49      | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top
% 7.73/1.49      | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_2240,c_2036]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2251,plain,
% 7.73/1.49      ( r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top
% 7.73/1.49      | sK2 = k1_xboole_0 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_2248,c_1430]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2252,plain,
% 7.73/1.49      ( sK2 = k1_xboole_0
% 7.73/1.49      | r2_hidden(sK0(sK5,sK3,sK4),sK3) != iProver_top ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_2251]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2257,plain,
% 7.73/1.49      ( sK2 = k1_xboole_0
% 7.73/1.49      | r2_hidden(sK5,k9_relat_1(sK4,sK3)) != iProver_top
% 7.73/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_912,c_2252]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_565,plain,
% 7.73/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.73/1.49      theory(equality) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1163,plain,
% 7.73/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(sK5,X2) | X1 != X2 | X0 != sK5 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_565]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1451,plain,
% 7.73/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(sK5,sK2) | X1 != sK2 | X0 != sK5 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1163]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1692,plain,
% 7.73/1.49      ( r2_hidden(sK5,X0)
% 7.73/1.49      | ~ r2_hidden(sK5,sK2)
% 7.73/1.49      | X0 != sK2
% 7.73/1.49      | sK5 != sK5 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1451]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1694,plain,
% 7.73/1.49      ( ~ r2_hidden(sK5,sK2)
% 7.73/1.49      | r2_hidden(sK5,k1_xboole_0)
% 7.73/1.49      | sK5 != sK5
% 7.73/1.49      | k1_xboole_0 != sK2 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1692]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1490,plain,
% 7.73/1.49      ( v1_relat_1(sK4) ),
% 7.73/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1489]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_564,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1279,plain,
% 7.73/1.49      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_564]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1280,plain,
% 7.73/1.49      ( sK2 != k1_xboole_0
% 7.73/1.49      | k1_xboole_0 = sK2
% 7.73/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1279]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.49      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1108,plain,
% 7.73/1.49      ( m1_subset_1(k7_relset_1(sK1,sK2,sK4,X0),k1_zfmisc_1(sK2))
% 7.73/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1214,plain,
% 7.73/1.49      ( m1_subset_1(k7_relset_1(sK1,sK2,sK4,sK3),k1_zfmisc_1(sK2))
% 7.73/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1108]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1074,plain,
% 7.73/1.49      ( ~ m1_subset_1(k7_relset_1(sK1,sK2,sK4,sK3),k1_zfmisc_1(X0))
% 7.73/1.49      | r2_hidden(sK5,X0)
% 7.73/1.49      | ~ r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1213,plain,
% 7.73/1.49      ( ~ m1_subset_1(k7_relset_1(sK1,sK2,sK4,sK3),k1_zfmisc_1(sK2))
% 7.73/1.49      | ~ r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))
% 7.73/1.49      | r2_hidden(sK5,sK2) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1074]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_563,plain,( X0 = X0 ),theory(equality) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1175,plain,
% 7.73/1.49      ( sK5 = sK5 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_563]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1085,plain,
% 7.73/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_294]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1089,plain,
% 7.73/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1085]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1064,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.49      | v1_relat_1(X0)
% 7.73/1.49      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1066,plain,
% 7.73/1.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 7.73/1.49      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 7.73/1.49      | v1_relat_1(k1_xboole_0) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1064]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_586,plain,
% 7.73/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_563]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_82,plain,
% 7.73/1.49      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(contradiction,plain,
% 7.73/1.49      ( $false ),
% 7.73/1.49      inference(minisat,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_37630,c_34898,c_21345,c_21337,c_17946,c_17942,c_16976,
% 7.73/1.49                 c_5474,c_5284,c_2943,c_2935,c_2931,c_2257,c_1694,c_1490,
% 7.73/1.49                 c_1489,c_1430,c_1280,c_1214,c_1213,c_1175,c_1089,c_1066,
% 7.73/1.49                 c_586,c_82,c_22,c_23]) ).
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  ------                               Statistics
% 7.73/1.49  
% 7.73/1.49  ------ General
% 7.73/1.49  
% 7.73/1.49  abstr_ref_over_cycles:                  0
% 7.73/1.49  abstr_ref_under_cycles:                 0
% 7.73/1.49  gc_basic_clause_elim:                   0
% 7.73/1.49  forced_gc_time:                         0
% 7.73/1.49  parsing_time:                           0.009
% 7.73/1.49  unif_index_cands_time:                  0.
% 7.73/1.49  unif_index_add_time:                    0.
% 7.73/1.49  orderings_time:                         0.
% 7.73/1.49  out_proof_time:                         0.011
% 7.73/1.49  total_time:                             0.994
% 7.73/1.49  num_of_symbols:                         52
% 7.73/1.49  num_of_terms:                           36395
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing
% 7.73/1.49  
% 7.73/1.49  num_of_splits:                          0
% 7.73/1.49  num_of_split_atoms:                     0
% 7.73/1.49  num_of_reused_defs:                     0
% 7.73/1.49  num_eq_ax_congr_red:                    22
% 7.73/1.49  num_of_sem_filtered_clauses:            1
% 7.73/1.49  num_of_subtypes:                        0
% 7.73/1.49  monotx_restored_types:                  0
% 7.73/1.49  sat_num_of_epr_types:                   0
% 7.73/1.49  sat_num_of_non_cyclic_types:            0
% 7.73/1.49  sat_guarded_non_collapsed_types:        0
% 7.73/1.49  num_pure_diseq_elim:                    0
% 7.73/1.49  simp_replaced_by:                       0
% 7.73/1.49  res_preprocessed:                       111
% 7.73/1.49  prep_upred:                             0
% 7.73/1.49  prep_unflattend:                        32
% 7.73/1.49  smt_new_axioms:                         0
% 7.73/1.49  pred_elim_cands:                        3
% 7.73/1.49  pred_elim:                              3
% 7.73/1.49  pred_elim_cl:                           6
% 7.73/1.49  pred_elim_cycles:                       5
% 7.73/1.49  merged_defs:                            0
% 7.73/1.49  merged_defs_ncl:                        0
% 7.73/1.49  bin_hyper_res:                          0
% 7.73/1.49  prep_cycles:                            4
% 7.73/1.49  pred_elim_time:                         0.002
% 7.73/1.49  splitting_time:                         0.
% 7.73/1.49  sem_filter_time:                        0.
% 7.73/1.49  monotx_time:                            0.
% 7.73/1.49  subtype_inf_time:                       0.
% 7.73/1.49  
% 7.73/1.49  ------ Problem properties
% 7.73/1.49  
% 7.73/1.49  clauses:                                20
% 7.73/1.49  conjectures:                            3
% 7.73/1.49  epr:                                    0
% 7.73/1.49  horn:                                   18
% 7.73/1.49  ground:                                 5
% 7.73/1.49  unary:                                  4
% 7.73/1.49  binary:                                 4
% 7.73/1.49  lits:                                   51
% 7.73/1.49  lits_eq:                                11
% 7.73/1.49  fd_pure:                                0
% 7.73/1.49  fd_pseudo:                              0
% 7.73/1.49  fd_cond:                                0
% 7.73/1.49  fd_pseudo_cond:                         1
% 7.73/1.49  ac_symbols:                             0
% 7.73/1.49  
% 7.73/1.49  ------ Propositional Solver
% 7.73/1.49  
% 7.73/1.49  prop_solver_calls:                      34
% 7.73/1.49  prop_fast_solver_calls:                 1629
% 7.73/1.49  smt_solver_calls:                       0
% 7.73/1.49  smt_fast_solver_calls:                  0
% 7.73/1.49  prop_num_of_clauses:                    12665
% 7.73/1.49  prop_preprocess_simplified:             12728
% 7.73/1.49  prop_fo_subsumed:                       79
% 7.73/1.49  prop_solver_time:                       0.
% 7.73/1.49  smt_solver_time:                        0.
% 7.73/1.49  smt_fast_solver_time:                   0.
% 7.73/1.49  prop_fast_solver_time:                  0.
% 7.73/1.49  prop_unsat_core_time:                   0.001
% 7.73/1.49  
% 7.73/1.49  ------ QBF
% 7.73/1.49  
% 7.73/1.49  qbf_q_res:                              0
% 7.73/1.49  qbf_num_tautologies:                    0
% 7.73/1.49  qbf_prep_cycles:                        0
% 7.73/1.49  
% 7.73/1.49  ------ BMC1
% 7.73/1.49  
% 7.73/1.49  bmc1_current_bound:                     -1
% 7.73/1.49  bmc1_last_solved_bound:                 -1
% 7.73/1.49  bmc1_unsat_core_size:                   -1
% 7.73/1.49  bmc1_unsat_core_parents_size:           -1
% 7.73/1.49  bmc1_merge_next_fun:                    0
% 7.73/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.73/1.49  
% 7.73/1.49  ------ Instantiation
% 7.73/1.49  
% 7.73/1.49  inst_num_of_clauses:                    2261
% 7.73/1.49  inst_num_in_passive:                    1145
% 7.73/1.49  inst_num_in_active:                     1094
% 7.73/1.49  inst_num_in_unprocessed:                21
% 7.73/1.49  inst_num_of_loops:                      1358
% 7.73/1.49  inst_num_of_learning_restarts:          0
% 7.73/1.49  inst_num_moves_active_passive:          257
% 7.73/1.49  inst_lit_activity:                      0
% 7.73/1.49  inst_lit_activity_moves:                0
% 7.73/1.49  inst_num_tautologies:                   0
% 7.73/1.49  inst_num_prop_implied:                  0
% 7.73/1.49  inst_num_existing_simplified:           0
% 7.73/1.49  inst_num_eq_res_simplified:             0
% 7.73/1.49  inst_num_child_elim:                    0
% 7.73/1.49  inst_num_of_dismatching_blockings:      1856
% 7.73/1.49  inst_num_of_non_proper_insts:           2871
% 7.73/1.49  inst_num_of_duplicates:                 0
% 7.73/1.49  inst_inst_num_from_inst_to_res:         0
% 7.73/1.49  inst_dismatching_checking_time:         0.
% 7.73/1.49  
% 7.73/1.49  ------ Resolution
% 7.73/1.49  
% 7.73/1.49  res_num_of_clauses:                     0
% 7.73/1.49  res_num_in_passive:                     0
% 7.73/1.49  res_num_in_active:                      0
% 7.73/1.49  res_num_of_loops:                       115
% 7.73/1.49  res_forward_subset_subsumed:            274
% 7.73/1.49  res_backward_subset_subsumed:           2
% 7.73/1.49  res_forward_subsumed:                   0
% 7.73/1.49  res_backward_subsumed:                  0
% 7.73/1.49  res_forward_subsumption_resolution:     0
% 7.73/1.49  res_backward_subsumption_resolution:    1
% 7.73/1.49  res_clause_to_clause_subsumption:       5502
% 7.73/1.49  res_orphan_elimination:                 0
% 7.73/1.49  res_tautology_del:                      481
% 7.73/1.49  res_num_eq_res_simplified:              0
% 7.73/1.49  res_num_sel_changes:                    0
% 7.73/1.49  res_moves_from_active_to_pass:          0
% 7.73/1.49  
% 7.73/1.49  ------ Superposition
% 7.73/1.49  
% 7.73/1.49  sup_time_total:                         0.
% 7.73/1.49  sup_time_generating:                    0.
% 7.73/1.49  sup_time_sim_full:                      0.
% 7.73/1.49  sup_time_sim_immed:                     0.
% 7.73/1.49  
% 7.73/1.49  sup_num_of_clauses:                     1500
% 7.73/1.49  sup_num_in_active:                      82
% 7.73/1.49  sup_num_in_passive:                     1418
% 7.73/1.49  sup_num_of_loops:                       270
% 7.73/1.49  sup_fw_superposition:                   1319
% 7.73/1.49  sup_bw_superposition:                   865
% 7.73/1.49  sup_immediate_simplified:               453
% 7.73/1.49  sup_given_eliminated:                   17
% 7.73/1.49  comparisons_done:                       0
% 7.73/1.49  comparisons_avoided:                    6
% 7.73/1.49  
% 7.73/1.49  ------ Simplifications
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  sim_fw_subset_subsumed:                 109
% 7.73/1.49  sim_bw_subset_subsumed:                 33
% 7.73/1.49  sim_fw_subsumed:                        184
% 7.73/1.49  sim_bw_subsumed:                        77
% 7.73/1.49  sim_fw_subsumption_res:                 76
% 7.73/1.49  sim_bw_subsumption_res:                 0
% 7.73/1.49  sim_tautology_del:                      14
% 7.73/1.49  sim_eq_tautology_del:                   16
% 7.73/1.49  sim_eq_res_simp:                        1
% 7.73/1.49  sim_fw_demodulated:                     25
% 7.73/1.49  sim_bw_demodulated:                     167
% 7.73/1.49  sim_light_normalised:                   40
% 7.73/1.49  sim_joinable_taut:                      0
% 7.73/1.49  sim_joinable_simp:                      0
% 7.73/1.49  sim_ac_normalised:                      0
% 7.73/1.49  sim_smt_subsumption:                    0
% 7.73/1.49  
%------------------------------------------------------------------------------

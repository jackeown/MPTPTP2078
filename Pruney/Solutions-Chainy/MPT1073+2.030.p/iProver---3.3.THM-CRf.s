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
% DateTime   : Thu Dec  3 12:10:06 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 540 expanded)
%              Number of clauses        :   76 ( 193 expanded)
%              Number of leaves         :   16 (  99 expanded)
%              Depth                    :   23
%              Number of atoms          :  390 (2208 expanded)
%              Number of equality atoms :  164 ( 566 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f39,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK4,X4) != sK1
          | ~ m1_subset_1(X4,sK2) )
      & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ! [X4] :
        ( k1_funct_1(sK4,X4) != sK1
        | ~ m1_subset_1(X4,sK2) )
    & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f40])).

fof(f66,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

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
    inference(nnf_transformation,[],[f20])).

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
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) != sK1
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_320,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_321,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_3872,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_579,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_581,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_579,c_25])).

cnf(c_1261,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1266,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1875,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1261,c_1266])).

cnf(c_2084,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_581,c_1875])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1265,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1664,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1261,c_1265])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1262,plain,
    ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1718,plain,
    ( r2_hidden(sK1,k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1664,c_1262])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1268,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1632,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1268])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1269,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1667,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1632,c_1269])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1271,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_331,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_332,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_1259,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_333,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_1436,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1437,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1436])).

cnf(c_1473,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | k1_funct_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1259,c_30,c_333,c_1437])).

cnf(c_1474,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_1473])).

cnf(c_2511,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1271,c_1474])).

cnf(c_2745,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2511,c_30,c_1437])).

cnf(c_2746,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2745])).

cnf(c_2755,plain,
    ( k1_funct_1(sK4,sK0(X0,k1_relat_1(sK4),sK4)) = X0
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1667,c_2746])).

cnf(c_3197,plain,
    ( k1_funct_1(sK4,sK0(sK1,k1_relat_1(sK4),sK4)) = sK1 ),
    inference(superposition,[status(thm)],[c_1718,c_2755])).

cnf(c_23,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,X0) != sK1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1263,plain,
    ( k1_funct_1(sK4,X0) != sK1
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3283,plain,
    ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3197,c_1263])).

cnf(c_3313,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(sK1,sK2,sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_3283])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1270,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2401,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_1270])).

cnf(c_2927,plain,
    ( r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2401,c_30,c_1437])).

cnf(c_2928,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2927])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1274,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2936,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK0(X0,X1,sK4),sK2) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2928,c_1274])).

cnf(c_3312,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2936,c_3283])).

cnf(c_3320,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1,k2_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3312,c_1667])).

cnf(c_3434,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3313,c_1718,c_3320])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1264,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1870,plain,
    ( k7_relset_1(sK2,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1261,c_1264])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1267,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2148,plain,
    ( m1_subset_1(k9_relat_1(sK4,X0),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1870,c_1267])).

cnf(c_2227,plain,
    ( m1_subset_1(k9_relat_1(sK4,X0),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2148,c_30])).

cnf(c_2234,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1667,c_2227])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1275,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2393,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2234,c_1275])).

cnf(c_2658,plain,
    ( r2_hidden(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1718,c_2393])).

cnf(c_3440,plain,
    ( r2_hidden(sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3434,c_2658])).

cnf(c_3513,plain,
    ( r2_hidden(sK1,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3440])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3872,c_3513])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.93/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.02  
% 2.93/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.93/1.02  
% 2.93/1.02  ------  iProver source info
% 2.93/1.02  
% 2.93/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.93/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.93/1.02  git: non_committed_changes: false
% 2.93/1.02  git: last_make_outside_of_git: false
% 2.93/1.02  
% 2.93/1.02  ------ 
% 2.93/1.02  
% 2.93/1.02  ------ Input Options
% 2.93/1.02  
% 2.93/1.02  --out_options                           all
% 2.93/1.02  --tptp_safe_out                         true
% 2.93/1.02  --problem_path                          ""
% 2.93/1.02  --include_path                          ""
% 2.93/1.02  --clausifier                            res/vclausify_rel
% 2.93/1.02  --clausifier_options                    --mode clausify
% 2.93/1.02  --stdin                                 false
% 2.93/1.02  --stats_out                             all
% 2.93/1.02  
% 2.93/1.02  ------ General Options
% 2.93/1.02  
% 2.93/1.02  --fof                                   false
% 2.93/1.02  --time_out_real                         305.
% 2.93/1.02  --time_out_virtual                      -1.
% 2.93/1.02  --symbol_type_check                     false
% 2.93/1.02  --clausify_out                          false
% 2.93/1.02  --sig_cnt_out                           false
% 2.93/1.02  --trig_cnt_out                          false
% 2.93/1.02  --trig_cnt_out_tolerance                1.
% 2.93/1.02  --trig_cnt_out_sk_spl                   false
% 2.93/1.02  --abstr_cl_out                          false
% 2.93/1.02  
% 2.93/1.02  ------ Global Options
% 2.93/1.02  
% 2.93/1.02  --schedule                              default
% 2.93/1.02  --add_important_lit                     false
% 2.93/1.02  --prop_solver_per_cl                    1000
% 2.93/1.02  --min_unsat_core                        false
% 2.93/1.02  --soft_assumptions                      false
% 2.93/1.02  --soft_lemma_size                       3
% 2.93/1.02  --prop_impl_unit_size                   0
% 2.93/1.02  --prop_impl_unit                        []
% 2.93/1.02  --share_sel_clauses                     true
% 2.93/1.02  --reset_solvers                         false
% 2.93/1.02  --bc_imp_inh                            [conj_cone]
% 2.93/1.02  --conj_cone_tolerance                   3.
% 2.93/1.02  --extra_neg_conj                        none
% 2.93/1.02  --large_theory_mode                     true
% 2.93/1.02  --prolific_symb_bound                   200
% 2.93/1.02  --lt_threshold                          2000
% 2.93/1.02  --clause_weak_htbl                      true
% 2.93/1.02  --gc_record_bc_elim                     false
% 2.93/1.02  
% 2.93/1.02  ------ Preprocessing Options
% 2.93/1.02  
% 2.93/1.02  --preprocessing_flag                    true
% 2.93/1.02  --time_out_prep_mult                    0.1
% 2.93/1.02  --splitting_mode                        input
% 2.93/1.02  --splitting_grd                         true
% 2.93/1.02  --splitting_cvd                         false
% 2.93/1.02  --splitting_cvd_svl                     false
% 2.93/1.02  --splitting_nvd                         32
% 2.93/1.02  --sub_typing                            true
% 2.93/1.02  --prep_gs_sim                           true
% 2.93/1.02  --prep_unflatten                        true
% 2.93/1.02  --prep_res_sim                          true
% 2.93/1.02  --prep_upred                            true
% 2.93/1.02  --prep_sem_filter                       exhaustive
% 2.93/1.02  --prep_sem_filter_out                   false
% 2.93/1.02  --pred_elim                             true
% 2.93/1.02  --res_sim_input                         true
% 2.93/1.02  --eq_ax_congr_red                       true
% 2.93/1.02  --pure_diseq_elim                       true
% 2.93/1.02  --brand_transform                       false
% 2.93/1.02  --non_eq_to_eq                          false
% 2.93/1.02  --prep_def_merge                        true
% 2.93/1.02  --prep_def_merge_prop_impl              false
% 2.93/1.02  --prep_def_merge_mbd                    true
% 2.93/1.02  --prep_def_merge_tr_red                 false
% 2.93/1.02  --prep_def_merge_tr_cl                  false
% 2.93/1.02  --smt_preprocessing                     true
% 2.93/1.02  --smt_ac_axioms                         fast
% 2.93/1.02  --preprocessed_out                      false
% 2.93/1.02  --preprocessed_stats                    false
% 2.93/1.02  
% 2.93/1.02  ------ Abstraction refinement Options
% 2.93/1.02  
% 2.93/1.02  --abstr_ref                             []
% 2.93/1.02  --abstr_ref_prep                        false
% 2.93/1.02  --abstr_ref_until_sat                   false
% 2.93/1.02  --abstr_ref_sig_restrict                funpre
% 2.93/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/1.02  --abstr_ref_under                       []
% 2.93/1.02  
% 2.93/1.02  ------ SAT Options
% 2.93/1.02  
% 2.93/1.02  --sat_mode                              false
% 2.93/1.02  --sat_fm_restart_options                ""
% 2.93/1.02  --sat_gr_def                            false
% 2.93/1.02  --sat_epr_types                         true
% 2.93/1.02  --sat_non_cyclic_types                  false
% 2.93/1.02  --sat_finite_models                     false
% 2.93/1.02  --sat_fm_lemmas                         false
% 2.93/1.02  --sat_fm_prep                           false
% 2.93/1.02  --sat_fm_uc_incr                        true
% 2.93/1.02  --sat_out_model                         small
% 2.93/1.02  --sat_out_clauses                       false
% 2.93/1.02  
% 2.93/1.02  ------ QBF Options
% 2.93/1.02  
% 2.93/1.02  --qbf_mode                              false
% 2.93/1.02  --qbf_elim_univ                         false
% 2.93/1.02  --qbf_dom_inst                          none
% 2.93/1.02  --qbf_dom_pre_inst                      false
% 2.93/1.02  --qbf_sk_in                             false
% 2.93/1.02  --qbf_pred_elim                         true
% 2.93/1.02  --qbf_split                             512
% 2.93/1.02  
% 2.93/1.02  ------ BMC1 Options
% 2.93/1.02  
% 2.93/1.02  --bmc1_incremental                      false
% 2.93/1.02  --bmc1_axioms                           reachable_all
% 2.93/1.02  --bmc1_min_bound                        0
% 2.93/1.02  --bmc1_max_bound                        -1
% 2.93/1.02  --bmc1_max_bound_default                -1
% 2.93/1.02  --bmc1_symbol_reachability              true
% 2.93/1.02  --bmc1_property_lemmas                  false
% 2.93/1.02  --bmc1_k_induction                      false
% 2.93/1.02  --bmc1_non_equiv_states                 false
% 2.93/1.02  --bmc1_deadlock                         false
% 2.93/1.02  --bmc1_ucm                              false
% 2.93/1.02  --bmc1_add_unsat_core                   none
% 2.93/1.02  --bmc1_unsat_core_children              false
% 2.93/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/1.02  --bmc1_out_stat                         full
% 2.93/1.02  --bmc1_ground_init                      false
% 2.93/1.02  --bmc1_pre_inst_next_state              false
% 2.93/1.02  --bmc1_pre_inst_state                   false
% 2.93/1.02  --bmc1_pre_inst_reach_state             false
% 2.93/1.02  --bmc1_out_unsat_core                   false
% 2.93/1.02  --bmc1_aig_witness_out                  false
% 2.93/1.02  --bmc1_verbose                          false
% 2.93/1.02  --bmc1_dump_clauses_tptp                false
% 2.93/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.93/1.02  --bmc1_dump_file                        -
% 2.93/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.93/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.93/1.02  --bmc1_ucm_extend_mode                  1
% 2.93/1.02  --bmc1_ucm_init_mode                    2
% 2.93/1.02  --bmc1_ucm_cone_mode                    none
% 2.93/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.93/1.02  --bmc1_ucm_relax_model                  4
% 2.93/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.93/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/1.02  --bmc1_ucm_layered_model                none
% 2.93/1.02  --bmc1_ucm_max_lemma_size               10
% 2.93/1.02  
% 2.93/1.02  ------ AIG Options
% 2.93/1.02  
% 2.93/1.02  --aig_mode                              false
% 2.93/1.02  
% 2.93/1.02  ------ Instantiation Options
% 2.93/1.02  
% 2.93/1.02  --instantiation_flag                    true
% 2.93/1.02  --inst_sos_flag                         false
% 2.93/1.02  --inst_sos_phase                        true
% 2.93/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/1.02  --inst_lit_sel_side                     num_symb
% 2.93/1.02  --inst_solver_per_active                1400
% 2.93/1.02  --inst_solver_calls_frac                1.
% 2.93/1.02  --inst_passive_queue_type               priority_queues
% 2.93/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/1.02  --inst_passive_queues_freq              [25;2]
% 2.93/1.02  --inst_dismatching                      true
% 2.93/1.02  --inst_eager_unprocessed_to_passive     true
% 2.93/1.02  --inst_prop_sim_given                   true
% 2.93/1.02  --inst_prop_sim_new                     false
% 2.93/1.02  --inst_subs_new                         false
% 2.93/1.02  --inst_eq_res_simp                      false
% 2.93/1.02  --inst_subs_given                       false
% 2.93/1.02  --inst_orphan_elimination               true
% 2.93/1.02  --inst_learning_loop_flag               true
% 2.93/1.02  --inst_learning_start                   3000
% 2.93/1.02  --inst_learning_factor                  2
% 2.93/1.02  --inst_start_prop_sim_after_learn       3
% 2.93/1.02  --inst_sel_renew                        solver
% 2.93/1.02  --inst_lit_activity_flag                true
% 2.93/1.02  --inst_restr_to_given                   false
% 2.93/1.02  --inst_activity_threshold               500
% 2.93/1.02  --inst_out_proof                        true
% 2.93/1.02  
% 2.93/1.02  ------ Resolution Options
% 2.93/1.02  
% 2.93/1.02  --resolution_flag                       true
% 2.93/1.02  --res_lit_sel                           adaptive
% 2.93/1.02  --res_lit_sel_side                      none
% 2.93/1.02  --res_ordering                          kbo
% 2.93/1.02  --res_to_prop_solver                    active
% 2.93/1.02  --res_prop_simpl_new                    false
% 2.93/1.02  --res_prop_simpl_given                  true
% 2.93/1.02  --res_passive_queue_type                priority_queues
% 2.93/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/1.02  --res_passive_queues_freq               [15;5]
% 2.93/1.02  --res_forward_subs                      full
% 2.93/1.02  --res_backward_subs                     full
% 2.93/1.02  --res_forward_subs_resolution           true
% 2.93/1.02  --res_backward_subs_resolution          true
% 2.93/1.02  --res_orphan_elimination                true
% 2.93/1.02  --res_time_limit                        2.
% 2.93/1.02  --res_out_proof                         true
% 2.93/1.02  
% 2.93/1.02  ------ Superposition Options
% 2.93/1.02  
% 2.93/1.02  --superposition_flag                    true
% 2.93/1.02  --sup_passive_queue_type                priority_queues
% 2.93/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.93/1.02  --demod_completeness_check              fast
% 2.93/1.02  --demod_use_ground                      true
% 2.93/1.02  --sup_to_prop_solver                    passive
% 2.93/1.02  --sup_prop_simpl_new                    true
% 2.93/1.02  --sup_prop_simpl_given                  true
% 2.93/1.02  --sup_fun_splitting                     false
% 2.93/1.02  --sup_smt_interval                      50000
% 2.93/1.02  
% 2.93/1.02  ------ Superposition Simplification Setup
% 2.93/1.02  
% 2.93/1.02  --sup_indices_passive                   []
% 2.93/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.02  --sup_full_bw                           [BwDemod]
% 2.93/1.02  --sup_immed_triv                        [TrivRules]
% 2.93/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.02  --sup_immed_bw_main                     []
% 2.93/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.02  
% 2.93/1.02  ------ Combination Options
% 2.93/1.02  
% 2.93/1.02  --comb_res_mult                         3
% 2.93/1.02  --comb_sup_mult                         2
% 2.93/1.02  --comb_inst_mult                        10
% 2.93/1.02  
% 2.93/1.02  ------ Debug Options
% 2.93/1.02  
% 2.93/1.02  --dbg_backtrace                         false
% 2.93/1.02  --dbg_dump_prop_clauses                 false
% 2.93/1.02  --dbg_dump_prop_clauses_file            -
% 2.93/1.02  --dbg_out_stat                          false
% 2.93/1.02  ------ Parsing...
% 2.93/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.93/1.02  
% 2.93/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.93/1.02  
% 2.93/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.93/1.02  
% 2.93/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.93/1.02  ------ Proving...
% 2.93/1.02  ------ Problem Properties 
% 2.93/1.02  
% 2.93/1.02  
% 2.93/1.02  clauses                                 22
% 2.93/1.02  conjectures                             3
% 2.93/1.02  EPR                                     2
% 2.93/1.02  Horn                                    20
% 2.93/1.02  unary                                   3
% 2.93/1.02  binary                                  9
% 2.93/1.02  lits                                    54
% 2.93/1.02  lits eq                                 13
% 2.93/1.02  fd_pure                                 0
% 2.93/1.02  fd_pseudo                               0
% 2.93/1.02  fd_cond                                 0
% 2.93/1.02  fd_pseudo_cond                          1
% 2.93/1.02  AC symbols                              0
% 2.93/1.02  
% 2.93/1.02  ------ Schedule dynamic 5 is on 
% 2.93/1.02  
% 2.93/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.93/1.02  
% 2.93/1.02  
% 2.93/1.02  ------ 
% 2.93/1.02  Current options:
% 2.93/1.02  ------ 
% 2.93/1.02  
% 2.93/1.02  ------ Input Options
% 2.93/1.02  
% 2.93/1.02  --out_options                           all
% 2.93/1.02  --tptp_safe_out                         true
% 2.93/1.02  --problem_path                          ""
% 2.93/1.02  --include_path                          ""
% 2.93/1.02  --clausifier                            res/vclausify_rel
% 2.93/1.02  --clausifier_options                    --mode clausify
% 2.93/1.02  --stdin                                 false
% 2.93/1.02  --stats_out                             all
% 2.93/1.02  
% 2.93/1.02  ------ General Options
% 2.93/1.02  
% 2.93/1.02  --fof                                   false
% 2.93/1.02  --time_out_real                         305.
% 2.93/1.02  --time_out_virtual                      -1.
% 2.93/1.02  --symbol_type_check                     false
% 2.93/1.02  --clausify_out                          false
% 2.93/1.02  --sig_cnt_out                           false
% 2.93/1.02  --trig_cnt_out                          false
% 2.93/1.02  --trig_cnt_out_tolerance                1.
% 2.93/1.02  --trig_cnt_out_sk_spl                   false
% 2.93/1.02  --abstr_cl_out                          false
% 2.93/1.02  
% 2.93/1.02  ------ Global Options
% 2.93/1.02  
% 2.93/1.02  --schedule                              default
% 2.93/1.02  --add_important_lit                     false
% 2.93/1.02  --prop_solver_per_cl                    1000
% 2.93/1.02  --min_unsat_core                        false
% 2.93/1.02  --soft_assumptions                      false
% 2.93/1.02  --soft_lemma_size                       3
% 2.93/1.02  --prop_impl_unit_size                   0
% 2.93/1.02  --prop_impl_unit                        []
% 2.93/1.02  --share_sel_clauses                     true
% 2.93/1.02  --reset_solvers                         false
% 2.93/1.02  --bc_imp_inh                            [conj_cone]
% 2.93/1.02  --conj_cone_tolerance                   3.
% 2.93/1.02  --extra_neg_conj                        none
% 2.93/1.02  --large_theory_mode                     true
% 2.93/1.02  --prolific_symb_bound                   200
% 2.93/1.02  --lt_threshold                          2000
% 2.93/1.02  --clause_weak_htbl                      true
% 2.93/1.02  --gc_record_bc_elim                     false
% 2.93/1.02  
% 2.93/1.02  ------ Preprocessing Options
% 2.93/1.02  
% 2.93/1.02  --preprocessing_flag                    true
% 2.93/1.02  --time_out_prep_mult                    0.1
% 2.93/1.02  --splitting_mode                        input
% 2.93/1.02  --splitting_grd                         true
% 2.93/1.02  --splitting_cvd                         false
% 2.93/1.02  --splitting_cvd_svl                     false
% 2.93/1.02  --splitting_nvd                         32
% 2.93/1.02  --sub_typing                            true
% 2.93/1.02  --prep_gs_sim                           true
% 2.93/1.02  --prep_unflatten                        true
% 2.93/1.02  --prep_res_sim                          true
% 2.93/1.02  --prep_upred                            true
% 2.93/1.02  --prep_sem_filter                       exhaustive
% 2.93/1.02  --prep_sem_filter_out                   false
% 2.93/1.02  --pred_elim                             true
% 2.93/1.02  --res_sim_input                         true
% 2.93/1.02  --eq_ax_congr_red                       true
% 2.93/1.02  --pure_diseq_elim                       true
% 2.93/1.02  --brand_transform                       false
% 2.93/1.02  --non_eq_to_eq                          false
% 2.93/1.02  --prep_def_merge                        true
% 2.93/1.02  --prep_def_merge_prop_impl              false
% 2.93/1.02  --prep_def_merge_mbd                    true
% 2.93/1.02  --prep_def_merge_tr_red                 false
% 2.93/1.02  --prep_def_merge_tr_cl                  false
% 2.93/1.02  --smt_preprocessing                     true
% 2.93/1.02  --smt_ac_axioms                         fast
% 2.93/1.02  --preprocessed_out                      false
% 2.93/1.02  --preprocessed_stats                    false
% 2.93/1.02  
% 2.93/1.02  ------ Abstraction refinement Options
% 2.93/1.02  
% 2.93/1.02  --abstr_ref                             []
% 2.93/1.02  --abstr_ref_prep                        false
% 2.93/1.02  --abstr_ref_until_sat                   false
% 2.93/1.02  --abstr_ref_sig_restrict                funpre
% 2.93/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/1.02  --abstr_ref_under                       []
% 2.93/1.02  
% 2.93/1.02  ------ SAT Options
% 2.93/1.02  
% 2.93/1.02  --sat_mode                              false
% 2.93/1.02  --sat_fm_restart_options                ""
% 2.93/1.02  --sat_gr_def                            false
% 2.93/1.02  --sat_epr_types                         true
% 2.93/1.02  --sat_non_cyclic_types                  false
% 2.93/1.02  --sat_finite_models                     false
% 2.93/1.02  --sat_fm_lemmas                         false
% 2.93/1.02  --sat_fm_prep                           false
% 2.93/1.02  --sat_fm_uc_incr                        true
% 2.93/1.02  --sat_out_model                         small
% 2.93/1.02  --sat_out_clauses                       false
% 2.93/1.02  
% 2.93/1.02  ------ QBF Options
% 2.93/1.02  
% 2.93/1.02  --qbf_mode                              false
% 2.93/1.02  --qbf_elim_univ                         false
% 2.93/1.02  --qbf_dom_inst                          none
% 2.93/1.02  --qbf_dom_pre_inst                      false
% 2.93/1.02  --qbf_sk_in                             false
% 2.93/1.02  --qbf_pred_elim                         true
% 2.93/1.02  --qbf_split                             512
% 2.93/1.02  
% 2.93/1.02  ------ BMC1 Options
% 2.93/1.02  
% 2.93/1.02  --bmc1_incremental                      false
% 2.93/1.02  --bmc1_axioms                           reachable_all
% 2.93/1.02  --bmc1_min_bound                        0
% 2.93/1.02  --bmc1_max_bound                        -1
% 2.93/1.02  --bmc1_max_bound_default                -1
% 2.93/1.02  --bmc1_symbol_reachability              true
% 2.93/1.02  --bmc1_property_lemmas                  false
% 2.93/1.02  --bmc1_k_induction                      false
% 2.93/1.02  --bmc1_non_equiv_states                 false
% 2.93/1.02  --bmc1_deadlock                         false
% 2.93/1.02  --bmc1_ucm                              false
% 2.93/1.02  --bmc1_add_unsat_core                   none
% 2.93/1.02  --bmc1_unsat_core_children              false
% 2.93/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/1.02  --bmc1_out_stat                         full
% 2.93/1.02  --bmc1_ground_init                      false
% 2.93/1.02  --bmc1_pre_inst_next_state              false
% 2.93/1.02  --bmc1_pre_inst_state                   false
% 2.93/1.02  --bmc1_pre_inst_reach_state             false
% 2.93/1.02  --bmc1_out_unsat_core                   false
% 2.93/1.02  --bmc1_aig_witness_out                  false
% 2.93/1.02  --bmc1_verbose                          false
% 2.93/1.02  --bmc1_dump_clauses_tptp                false
% 2.93/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.93/1.02  --bmc1_dump_file                        -
% 2.93/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.93/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.93/1.02  --bmc1_ucm_extend_mode                  1
% 2.93/1.02  --bmc1_ucm_init_mode                    2
% 2.93/1.02  --bmc1_ucm_cone_mode                    none
% 2.93/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.93/1.02  --bmc1_ucm_relax_model                  4
% 2.93/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.93/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/1.02  --bmc1_ucm_layered_model                none
% 2.93/1.02  --bmc1_ucm_max_lemma_size               10
% 2.93/1.02  
% 2.93/1.02  ------ AIG Options
% 2.93/1.02  
% 2.93/1.02  --aig_mode                              false
% 2.93/1.02  
% 2.93/1.02  ------ Instantiation Options
% 2.93/1.02  
% 2.93/1.02  --instantiation_flag                    true
% 2.93/1.02  --inst_sos_flag                         false
% 2.93/1.02  --inst_sos_phase                        true
% 2.93/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/1.02  --inst_lit_sel_side                     none
% 2.93/1.02  --inst_solver_per_active                1400
% 2.93/1.02  --inst_solver_calls_frac                1.
% 2.93/1.02  --inst_passive_queue_type               priority_queues
% 2.93/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/1.02  --inst_passive_queues_freq              [25;2]
% 2.93/1.02  --inst_dismatching                      true
% 2.93/1.02  --inst_eager_unprocessed_to_passive     true
% 2.93/1.02  --inst_prop_sim_given                   true
% 2.93/1.02  --inst_prop_sim_new                     false
% 2.93/1.02  --inst_subs_new                         false
% 2.93/1.02  --inst_eq_res_simp                      false
% 2.93/1.02  --inst_subs_given                       false
% 2.93/1.02  --inst_orphan_elimination               true
% 2.93/1.02  --inst_learning_loop_flag               true
% 2.93/1.02  --inst_learning_start                   3000
% 2.93/1.02  --inst_learning_factor                  2
% 2.93/1.02  --inst_start_prop_sim_after_learn       3
% 2.93/1.02  --inst_sel_renew                        solver
% 2.93/1.02  --inst_lit_activity_flag                true
% 2.93/1.02  --inst_restr_to_given                   false
% 2.93/1.02  --inst_activity_threshold               500
% 2.93/1.02  --inst_out_proof                        true
% 2.93/1.02  
% 2.93/1.02  ------ Resolution Options
% 2.93/1.02  
% 2.93/1.02  --resolution_flag                       false
% 2.93/1.02  --res_lit_sel                           adaptive
% 2.93/1.02  --res_lit_sel_side                      none
% 2.93/1.02  --res_ordering                          kbo
% 2.93/1.02  --res_to_prop_solver                    active
% 2.93/1.02  --res_prop_simpl_new                    false
% 2.93/1.02  --res_prop_simpl_given                  true
% 2.93/1.02  --res_passive_queue_type                priority_queues
% 2.93/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/1.02  --res_passive_queues_freq               [15;5]
% 2.93/1.02  --res_forward_subs                      full
% 2.93/1.02  --res_backward_subs                     full
% 2.93/1.02  --res_forward_subs_resolution           true
% 2.93/1.02  --res_backward_subs_resolution          true
% 2.93/1.02  --res_orphan_elimination                true
% 2.93/1.02  --res_time_limit                        2.
% 2.93/1.02  --res_out_proof                         true
% 2.93/1.02  
% 2.93/1.02  ------ Superposition Options
% 2.93/1.02  
% 2.93/1.02  --superposition_flag                    true
% 2.93/1.02  --sup_passive_queue_type                priority_queues
% 2.93/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.93/1.02  --demod_completeness_check              fast
% 2.93/1.02  --demod_use_ground                      true
% 2.93/1.02  --sup_to_prop_solver                    passive
% 2.93/1.02  --sup_prop_simpl_new                    true
% 2.93/1.02  --sup_prop_simpl_given                  true
% 2.93/1.02  --sup_fun_splitting                     false
% 2.93/1.02  --sup_smt_interval                      50000
% 2.93/1.02  
% 2.93/1.02  ------ Superposition Simplification Setup
% 2.93/1.02  
% 2.93/1.02  --sup_indices_passive                   []
% 2.93/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.02  --sup_full_bw                           [BwDemod]
% 2.93/1.02  --sup_immed_triv                        [TrivRules]
% 2.93/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.02  --sup_immed_bw_main                     []
% 2.93/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/1.02  
% 2.93/1.02  ------ Combination Options
% 2.93/1.02  
% 2.93/1.02  --comb_res_mult                         3
% 2.93/1.02  --comb_sup_mult                         2
% 2.93/1.02  --comb_inst_mult                        10
% 2.93/1.02  
% 2.93/1.02  ------ Debug Options
% 2.93/1.02  
% 2.93/1.02  --dbg_backtrace                         false
% 2.93/1.02  --dbg_dump_prop_clauses                 false
% 2.93/1.02  --dbg_dump_prop_clauses_file            -
% 2.93/1.02  --dbg_out_stat                          false
% 2.93/1.02  
% 2.93/1.02  
% 2.93/1.02  
% 2.93/1.02  
% 2.93/1.02  ------ Proving...
% 2.93/1.02  
% 2.93/1.02  
% 2.93/1.02  % SZS status Theorem for theBenchmark.p
% 2.93/1.02  
% 2.93/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.93/1.02  
% 2.93/1.02  fof(f1,axiom,(
% 2.93/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f16,plain,(
% 2.93/1.02    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.93/1.02    inference(unused_predicate_definition_removal,[],[f1])).
% 2.93/1.02  
% 2.93/1.02  fof(f17,plain,(
% 2.93/1.02    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.93/1.02    inference(ennf_transformation,[],[f16])).
% 2.93/1.02  
% 2.93/1.02  fof(f42,plain,(
% 2.93/1.02    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.93/1.02    inference(cnf_transformation,[],[f17])).
% 2.93/1.02  
% 2.93/1.02  fof(f2,axiom,(
% 2.93/1.02    v1_xboole_0(k1_xboole_0)),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f43,plain,(
% 2.93/1.02    v1_xboole_0(k1_xboole_0)),
% 2.93/1.02    inference(cnf_transformation,[],[f2])).
% 2.93/1.02  
% 2.93/1.02  fof(f13,axiom,(
% 2.93/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f29,plain,(
% 2.93/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.02    inference(ennf_transformation,[],[f13])).
% 2.93/1.02  
% 2.93/1.02  fof(f30,plain,(
% 2.93/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.02    inference(flattening,[],[f29])).
% 2.93/1.02  
% 2.93/1.02  fof(f39,plain,(
% 2.93/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.02    inference(nnf_transformation,[],[f30])).
% 2.93/1.02  
% 2.93/1.02  fof(f59,plain,(
% 2.93/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.02    inference(cnf_transformation,[],[f39])).
% 2.93/1.02  
% 2.93/1.02  fof(f14,conjecture,(
% 2.93/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f15,negated_conjecture,(
% 2.93/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 2.93/1.02    inference(negated_conjecture,[],[f14])).
% 2.93/1.02  
% 2.93/1.02  fof(f31,plain,(
% 2.93/1.02    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 2.93/1.02    inference(ennf_transformation,[],[f15])).
% 2.93/1.02  
% 2.93/1.02  fof(f32,plain,(
% 2.93/1.02    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 2.93/1.02    inference(flattening,[],[f31])).
% 2.93/1.02  
% 2.93/1.02  fof(f40,plain,(
% 2.93/1.02    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK4,X4) != sK1 | ~m1_subset_1(X4,sK2)) & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.93/1.02    introduced(choice_axiom,[])).
% 2.93/1.02  
% 2.93/1.02  fof(f41,plain,(
% 2.93/1.02    ! [X4] : (k1_funct_1(sK4,X4) != sK1 | ~m1_subset_1(X4,sK2)) & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.93/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f40])).
% 2.93/1.02  
% 2.93/1.02  fof(f66,plain,(
% 2.93/1.02    v1_funct_2(sK4,sK2,sK3)),
% 2.93/1.02    inference(cnf_transformation,[],[f41])).
% 2.93/1.02  
% 2.93/1.02  fof(f67,plain,(
% 2.93/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.93/1.02    inference(cnf_transformation,[],[f41])).
% 2.93/1.02  
% 2.93/1.02  fof(f10,axiom,(
% 2.93/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f26,plain,(
% 2.93/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.02    inference(ennf_transformation,[],[f10])).
% 2.93/1.02  
% 2.93/1.02  fof(f56,plain,(
% 2.93/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.02    inference(cnf_transformation,[],[f26])).
% 2.93/1.02  
% 2.93/1.02  fof(f11,axiom,(
% 2.93/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f27,plain,(
% 2.93/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.02    inference(ennf_transformation,[],[f11])).
% 2.93/1.02  
% 2.93/1.02  fof(f57,plain,(
% 2.93/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.02    inference(cnf_transformation,[],[f27])).
% 2.93/1.02  
% 2.93/1.02  fof(f68,plain,(
% 2.93/1.02    r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))),
% 2.93/1.02    inference(cnf_transformation,[],[f41])).
% 2.93/1.02  
% 2.93/1.02  fof(f8,axiom,(
% 2.93/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f24,plain,(
% 2.93/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.02    inference(ennf_transformation,[],[f8])).
% 2.93/1.02  
% 2.93/1.02  fof(f54,plain,(
% 2.93/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.02    inference(cnf_transformation,[],[f24])).
% 2.93/1.02  
% 2.93/1.02  fof(f6,axiom,(
% 2.93/1.02    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f21,plain,(
% 2.93/1.02    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.93/1.02    inference(ennf_transformation,[],[f6])).
% 2.93/1.02  
% 2.93/1.02  fof(f50,plain,(
% 2.93/1.02    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/1.02    inference(cnf_transformation,[],[f21])).
% 2.93/1.02  
% 2.93/1.02  fof(f5,axiom,(
% 2.93/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f20,plain,(
% 2.93/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.93/1.02    inference(ennf_transformation,[],[f5])).
% 2.93/1.02  
% 2.93/1.02  fof(f33,plain,(
% 2.93/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.93/1.02    inference(nnf_transformation,[],[f20])).
% 2.93/1.02  
% 2.93/1.02  fof(f34,plain,(
% 2.93/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.93/1.02    inference(rectify,[],[f33])).
% 2.93/1.02  
% 2.93/1.02  fof(f35,plain,(
% 2.93/1.02    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 2.93/1.02    introduced(choice_axiom,[])).
% 2.93/1.02  
% 2.93/1.02  fof(f36,plain,(
% 2.93/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.93/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.93/1.02  
% 2.93/1.02  fof(f47,plain,(
% 2.93/1.02    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.93/1.02    inference(cnf_transformation,[],[f36])).
% 2.93/1.02  
% 2.93/1.02  fof(f7,axiom,(
% 2.93/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f22,plain,(
% 2.93/1.02    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.93/1.02    inference(ennf_transformation,[],[f7])).
% 2.93/1.02  
% 2.93/1.02  fof(f23,plain,(
% 2.93/1.02    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.93/1.02    inference(flattening,[],[f22])).
% 2.93/1.02  
% 2.93/1.02  fof(f37,plain,(
% 2.93/1.02    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.93/1.02    inference(nnf_transformation,[],[f23])).
% 2.93/1.02  
% 2.93/1.02  fof(f38,plain,(
% 2.93/1.02    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.93/1.02    inference(flattening,[],[f37])).
% 2.93/1.02  
% 2.93/1.02  fof(f52,plain,(
% 2.93/1.02    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.93/1.02    inference(cnf_transformation,[],[f38])).
% 2.93/1.02  
% 2.93/1.02  fof(f65,plain,(
% 2.93/1.02    v1_funct_1(sK4)),
% 2.93/1.02    inference(cnf_transformation,[],[f41])).
% 2.93/1.02  
% 2.93/1.02  fof(f69,plain,(
% 2.93/1.02    ( ! [X4] : (k1_funct_1(sK4,X4) != sK1 | ~m1_subset_1(X4,sK2)) )),
% 2.93/1.02    inference(cnf_transformation,[],[f41])).
% 2.93/1.02  
% 2.93/1.02  fof(f46,plain,(
% 2.93/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.93/1.02    inference(cnf_transformation,[],[f36])).
% 2.93/1.02  
% 2.93/1.02  fof(f4,axiom,(
% 2.93/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f19,plain,(
% 2.93/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.93/1.02    inference(ennf_transformation,[],[f4])).
% 2.93/1.02  
% 2.93/1.02  fof(f45,plain,(
% 2.93/1.02    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.93/1.02    inference(cnf_transformation,[],[f19])).
% 2.93/1.02  
% 2.93/1.02  fof(f12,axiom,(
% 2.93/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f28,plain,(
% 2.93/1.02    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.02    inference(ennf_transformation,[],[f12])).
% 2.93/1.02  
% 2.93/1.02  fof(f58,plain,(
% 2.93/1.02    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.02    inference(cnf_transformation,[],[f28])).
% 2.93/1.02  
% 2.93/1.02  fof(f9,axiom,(
% 2.93/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f25,plain,(
% 2.93/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/1.02    inference(ennf_transformation,[],[f9])).
% 2.93/1.02  
% 2.93/1.02  fof(f55,plain,(
% 2.93/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/1.02    inference(cnf_transformation,[],[f25])).
% 2.93/1.02  
% 2.93/1.02  fof(f3,axiom,(
% 2.93/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.02  
% 2.93/1.02  fof(f18,plain,(
% 2.93/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.93/1.02    inference(ennf_transformation,[],[f3])).
% 2.93/1.02  
% 2.93/1.02  fof(f44,plain,(
% 2.93/1.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.93/1.02    inference(cnf_transformation,[],[f18])).
% 2.93/1.02  
% 2.93/1.02  cnf(c_0,plain,
% 2.93/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.93/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1,plain,
% 2.93/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.93/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_320,plain,
% 2.93/1.02      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.93/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_321,plain,
% 2.93/1.02      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.93/1.02      inference(unflattening,[status(thm)],[c_320]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_3872,plain,
% 2.93/1.02      ( ~ r2_hidden(sK1,k1_xboole_0) ),
% 2.93/1.02      inference(instantiation,[status(thm)],[c_321]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_22,plain,
% 2.93/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.93/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.93/1.02      | k1_xboole_0 = X2 ),
% 2.93/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_26,negated_conjecture,
% 2.93/1.02      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.93/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_578,plain,
% 2.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.93/1.02      | sK3 != X2
% 2.93/1.02      | sK2 != X1
% 2.93/1.02      | sK4 != X0
% 2.93/1.02      | k1_xboole_0 = X2 ),
% 2.93/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_579,plain,
% 2.93/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.93/1.02      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.93/1.02      | k1_xboole_0 = sK3 ),
% 2.93/1.02      inference(unflattening,[status(thm)],[c_578]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_25,negated_conjecture,
% 2.93/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.93/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_581,plain,
% 2.93/1.02      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.93/1.02      inference(global_propositional_subsumption,
% 2.93/1.02                [status(thm)],
% 2.93/1.02                [c_579,c_25]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1261,plain,
% 2.93/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_14,plain,
% 2.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.93/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1266,plain,
% 2.93/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.93/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1875,plain,
% 2.93/1.02      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_1261,c_1266]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2084,plain,
% 2.93/1.02      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_581,c_1875]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_15,plain,
% 2.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.93/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1265,plain,
% 2.93/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.93/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1664,plain,
% 2.93/1.02      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_1261,c_1265]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_24,negated_conjecture,
% 2.93/1.02      ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
% 2.93/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1262,plain,
% 2.93/1.02      ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1718,plain,
% 2.93/1.02      ( r2_hidden(sK1,k2_relat_1(sK4)) = iProver_top ),
% 2.93/1.02      inference(demodulation,[status(thm)],[c_1664,c_1262]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_12,plain,
% 2.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.02      | v1_relat_1(X0) ),
% 2.93/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1268,plain,
% 2.93/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.93/1.02      | v1_relat_1(X0) = iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1632,plain,
% 2.93/1.02      ( v1_relat_1(sK4) = iProver_top ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_1261,c_1268]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_8,plain,
% 2.93/1.02      ( ~ v1_relat_1(X0)
% 2.93/1.02      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.93/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1269,plain,
% 2.93/1.02      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.93/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1667,plain,
% 2.93/1.02      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_1632,c_1269]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_6,plain,
% 2.93/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.93/1.02      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 2.93/1.02      | ~ v1_relat_1(X1) ),
% 2.93/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1271,plain,
% 2.93/1.02      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.93/1.02      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 2.93/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_10,plain,
% 2.93/1.02      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.93/1.02      | ~ v1_funct_1(X2)
% 2.93/1.02      | ~ v1_relat_1(X2)
% 2.93/1.02      | k1_funct_1(X2,X0) = X1 ),
% 2.93/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_27,negated_conjecture,
% 2.93/1.02      ( v1_funct_1(sK4) ),
% 2.93/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_331,plain,
% 2.93/1.02      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.93/1.02      | ~ v1_relat_1(X2)
% 2.93/1.02      | k1_funct_1(X2,X0) = X1
% 2.93/1.02      | sK4 != X2 ),
% 2.93/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_332,plain,
% 2.93/1.02      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 2.93/1.02      | ~ v1_relat_1(sK4)
% 2.93/1.02      | k1_funct_1(sK4,X0) = X1 ),
% 2.93/1.02      inference(unflattening,[status(thm)],[c_331]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1259,plain,
% 2.93/1.02      ( k1_funct_1(sK4,X0) = X1
% 2.93/1.02      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 2.93/1.02      | v1_relat_1(sK4) != iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_30,plain,
% 2.93/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_333,plain,
% 2.93/1.02      ( k1_funct_1(sK4,X0) = X1
% 2.93/1.02      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 2.93/1.02      | v1_relat_1(sK4) != iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1436,plain,
% 2.93/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.93/1.02      | v1_relat_1(sK4) ),
% 2.93/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1437,plain,
% 2.93/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.93/1.02      | v1_relat_1(sK4) = iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_1436]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1473,plain,
% 2.93/1.02      ( r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 2.93/1.02      | k1_funct_1(sK4,X0) = X1 ),
% 2.93/1.02      inference(global_propositional_subsumption,
% 2.93/1.02                [status(thm)],
% 2.93/1.02                [c_1259,c_30,c_333,c_1437]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1474,plain,
% 2.93/1.02      ( k1_funct_1(sK4,X0) = X1
% 2.93/1.02      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
% 2.93/1.02      inference(renaming,[status(thm)],[c_1473]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2511,plain,
% 2.93/1.02      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 2.93/1.02      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.93/1.02      | v1_relat_1(sK4) != iProver_top ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_1271,c_1474]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2745,plain,
% 2.93/1.02      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.93/1.02      | k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0 ),
% 2.93/1.02      inference(global_propositional_subsumption,
% 2.93/1.02                [status(thm)],
% 2.93/1.02                [c_2511,c_30,c_1437]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2746,plain,
% 2.93/1.02      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 2.93/1.02      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 2.93/1.02      inference(renaming,[status(thm)],[c_2745]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2755,plain,
% 2.93/1.02      ( k1_funct_1(sK4,sK0(X0,k1_relat_1(sK4),sK4)) = X0
% 2.93/1.02      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_1667,c_2746]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_3197,plain,
% 2.93/1.02      ( k1_funct_1(sK4,sK0(sK1,k1_relat_1(sK4),sK4)) = sK1 ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_1718,c_2755]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_23,negated_conjecture,
% 2.93/1.02      ( ~ m1_subset_1(X0,sK2) | k1_funct_1(sK4,X0) != sK1 ),
% 2.93/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1263,plain,
% 2.93/1.02      ( k1_funct_1(sK4,X0) != sK1 | m1_subset_1(X0,sK2) != iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_3283,plain,
% 2.93/1.02      ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),sK2) != iProver_top ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_3197,c_1263]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_3313,plain,
% 2.93/1.02      ( sK3 = k1_xboole_0
% 2.93/1.02      | m1_subset_1(sK0(sK1,sK2,sK4),sK2) != iProver_top ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_2084,c_3283]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_7,plain,
% 2.93/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.93/1.02      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 2.93/1.02      | ~ v1_relat_1(X1) ),
% 2.93/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1270,plain,
% 2.93/1.02      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.93/1.02      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 2.93/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2401,plain,
% 2.93/1.02      ( sK3 = k1_xboole_0
% 2.93/1.02      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.93/1.02      | r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top
% 2.93/1.02      | v1_relat_1(sK4) != iProver_top ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_2084,c_1270]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2927,plain,
% 2.93/1.02      ( r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top
% 2.93/1.02      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.93/1.02      | sK3 = k1_xboole_0 ),
% 2.93/1.02      inference(global_propositional_subsumption,
% 2.93/1.02                [status(thm)],
% 2.93/1.02                [c_2401,c_30,c_1437]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2928,plain,
% 2.93/1.02      ( sK3 = k1_xboole_0
% 2.93/1.02      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 2.93/1.02      | r2_hidden(sK0(X0,X1,sK4),sK2) = iProver_top ),
% 2.93/1.02      inference(renaming,[status(thm)],[c_2927]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_3,plain,
% 2.93/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.93/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1274,plain,
% 2.93/1.02      ( m1_subset_1(X0,X1) = iProver_top
% 2.93/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2936,plain,
% 2.93/1.02      ( sK3 = k1_xboole_0
% 2.93/1.02      | m1_subset_1(sK0(X0,X1,sK4),sK2) = iProver_top
% 2.93/1.02      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_2928,c_1274]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_3312,plain,
% 2.93/1.02      ( sK3 = k1_xboole_0
% 2.93/1.02      | r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4))) != iProver_top ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_2936,c_3283]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_3320,plain,
% 2.93/1.02      ( sK3 = k1_xboole_0
% 2.93/1.02      | r2_hidden(sK1,k2_relat_1(sK4)) != iProver_top ),
% 2.93/1.02      inference(light_normalisation,[status(thm)],[c_3312,c_1667]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_3434,plain,
% 2.93/1.02      ( sK3 = k1_xboole_0 ),
% 2.93/1.02      inference(global_propositional_subsumption,
% 2.93/1.02                [status(thm)],
% 2.93/1.02                [c_3313,c_1718,c_3320]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_16,plain,
% 2.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.93/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1264,plain,
% 2.93/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.93/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1870,plain,
% 2.93/1.02      ( k7_relset_1(sK2,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_1261,c_1264]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_13,plain,
% 2.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/1.02      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 2.93/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1267,plain,
% 2.93/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.93/1.02      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2148,plain,
% 2.93/1.02      ( m1_subset_1(k9_relat_1(sK4,X0),k1_zfmisc_1(sK3)) = iProver_top
% 2.93/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_1870,c_1267]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2227,plain,
% 2.93/1.02      ( m1_subset_1(k9_relat_1(sK4,X0),k1_zfmisc_1(sK3)) = iProver_top ),
% 2.93/1.02      inference(global_propositional_subsumption,
% 2.93/1.02                [status(thm)],
% 2.93/1.02                [c_2148,c_30]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2234,plain,
% 2.93/1.02      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_1667,c_2227]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2,plain,
% 2.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.93/1.02      | ~ r2_hidden(X2,X0)
% 2.93/1.02      | r2_hidden(X2,X1) ),
% 2.93/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_1275,plain,
% 2.93/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.93/1.02      | r2_hidden(X2,X0) != iProver_top
% 2.93/1.02      | r2_hidden(X2,X1) = iProver_top ),
% 2.93/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2393,plain,
% 2.93/1.02      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 2.93/1.02      | r2_hidden(X0,sK3) = iProver_top ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_2234,c_1275]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_2658,plain,
% 2.93/1.02      ( r2_hidden(sK1,sK3) = iProver_top ),
% 2.93/1.02      inference(superposition,[status(thm)],[c_1718,c_2393]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_3440,plain,
% 2.93/1.02      ( r2_hidden(sK1,k1_xboole_0) = iProver_top ),
% 2.93/1.02      inference(demodulation,[status(thm)],[c_3434,c_2658]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(c_3513,plain,
% 2.93/1.02      ( r2_hidden(sK1,k1_xboole_0) ),
% 2.93/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_3440]) ).
% 2.93/1.02  
% 2.93/1.02  cnf(contradiction,plain,
% 2.93/1.02      ( $false ),
% 2.93/1.02      inference(minisat,[status(thm)],[c_3872,c_3513]) ).
% 2.93/1.02  
% 2.93/1.02  
% 2.93/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.93/1.02  
% 2.93/1.02  ------                               Statistics
% 2.93/1.02  
% 2.93/1.02  ------ General
% 2.93/1.02  
% 2.93/1.02  abstr_ref_over_cycles:                  0
% 2.93/1.02  abstr_ref_under_cycles:                 0
% 2.93/1.02  gc_basic_clause_elim:                   0
% 2.93/1.02  forced_gc_time:                         0
% 2.93/1.02  parsing_time:                           0.008
% 2.93/1.02  unif_index_cands_time:                  0.
% 2.93/1.02  unif_index_add_time:                    0.
% 2.93/1.02  orderings_time:                         0.
% 2.93/1.02  out_proof_time:                         0.009
% 2.93/1.02  total_time:                             0.103
% 2.93/1.02  num_of_symbols:                         53
% 2.93/1.02  num_of_terms:                           2922
% 2.93/1.02  
% 2.93/1.02  ------ Preprocessing
% 2.93/1.02  
% 2.93/1.02  num_of_splits:                          0
% 2.93/1.02  num_of_split_atoms:                     0
% 2.93/1.02  num_of_reused_defs:                     0
% 2.93/1.02  num_eq_ax_congr_red:                    34
% 2.93/1.02  num_of_sem_filtered_clauses:            1
% 2.93/1.02  num_of_subtypes:                        0
% 2.93/1.02  monotx_restored_types:                  0
% 2.93/1.02  sat_num_of_epr_types:                   0
% 2.93/1.02  sat_num_of_non_cyclic_types:            0
% 2.93/1.02  sat_guarded_non_collapsed_types:        0
% 2.93/1.02  num_pure_diseq_elim:                    0
% 2.93/1.02  simp_replaced_by:                       0
% 2.93/1.02  res_preprocessed:                       121
% 2.93/1.02  prep_upred:                             0
% 2.93/1.02  prep_unflattend:                        45
% 2.93/1.02  smt_new_axioms:                         0
% 2.93/1.02  pred_elim_cands:                        3
% 2.93/1.02  pred_elim:                              3
% 2.93/1.02  pred_elim_cl:                           6
% 2.93/1.02  pred_elim_cycles:                       6
% 2.93/1.02  merged_defs:                            0
% 2.93/1.02  merged_defs_ncl:                        0
% 2.93/1.02  bin_hyper_res:                          0
% 2.93/1.02  prep_cycles:                            4
% 2.93/1.02  pred_elim_time:                         0.005
% 2.93/1.02  splitting_time:                         0.
% 2.93/1.02  sem_filter_time:                        0.
% 2.93/1.02  monotx_time:                            0.
% 2.93/1.02  subtype_inf_time:                       0.
% 2.93/1.02  
% 2.93/1.02  ------ Problem properties
% 2.93/1.02  
% 2.93/1.02  clauses:                                22
% 2.93/1.02  conjectures:                            3
% 2.93/1.02  epr:                                    2
% 2.93/1.02  horn:                                   20
% 2.93/1.02  ground:                                 5
% 2.93/1.02  unary:                                  3
% 2.93/1.02  binary:                                 9
% 2.93/1.02  lits:                                   54
% 2.93/1.02  lits_eq:                                13
% 2.93/1.02  fd_pure:                                0
% 2.93/1.02  fd_pseudo:                              0
% 2.93/1.02  fd_cond:                                0
% 2.93/1.02  fd_pseudo_cond:                         1
% 2.93/1.02  ac_symbols:                             0
% 2.93/1.02  
% 2.93/1.02  ------ Propositional Solver
% 2.93/1.02  
% 2.93/1.02  prop_solver_calls:                      31
% 2.93/1.02  prop_fast_solver_calls:                 839
% 2.93/1.02  smt_solver_calls:                       0
% 2.93/1.02  smt_fast_solver_calls:                  0
% 2.93/1.02  prop_num_of_clauses:                    1148
% 2.93/1.02  prop_preprocess_simplified:             4395
% 2.93/1.02  prop_fo_subsumed:                       9
% 2.93/1.02  prop_solver_time:                       0.
% 2.93/1.02  smt_solver_time:                        0.
% 2.93/1.02  smt_fast_solver_time:                   0.
% 2.93/1.02  prop_fast_solver_time:                  0.
% 2.93/1.02  prop_unsat_core_time:                   0.
% 2.93/1.02  
% 2.93/1.02  ------ QBF
% 2.93/1.02  
% 2.93/1.02  qbf_q_res:                              0
% 2.93/1.02  qbf_num_tautologies:                    0
% 2.93/1.02  qbf_prep_cycles:                        0
% 2.93/1.02  
% 2.93/1.02  ------ BMC1
% 2.93/1.02  
% 2.93/1.02  bmc1_current_bound:                     -1
% 2.93/1.02  bmc1_last_solved_bound:                 -1
% 2.93/1.02  bmc1_unsat_core_size:                   -1
% 2.93/1.02  bmc1_unsat_core_parents_size:           -1
% 2.93/1.02  bmc1_merge_next_fun:                    0
% 2.93/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.93/1.02  
% 2.93/1.02  ------ Instantiation
% 2.93/1.02  
% 2.93/1.02  inst_num_of_clauses:                    366
% 2.93/1.02  inst_num_in_passive:                    107
% 2.93/1.02  inst_num_in_active:                     229
% 2.93/1.02  inst_num_in_unprocessed:                29
% 2.93/1.02  inst_num_of_loops:                      318
% 2.93/1.02  inst_num_of_learning_restarts:          0
% 2.93/1.02  inst_num_moves_active_passive:          82
% 2.93/1.02  inst_lit_activity:                      0
% 2.93/1.02  inst_lit_activity_moves:                0
% 2.93/1.02  inst_num_tautologies:                   0
% 2.93/1.02  inst_num_prop_implied:                  0
% 2.93/1.02  inst_num_existing_simplified:           0
% 2.93/1.02  inst_num_eq_res_simplified:             0
% 2.93/1.02  inst_num_child_elim:                    0
% 2.93/1.02  inst_num_of_dismatching_blockings:      55
% 2.93/1.02  inst_num_of_non_proper_insts:           427
% 2.93/1.02  inst_num_of_duplicates:                 0
% 2.93/1.02  inst_inst_num_from_inst_to_res:         0
% 2.93/1.02  inst_dismatching_checking_time:         0.
% 2.93/1.02  
% 2.93/1.02  ------ Resolution
% 2.93/1.02  
% 2.93/1.02  res_num_of_clauses:                     0
% 2.93/1.02  res_num_in_passive:                     0
% 2.93/1.02  res_num_in_active:                      0
% 2.93/1.02  res_num_of_loops:                       125
% 2.93/1.02  res_forward_subset_subsumed:            66
% 2.93/1.02  res_backward_subset_subsumed:           2
% 2.93/1.02  res_forward_subsumed:                   0
% 2.93/1.02  res_backward_subsumed:                  0
% 2.93/1.02  res_forward_subsumption_resolution:     0
% 2.93/1.02  res_backward_subsumption_resolution:    0
% 2.93/1.02  res_clause_to_clause_subsumption:       229
% 2.93/1.02  res_orphan_elimination:                 0
% 2.93/1.02  res_tautology_del:                      105
% 2.93/1.02  res_num_eq_res_simplified:              0
% 2.93/1.02  res_num_sel_changes:                    0
% 2.93/1.02  res_moves_from_active_to_pass:          0
% 2.93/1.02  
% 2.93/1.02  ------ Superposition
% 2.93/1.02  
% 2.93/1.02  sup_time_total:                         0.
% 2.93/1.02  sup_time_generating:                    0.
% 2.93/1.02  sup_time_sim_full:                      0.
% 2.93/1.02  sup_time_sim_immed:                     0.
% 2.93/1.02  
% 2.93/1.02  sup_num_of_clauses:                     97
% 2.93/1.02  sup_num_in_active:                      43
% 2.93/1.02  sup_num_in_passive:                     54
% 2.93/1.02  sup_num_of_loops:                       62
% 2.93/1.02  sup_fw_superposition:                   50
% 2.93/1.02  sup_bw_superposition:                   48
% 2.93/1.02  sup_immediate_simplified:               12
% 2.93/1.02  sup_given_eliminated:                   0
% 2.93/1.02  comparisons_done:                       0
% 2.93/1.02  comparisons_avoided:                    6
% 2.93/1.02  
% 2.93/1.02  ------ Simplifications
% 2.93/1.02  
% 2.93/1.02  
% 2.93/1.02  sim_fw_subset_subsumed:                 6
% 2.93/1.02  sim_bw_subset_subsumed:                 3
% 2.93/1.02  sim_fw_subsumed:                        3
% 2.93/1.02  sim_bw_subsumed:                        1
% 2.93/1.02  sim_fw_subsumption_res:                 1
% 2.93/1.02  sim_bw_subsumption_res:                 0
% 2.93/1.02  sim_tautology_del:                      1
% 2.93/1.02  sim_eq_tautology_del:                   2
% 2.93/1.02  sim_eq_res_simp:                        1
% 2.93/1.02  sim_fw_demodulated:                     0
% 2.93/1.02  sim_bw_demodulated:                     17
% 2.93/1.02  sim_light_normalised:                   2
% 2.93/1.02  sim_joinable_taut:                      0
% 2.93/1.02  sim_joinable_simp:                      0
% 2.93/1.02  sim_ac_normalised:                      0
% 2.93/1.02  sim_smt_subsumption:                    0
% 2.93/1.02  
%------------------------------------------------------------------------------

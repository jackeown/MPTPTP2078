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
% DateTime   : Thu Dec  3 12:04:08 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 400 expanded)
%              Number of clauses        :   79 ( 153 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :   25
%              Number of atoms          :  399 (1395 expanded)
%              Number of equality atoms :  185 ( 274 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f15])).

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
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
        & r1_tarski(X0,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)
      & r1_tarski(sK1,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)
    & r1_tarski(sK1,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f40])).

fof(f69,plain,(
    r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(nnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f70,plain,(
    ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_978,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_974,plain,
    ( r1_tarski(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_362,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_363,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_597,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != sK4
    | sK2 != X1
    | sK1 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_363])).

cnf(c_598,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_660,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_598])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_398,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_399,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_1100,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_399])).

cnf(c_1203,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_660,c_1100])).

cnf(c_12,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_407,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_408,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_555,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_408])).

cnf(c_556,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),X0)
    | k7_relat_1(sK4,X0) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_727,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),X0)
    | k7_relat_1(sK4,X0) = sK4
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_556])).

cnf(c_971,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_728,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_556])).

cnf(c_757,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_758,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_730,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1123,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_11,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_570,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_408])).

cnf(c_571,plain,
    ( r1_tarski(k7_relat_1(sK4,X0),sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_724,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_571])).

cnf(c_1125,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_1127,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_1577,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | k7_relat_1(sK4,X0) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_971,c_757,c_758,c_1123,c_1127])).

cnf(c_1578,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1577])).

cnf(c_1586,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_1578])).

cnf(c_1952,plain,
    ( k7_relat_1(sK4,sK3) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_974,c_1586])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_303,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_496,plain,
    ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_303])).

cnf(c_664,plain,
    ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_496])).

cnf(c_1143,plain,
    ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_664])).

cnf(c_15,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != X0
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_350,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK4 != k2_partfun1(sK1,sK2,sK4,sK3) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_507,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution_lifted,[status(thm)],[c_26,c_350])).

cnf(c_663,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_507])).

cnf(c_1433,plain,
    ( k7_relat_1(sK4,sK3) != sK4 ),
    inference(demodulation,[status(thm)],[c_1143,c_663])).

cnf(c_2032,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1952,c_1433])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_484,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k1_xboole_0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_288])).

cnf(c_485,plain,
    ( ~ r2_hidden(X0,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_973,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_2044,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2032,c_973])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2056,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2044,c_7])).

cnf(c_2057,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2056])).

cnf(c_2232,plain,
    ( r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_2057])).

cnf(c_725,plain,
    ( r1_tarski(k7_relat_1(sK4,X0),sK4)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_571])).

cnf(c_968,plain,
    ( r1_tarski(k7_relat_1(sK4,X0),sK4) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_726,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_571])).

cnf(c_750,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_751,plain,
    ( r1_tarski(k7_relat_1(sK4,X0),sK4) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_1471,plain,
    ( r1_tarski(k7_relat_1(sK4,X0),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_968,c_750,c_751,c_1123,c_1127])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_976,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1674,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | r1_tarski(sK4,k7_relat_1(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1471,c_976])).

cnf(c_2239,plain,
    ( k7_relat_1(sK4,X0) = sK4 ),
    inference(superposition,[status(thm)],[c_2232,c_1674])).

cnf(c_2329,plain,
    ( sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_2239,c_1433])).

cnf(c_2330,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2329])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:25:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.72/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/0.99  
% 2.72/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.72/0.99  
% 2.72/0.99  ------  iProver source info
% 2.72/0.99  
% 2.72/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.72/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.72/0.99  git: non_committed_changes: false
% 2.72/0.99  git: last_make_outside_of_git: false
% 2.72/0.99  
% 2.72/0.99  ------ 
% 2.72/0.99  
% 2.72/0.99  ------ Input Options
% 2.72/0.99  
% 2.72/0.99  --out_options                           all
% 2.72/0.99  --tptp_safe_out                         true
% 2.72/0.99  --problem_path                          ""
% 2.72/0.99  --include_path                          ""
% 2.72/0.99  --clausifier                            res/vclausify_rel
% 2.72/0.99  --clausifier_options                    --mode clausify
% 2.72/0.99  --stdin                                 false
% 2.72/0.99  --stats_out                             all
% 2.72/0.99  
% 2.72/0.99  ------ General Options
% 2.72/0.99  
% 2.72/0.99  --fof                                   false
% 2.72/0.99  --time_out_real                         305.
% 2.72/0.99  --time_out_virtual                      -1.
% 2.72/0.99  --symbol_type_check                     false
% 2.72/0.99  --clausify_out                          false
% 2.72/0.99  --sig_cnt_out                           false
% 2.72/0.99  --trig_cnt_out                          false
% 2.72/0.99  --trig_cnt_out_tolerance                1.
% 2.72/0.99  --trig_cnt_out_sk_spl                   false
% 2.72/0.99  --abstr_cl_out                          false
% 2.72/0.99  
% 2.72/0.99  ------ Global Options
% 2.72/0.99  
% 2.72/0.99  --schedule                              default
% 2.72/0.99  --add_important_lit                     false
% 2.72/0.99  --prop_solver_per_cl                    1000
% 2.72/0.99  --min_unsat_core                        false
% 2.72/0.99  --soft_assumptions                      false
% 2.72/0.99  --soft_lemma_size                       3
% 2.72/0.99  --prop_impl_unit_size                   0
% 2.72/0.99  --prop_impl_unit                        []
% 2.72/0.99  --share_sel_clauses                     true
% 2.72/0.99  --reset_solvers                         false
% 2.72/0.99  --bc_imp_inh                            [conj_cone]
% 2.72/0.99  --conj_cone_tolerance                   3.
% 2.72/0.99  --extra_neg_conj                        none
% 2.72/0.99  --large_theory_mode                     true
% 2.72/0.99  --prolific_symb_bound                   200
% 2.72/0.99  --lt_threshold                          2000
% 2.72/0.99  --clause_weak_htbl                      true
% 2.72/0.99  --gc_record_bc_elim                     false
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing Options
% 2.72/0.99  
% 2.72/0.99  --preprocessing_flag                    true
% 2.72/0.99  --time_out_prep_mult                    0.1
% 2.72/0.99  --splitting_mode                        input
% 2.72/0.99  --splitting_grd                         true
% 2.72/0.99  --splitting_cvd                         false
% 2.72/0.99  --splitting_cvd_svl                     false
% 2.72/0.99  --splitting_nvd                         32
% 2.72/0.99  --sub_typing                            true
% 2.72/0.99  --prep_gs_sim                           true
% 2.72/0.99  --prep_unflatten                        true
% 2.72/0.99  --prep_res_sim                          true
% 2.72/0.99  --prep_upred                            true
% 2.72/0.99  --prep_sem_filter                       exhaustive
% 2.72/0.99  --prep_sem_filter_out                   false
% 2.72/0.99  --pred_elim                             true
% 2.72/0.99  --res_sim_input                         true
% 2.72/0.99  --eq_ax_congr_red                       true
% 2.72/0.99  --pure_diseq_elim                       true
% 2.72/0.99  --brand_transform                       false
% 2.72/0.99  --non_eq_to_eq                          false
% 2.72/0.99  --prep_def_merge                        true
% 2.72/0.99  --prep_def_merge_prop_impl              false
% 2.72/0.99  --prep_def_merge_mbd                    true
% 2.72/0.99  --prep_def_merge_tr_red                 false
% 2.72/0.99  --prep_def_merge_tr_cl                  false
% 2.72/0.99  --smt_preprocessing                     true
% 2.72/0.99  --smt_ac_axioms                         fast
% 2.72/0.99  --preprocessed_out                      false
% 2.72/0.99  --preprocessed_stats                    false
% 2.72/0.99  
% 2.72/0.99  ------ Abstraction refinement Options
% 2.72/0.99  
% 2.72/0.99  --abstr_ref                             []
% 2.72/0.99  --abstr_ref_prep                        false
% 2.72/0.99  --abstr_ref_until_sat                   false
% 2.72/0.99  --abstr_ref_sig_restrict                funpre
% 2.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.99  --abstr_ref_under                       []
% 2.72/0.99  
% 2.72/0.99  ------ SAT Options
% 2.72/0.99  
% 2.72/0.99  --sat_mode                              false
% 2.72/0.99  --sat_fm_restart_options                ""
% 2.72/0.99  --sat_gr_def                            false
% 2.72/0.99  --sat_epr_types                         true
% 2.72/0.99  --sat_non_cyclic_types                  false
% 2.72/0.99  --sat_finite_models                     false
% 2.72/0.99  --sat_fm_lemmas                         false
% 2.72/0.99  --sat_fm_prep                           false
% 2.72/0.99  --sat_fm_uc_incr                        true
% 2.72/0.99  --sat_out_model                         small
% 2.72/0.99  --sat_out_clauses                       false
% 2.72/0.99  
% 2.72/0.99  ------ QBF Options
% 2.72/0.99  
% 2.72/0.99  --qbf_mode                              false
% 2.72/0.99  --qbf_elim_univ                         false
% 2.72/0.99  --qbf_dom_inst                          none
% 2.72/0.99  --qbf_dom_pre_inst                      false
% 2.72/0.99  --qbf_sk_in                             false
% 2.72/0.99  --qbf_pred_elim                         true
% 2.72/0.99  --qbf_split                             512
% 2.72/0.99  
% 2.72/0.99  ------ BMC1 Options
% 2.72/0.99  
% 2.72/0.99  --bmc1_incremental                      false
% 2.72/0.99  --bmc1_axioms                           reachable_all
% 2.72/0.99  --bmc1_min_bound                        0
% 2.72/0.99  --bmc1_max_bound                        -1
% 2.72/0.99  --bmc1_max_bound_default                -1
% 2.72/0.99  --bmc1_symbol_reachability              true
% 2.72/0.99  --bmc1_property_lemmas                  false
% 2.72/0.99  --bmc1_k_induction                      false
% 2.72/0.99  --bmc1_non_equiv_states                 false
% 2.72/0.99  --bmc1_deadlock                         false
% 2.72/0.99  --bmc1_ucm                              false
% 2.72/0.99  --bmc1_add_unsat_core                   none
% 2.72/0.99  --bmc1_unsat_core_children              false
% 2.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.99  --bmc1_out_stat                         full
% 2.72/0.99  --bmc1_ground_init                      false
% 2.72/0.99  --bmc1_pre_inst_next_state              false
% 2.72/0.99  --bmc1_pre_inst_state                   false
% 2.72/0.99  --bmc1_pre_inst_reach_state             false
% 2.72/0.99  --bmc1_out_unsat_core                   false
% 2.72/0.99  --bmc1_aig_witness_out                  false
% 2.72/0.99  --bmc1_verbose                          false
% 2.72/0.99  --bmc1_dump_clauses_tptp                false
% 2.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.99  --bmc1_dump_file                        -
% 2.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.99  --bmc1_ucm_extend_mode                  1
% 2.72/0.99  --bmc1_ucm_init_mode                    2
% 2.72/0.99  --bmc1_ucm_cone_mode                    none
% 2.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.99  --bmc1_ucm_relax_model                  4
% 2.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.99  --bmc1_ucm_layered_model                none
% 2.72/0.99  --bmc1_ucm_max_lemma_size               10
% 2.72/0.99  
% 2.72/0.99  ------ AIG Options
% 2.72/0.99  
% 2.72/0.99  --aig_mode                              false
% 2.72/0.99  
% 2.72/0.99  ------ Instantiation Options
% 2.72/0.99  
% 2.72/0.99  --instantiation_flag                    true
% 2.72/0.99  --inst_sos_flag                         false
% 2.72/0.99  --inst_sos_phase                        true
% 2.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.99  --inst_lit_sel_side                     num_symb
% 2.72/0.99  --inst_solver_per_active                1400
% 2.72/0.99  --inst_solver_calls_frac                1.
% 2.72/0.99  --inst_passive_queue_type               priority_queues
% 2.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.99  --inst_passive_queues_freq              [25;2]
% 2.72/0.99  --inst_dismatching                      true
% 2.72/0.99  --inst_eager_unprocessed_to_passive     true
% 2.72/0.99  --inst_prop_sim_given                   true
% 2.72/0.99  --inst_prop_sim_new                     false
% 2.72/0.99  --inst_subs_new                         false
% 2.72/0.99  --inst_eq_res_simp                      false
% 2.72/0.99  --inst_subs_given                       false
% 2.72/0.99  --inst_orphan_elimination               true
% 2.72/0.99  --inst_learning_loop_flag               true
% 2.72/0.99  --inst_learning_start                   3000
% 2.72/0.99  --inst_learning_factor                  2
% 2.72/0.99  --inst_start_prop_sim_after_learn       3
% 2.72/0.99  --inst_sel_renew                        solver
% 2.72/0.99  --inst_lit_activity_flag                true
% 2.72/0.99  --inst_restr_to_given                   false
% 2.72/0.99  --inst_activity_threshold               500
% 2.72/0.99  --inst_out_proof                        true
% 2.72/0.99  
% 2.72/0.99  ------ Resolution Options
% 2.72/0.99  
% 2.72/0.99  --resolution_flag                       true
% 2.72/0.99  --res_lit_sel                           adaptive
% 2.72/0.99  --res_lit_sel_side                      none
% 2.72/0.99  --res_ordering                          kbo
% 2.72/0.99  --res_to_prop_solver                    active
% 2.72/0.99  --res_prop_simpl_new                    false
% 2.72/0.99  --res_prop_simpl_given                  true
% 2.72/0.99  --res_passive_queue_type                priority_queues
% 2.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.99  --res_passive_queues_freq               [15;5]
% 2.72/0.99  --res_forward_subs                      full
% 2.72/0.99  --res_backward_subs                     full
% 2.72/0.99  --res_forward_subs_resolution           true
% 2.72/0.99  --res_backward_subs_resolution          true
% 2.72/0.99  --res_orphan_elimination                true
% 2.72/0.99  --res_time_limit                        2.
% 2.72/0.99  --res_out_proof                         true
% 2.72/0.99  
% 2.72/0.99  ------ Superposition Options
% 2.72/0.99  
% 2.72/0.99  --superposition_flag                    true
% 2.72/0.99  --sup_passive_queue_type                priority_queues
% 2.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.99  --demod_completeness_check              fast
% 2.72/0.99  --demod_use_ground                      true
% 2.72/0.99  --sup_to_prop_solver                    passive
% 2.72/0.99  --sup_prop_simpl_new                    true
% 2.72/0.99  --sup_prop_simpl_given                  true
% 2.72/0.99  --sup_fun_splitting                     false
% 2.72/0.99  --sup_smt_interval                      50000
% 2.72/0.99  
% 2.72/0.99  ------ Superposition Simplification Setup
% 2.72/0.99  
% 2.72/0.99  --sup_indices_passive                   []
% 2.72/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_full_bw                           [BwDemod]
% 2.72/0.99  --sup_immed_triv                        [TrivRules]
% 2.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_immed_bw_main                     []
% 2.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.99  
% 2.72/0.99  ------ Combination Options
% 2.72/0.99  
% 2.72/0.99  --comb_res_mult                         3
% 2.72/0.99  --comb_sup_mult                         2
% 2.72/0.99  --comb_inst_mult                        10
% 2.72/0.99  
% 2.72/0.99  ------ Debug Options
% 2.72/0.99  
% 2.72/0.99  --dbg_backtrace                         false
% 2.72/0.99  --dbg_dump_prop_clauses                 false
% 2.72/0.99  --dbg_dump_prop_clauses_file            -
% 2.72/0.99  --dbg_out_stat                          false
% 2.72/0.99  ------ Parsing...
% 2.72/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.72/0.99  ------ Proving...
% 2.72/0.99  ------ Problem Properties 
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  clauses                                 22
% 2.72/0.99  conjectures                             1
% 2.72/0.99  EPR                                     6
% 2.72/0.99  Horn                                    16
% 2.72/0.99  unary                                   5
% 2.72/0.99  binary                                  11
% 2.72/0.99  lits                                    46
% 2.72/0.99  lits eq                                 24
% 2.72/0.99  fd_pure                                 0
% 2.72/0.99  fd_pseudo                               0
% 2.72/0.99  fd_cond                                 1
% 2.72/0.99  fd_pseudo_cond                          1
% 2.72/0.99  AC symbols                              0
% 2.72/0.99  
% 2.72/0.99  ------ Schedule dynamic 5 is on 
% 2.72/0.99  
% 2.72/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  ------ 
% 2.72/0.99  Current options:
% 2.72/0.99  ------ 
% 2.72/0.99  
% 2.72/0.99  ------ Input Options
% 2.72/0.99  
% 2.72/0.99  --out_options                           all
% 2.72/0.99  --tptp_safe_out                         true
% 2.72/0.99  --problem_path                          ""
% 2.72/0.99  --include_path                          ""
% 2.72/0.99  --clausifier                            res/vclausify_rel
% 2.72/0.99  --clausifier_options                    --mode clausify
% 2.72/0.99  --stdin                                 false
% 2.72/0.99  --stats_out                             all
% 2.72/0.99  
% 2.72/0.99  ------ General Options
% 2.72/0.99  
% 2.72/0.99  --fof                                   false
% 2.72/0.99  --time_out_real                         305.
% 2.72/0.99  --time_out_virtual                      -1.
% 2.72/0.99  --symbol_type_check                     false
% 2.72/0.99  --clausify_out                          false
% 2.72/0.99  --sig_cnt_out                           false
% 2.72/0.99  --trig_cnt_out                          false
% 2.72/0.99  --trig_cnt_out_tolerance                1.
% 2.72/0.99  --trig_cnt_out_sk_spl                   false
% 2.72/0.99  --abstr_cl_out                          false
% 2.72/0.99  
% 2.72/0.99  ------ Global Options
% 2.72/0.99  
% 2.72/0.99  --schedule                              default
% 2.72/0.99  --add_important_lit                     false
% 2.72/0.99  --prop_solver_per_cl                    1000
% 2.72/0.99  --min_unsat_core                        false
% 2.72/0.99  --soft_assumptions                      false
% 2.72/0.99  --soft_lemma_size                       3
% 2.72/0.99  --prop_impl_unit_size                   0
% 2.72/0.99  --prop_impl_unit                        []
% 2.72/0.99  --share_sel_clauses                     true
% 2.72/0.99  --reset_solvers                         false
% 2.72/0.99  --bc_imp_inh                            [conj_cone]
% 2.72/0.99  --conj_cone_tolerance                   3.
% 2.72/0.99  --extra_neg_conj                        none
% 2.72/0.99  --large_theory_mode                     true
% 2.72/0.99  --prolific_symb_bound                   200
% 2.72/0.99  --lt_threshold                          2000
% 2.72/0.99  --clause_weak_htbl                      true
% 2.72/0.99  --gc_record_bc_elim                     false
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing Options
% 2.72/0.99  
% 2.72/0.99  --preprocessing_flag                    true
% 2.72/0.99  --time_out_prep_mult                    0.1
% 2.72/0.99  --splitting_mode                        input
% 2.72/0.99  --splitting_grd                         true
% 2.72/0.99  --splitting_cvd                         false
% 2.72/0.99  --splitting_cvd_svl                     false
% 2.72/0.99  --splitting_nvd                         32
% 2.72/0.99  --sub_typing                            true
% 2.72/0.99  --prep_gs_sim                           true
% 2.72/0.99  --prep_unflatten                        true
% 2.72/0.99  --prep_res_sim                          true
% 2.72/0.99  --prep_upred                            true
% 2.72/0.99  --prep_sem_filter                       exhaustive
% 2.72/0.99  --prep_sem_filter_out                   false
% 2.72/0.99  --pred_elim                             true
% 2.72/0.99  --res_sim_input                         true
% 2.72/0.99  --eq_ax_congr_red                       true
% 2.72/0.99  --pure_diseq_elim                       true
% 2.72/0.99  --brand_transform                       false
% 2.72/0.99  --non_eq_to_eq                          false
% 2.72/0.99  --prep_def_merge                        true
% 2.72/0.99  --prep_def_merge_prop_impl              false
% 2.72/0.99  --prep_def_merge_mbd                    true
% 2.72/0.99  --prep_def_merge_tr_red                 false
% 2.72/0.99  --prep_def_merge_tr_cl                  false
% 2.72/0.99  --smt_preprocessing                     true
% 2.72/0.99  --smt_ac_axioms                         fast
% 2.72/0.99  --preprocessed_out                      false
% 2.72/0.99  --preprocessed_stats                    false
% 2.72/0.99  
% 2.72/0.99  ------ Abstraction refinement Options
% 2.72/0.99  
% 2.72/0.99  --abstr_ref                             []
% 2.72/0.99  --abstr_ref_prep                        false
% 2.72/0.99  --abstr_ref_until_sat                   false
% 2.72/0.99  --abstr_ref_sig_restrict                funpre
% 2.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.99  --abstr_ref_under                       []
% 2.72/0.99  
% 2.72/0.99  ------ SAT Options
% 2.72/0.99  
% 2.72/0.99  --sat_mode                              false
% 2.72/0.99  --sat_fm_restart_options                ""
% 2.72/0.99  --sat_gr_def                            false
% 2.72/0.99  --sat_epr_types                         true
% 2.72/0.99  --sat_non_cyclic_types                  false
% 2.72/0.99  --sat_finite_models                     false
% 2.72/0.99  --sat_fm_lemmas                         false
% 2.72/0.99  --sat_fm_prep                           false
% 2.72/0.99  --sat_fm_uc_incr                        true
% 2.72/0.99  --sat_out_model                         small
% 2.72/0.99  --sat_out_clauses                       false
% 2.72/0.99  
% 2.72/0.99  ------ QBF Options
% 2.72/0.99  
% 2.72/0.99  --qbf_mode                              false
% 2.72/0.99  --qbf_elim_univ                         false
% 2.72/0.99  --qbf_dom_inst                          none
% 2.72/0.99  --qbf_dom_pre_inst                      false
% 2.72/0.99  --qbf_sk_in                             false
% 2.72/0.99  --qbf_pred_elim                         true
% 2.72/0.99  --qbf_split                             512
% 2.72/0.99  
% 2.72/0.99  ------ BMC1 Options
% 2.72/0.99  
% 2.72/0.99  --bmc1_incremental                      false
% 2.72/0.99  --bmc1_axioms                           reachable_all
% 2.72/0.99  --bmc1_min_bound                        0
% 2.72/0.99  --bmc1_max_bound                        -1
% 2.72/0.99  --bmc1_max_bound_default                -1
% 2.72/0.99  --bmc1_symbol_reachability              true
% 2.72/0.99  --bmc1_property_lemmas                  false
% 2.72/0.99  --bmc1_k_induction                      false
% 2.72/0.99  --bmc1_non_equiv_states                 false
% 2.72/0.99  --bmc1_deadlock                         false
% 2.72/0.99  --bmc1_ucm                              false
% 2.72/0.99  --bmc1_add_unsat_core                   none
% 2.72/0.99  --bmc1_unsat_core_children              false
% 2.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.99  --bmc1_out_stat                         full
% 2.72/0.99  --bmc1_ground_init                      false
% 2.72/0.99  --bmc1_pre_inst_next_state              false
% 2.72/0.99  --bmc1_pre_inst_state                   false
% 2.72/0.99  --bmc1_pre_inst_reach_state             false
% 2.72/0.99  --bmc1_out_unsat_core                   false
% 2.72/0.99  --bmc1_aig_witness_out                  false
% 2.72/0.99  --bmc1_verbose                          false
% 2.72/0.99  --bmc1_dump_clauses_tptp                false
% 2.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.99  --bmc1_dump_file                        -
% 2.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.99  --bmc1_ucm_extend_mode                  1
% 2.72/0.99  --bmc1_ucm_init_mode                    2
% 2.72/0.99  --bmc1_ucm_cone_mode                    none
% 2.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.99  --bmc1_ucm_relax_model                  4
% 2.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.99  --bmc1_ucm_layered_model                none
% 2.72/0.99  --bmc1_ucm_max_lemma_size               10
% 2.72/0.99  
% 2.72/0.99  ------ AIG Options
% 2.72/0.99  
% 2.72/0.99  --aig_mode                              false
% 2.72/0.99  
% 2.72/0.99  ------ Instantiation Options
% 2.72/0.99  
% 2.72/0.99  --instantiation_flag                    true
% 2.72/0.99  --inst_sos_flag                         false
% 2.72/0.99  --inst_sos_phase                        true
% 2.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.99  --inst_lit_sel_side                     none
% 2.72/0.99  --inst_solver_per_active                1400
% 2.72/0.99  --inst_solver_calls_frac                1.
% 2.72/0.99  --inst_passive_queue_type               priority_queues
% 2.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.99  --inst_passive_queues_freq              [25;2]
% 2.72/0.99  --inst_dismatching                      true
% 2.72/0.99  --inst_eager_unprocessed_to_passive     true
% 2.72/0.99  --inst_prop_sim_given                   true
% 2.72/0.99  --inst_prop_sim_new                     false
% 2.72/0.99  --inst_subs_new                         false
% 2.72/0.99  --inst_eq_res_simp                      false
% 2.72/0.99  --inst_subs_given                       false
% 2.72/0.99  --inst_orphan_elimination               true
% 2.72/0.99  --inst_learning_loop_flag               true
% 2.72/0.99  --inst_learning_start                   3000
% 2.72/0.99  --inst_learning_factor                  2
% 2.72/0.99  --inst_start_prop_sim_after_learn       3
% 2.72/0.99  --inst_sel_renew                        solver
% 2.72/0.99  --inst_lit_activity_flag                true
% 2.72/0.99  --inst_restr_to_given                   false
% 2.72/0.99  --inst_activity_threshold               500
% 2.72/0.99  --inst_out_proof                        true
% 2.72/0.99  
% 2.72/0.99  ------ Resolution Options
% 2.72/0.99  
% 2.72/0.99  --resolution_flag                       false
% 2.72/0.99  --res_lit_sel                           adaptive
% 2.72/0.99  --res_lit_sel_side                      none
% 2.72/0.99  --res_ordering                          kbo
% 2.72/0.99  --res_to_prop_solver                    active
% 2.72/0.99  --res_prop_simpl_new                    false
% 2.72/0.99  --res_prop_simpl_given                  true
% 2.72/0.99  --res_passive_queue_type                priority_queues
% 2.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.99  --res_passive_queues_freq               [15;5]
% 2.72/0.99  --res_forward_subs                      full
% 2.72/0.99  --res_backward_subs                     full
% 2.72/0.99  --res_forward_subs_resolution           true
% 2.72/0.99  --res_backward_subs_resolution          true
% 2.72/0.99  --res_orphan_elimination                true
% 2.72/0.99  --res_time_limit                        2.
% 2.72/0.99  --res_out_proof                         true
% 2.72/0.99  
% 2.72/0.99  ------ Superposition Options
% 2.72/0.99  
% 2.72/0.99  --superposition_flag                    true
% 2.72/0.99  --sup_passive_queue_type                priority_queues
% 2.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.99  --demod_completeness_check              fast
% 2.72/0.99  --demod_use_ground                      true
% 2.72/0.99  --sup_to_prop_solver                    passive
% 2.72/0.99  --sup_prop_simpl_new                    true
% 2.72/0.99  --sup_prop_simpl_given                  true
% 2.72/0.99  --sup_fun_splitting                     false
% 2.72/0.99  --sup_smt_interval                      50000
% 2.72/0.99  
% 2.72/0.99  ------ Superposition Simplification Setup
% 2.72/0.99  
% 2.72/0.99  --sup_indices_passive                   []
% 2.72/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_full_bw                           [BwDemod]
% 2.72/0.99  --sup_immed_triv                        [TrivRules]
% 2.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_immed_bw_main                     []
% 2.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.99  
% 2.72/0.99  ------ Combination Options
% 2.72/0.99  
% 2.72/0.99  --comb_res_mult                         3
% 2.72/0.99  --comb_sup_mult                         2
% 2.72/0.99  --comb_inst_mult                        10
% 2.72/0.99  
% 2.72/0.99  ------ Debug Options
% 2.72/0.99  
% 2.72/0.99  --dbg_backtrace                         false
% 2.72/0.99  --dbg_dump_prop_clauses                 false
% 2.72/0.99  --dbg_dump_prop_clauses_file            -
% 2.72/0.99  --dbg_out_stat                          false
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  ------ Proving...
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  % SZS status Theorem for theBenchmark.p
% 2.72/0.99  
% 2.72/0.99   Resolution empty clause
% 2.72/0.99  
% 2.72/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.72/0.99  
% 2.72/0.99  fof(f1,axiom,(
% 2.72/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f15,plain,(
% 2.72/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.72/0.99    inference(ennf_transformation,[],[f1])).
% 2.72/0.99  
% 2.72/0.99  fof(f30,plain,(
% 2.72/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.72/0.99    inference(nnf_transformation,[],[f15])).
% 2.72/0.99  
% 2.72/0.99  fof(f31,plain,(
% 2.72/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.72/0.99    inference(rectify,[],[f30])).
% 2.72/0.99  
% 2.72/0.99  fof(f32,plain,(
% 2.72/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.72/0.99    introduced(choice_axiom,[])).
% 2.72/0.99  
% 2.72/0.99  fof(f33,plain,(
% 2.72/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.72/0.99  
% 2.72/0.99  fof(f43,plain,(
% 2.72/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f33])).
% 2.72/0.99  
% 2.72/0.99  fof(f13,conjecture,(
% 2.72/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f14,negated_conjecture,(
% 2.72/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 2.72/0.99    inference(negated_conjecture,[],[f13])).
% 2.72/0.99  
% 2.72/0.99  fof(f28,plain,(
% 2.72/0.99    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.72/0.99    inference(ennf_transformation,[],[f14])).
% 2.72/0.99  
% 2.72/0.99  fof(f29,plain,(
% 2.72/0.99    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.72/0.99    inference(flattening,[],[f28])).
% 2.72/0.99  
% 2.72/0.99  fof(f40,plain,(
% 2.72/0.99    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 2.72/0.99    introduced(choice_axiom,[])).
% 2.72/0.99  
% 2.72/0.99  fof(f41,plain,(
% 2.72/0.99    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 2.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f40])).
% 2.72/0.99  
% 2.72/0.99  fof(f69,plain,(
% 2.72/0.99    r1_tarski(sK1,sK3)),
% 2.72/0.99    inference(cnf_transformation,[],[f41])).
% 2.72/0.99  
% 2.72/0.99  fof(f67,plain,(
% 2.72/0.99    v1_funct_2(sK4,sK1,sK2)),
% 2.72/0.99    inference(cnf_transformation,[],[f41])).
% 2.72/0.99  
% 2.72/0.99  fof(f11,axiom,(
% 2.72/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f24,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.99    inference(ennf_transformation,[],[f11])).
% 2.72/0.99  
% 2.72/0.99  fof(f25,plain,(
% 2.72/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.99    inference(flattening,[],[f24])).
% 2.72/0.99  
% 2.72/0.99  fof(f39,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.99    inference(nnf_transformation,[],[f25])).
% 2.72/0.99  
% 2.72/0.99  fof(f59,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.99    inference(cnf_transformation,[],[f39])).
% 2.72/0.99  
% 2.72/0.99  fof(f68,plain,(
% 2.72/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.72/0.99    inference(cnf_transformation,[],[f41])).
% 2.72/0.99  
% 2.72/0.99  fof(f9,axiom,(
% 2.72/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f21,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.99    inference(ennf_transformation,[],[f9])).
% 2.72/0.99  
% 2.72/0.99  fof(f56,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.99    inference(cnf_transformation,[],[f21])).
% 2.72/0.99  
% 2.72/0.99  fof(f7,axiom,(
% 2.72/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f18,plain,(
% 2.72/0.99    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.72/0.99    inference(ennf_transformation,[],[f7])).
% 2.72/0.99  
% 2.72/0.99  fof(f19,plain,(
% 2.72/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.72/0.99    inference(flattening,[],[f18])).
% 2.72/0.99  
% 2.72/0.99  fof(f54,plain,(
% 2.72/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f19])).
% 2.72/0.99  
% 2.72/0.99  fof(f8,axiom,(
% 2.72/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f20,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.99    inference(ennf_transformation,[],[f8])).
% 2.72/0.99  
% 2.72/0.99  fof(f55,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.99    inference(cnf_transformation,[],[f20])).
% 2.72/0.99  
% 2.72/0.99  fof(f6,axiom,(
% 2.72/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f17,plain,(
% 2.72/0.99    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.72/0.99    inference(ennf_transformation,[],[f6])).
% 2.72/0.99  
% 2.72/0.99  fof(f53,plain,(
% 2.72/0.99    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f17])).
% 2.72/0.99  
% 2.72/0.99  fof(f12,axiom,(
% 2.72/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f26,plain,(
% 2.72/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.72/0.99    inference(ennf_transformation,[],[f12])).
% 2.72/0.99  
% 2.72/0.99  fof(f27,plain,(
% 2.72/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.72/0.99    inference(flattening,[],[f26])).
% 2.72/0.99  
% 2.72/0.99  fof(f65,plain,(
% 2.72/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f27])).
% 2.72/0.99  
% 2.72/0.99  fof(f66,plain,(
% 2.72/0.99    v1_funct_1(sK4)),
% 2.72/0.99    inference(cnf_transformation,[],[f41])).
% 2.72/0.99  
% 2.72/0.99  fof(f10,axiom,(
% 2.72/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f22,plain,(
% 2.72/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.72/0.99    inference(ennf_transformation,[],[f10])).
% 2.72/0.99  
% 2.72/0.99  fof(f23,plain,(
% 2.72/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.99    inference(flattening,[],[f22])).
% 2.72/0.99  
% 2.72/0.99  fof(f38,plain,(
% 2.72/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.99    inference(nnf_transformation,[],[f23])).
% 2.72/0.99  
% 2.72/0.99  fof(f58,plain,(
% 2.72/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.99    inference(cnf_transformation,[],[f38])).
% 2.72/0.99  
% 2.72/0.99  fof(f75,plain,(
% 2.72/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.99    inference(equality_resolution,[],[f58])).
% 2.72/0.99  
% 2.72/0.99  fof(f70,plain,(
% 2.72/0.99    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)),
% 2.72/0.99    inference(cnf_transformation,[],[f41])).
% 2.72/0.99  
% 2.72/0.99  fof(f2,axiom,(
% 2.72/0.99    v1_xboole_0(k1_xboole_0)),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f45,plain,(
% 2.72/0.99    v1_xboole_0(k1_xboole_0)),
% 2.72/0.99    inference(cnf_transformation,[],[f2])).
% 2.72/0.99  
% 2.72/0.99  fof(f5,axiom,(
% 2.72/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f16,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.72/0.99    inference(ennf_transformation,[],[f5])).
% 2.72/0.99  
% 2.72/0.99  fof(f52,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f16])).
% 2.72/0.99  
% 2.72/0.99  fof(f4,axiom,(
% 2.72/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f36,plain,(
% 2.72/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.72/0.99    inference(nnf_transformation,[],[f4])).
% 2.72/0.99  
% 2.72/0.99  fof(f37,plain,(
% 2.72/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.72/0.99    inference(flattening,[],[f36])).
% 2.72/0.99  
% 2.72/0.99  fof(f51,plain,(
% 2.72/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.72/0.99    inference(cnf_transformation,[],[f37])).
% 2.72/0.99  
% 2.72/0.99  fof(f73,plain,(
% 2.72/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.72/0.99    inference(equality_resolution,[],[f51])).
% 2.72/0.99  
% 2.72/0.99  fof(f3,axiom,(
% 2.72/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f34,plain,(
% 2.72/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.72/0.99    inference(nnf_transformation,[],[f3])).
% 2.72/0.99  
% 2.72/0.99  fof(f35,plain,(
% 2.72/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.72/0.99    inference(flattening,[],[f34])).
% 2.72/0.99  
% 2.72/0.99  fof(f48,plain,(
% 2.72/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f35])).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1,plain,
% 2.72/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.72/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_978,plain,
% 2.72/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.72/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_25,negated_conjecture,
% 2.72/0.99      ( r1_tarski(sK1,sK3) ),
% 2.72/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_974,plain,
% 2.72/0.99      ( r1_tarski(sK1,sK3) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_27,negated_conjecture,
% 2.72/0.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 2.72/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_22,plain,
% 2.72/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.72/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.72/0.99      | k1_xboole_0 = X2 ),
% 2.72/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_26,negated_conjecture,
% 2.72/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.72/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_362,plain,
% 2.72/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.72/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.72/0.99      | sK4 != X0
% 2.72/0.99      | k1_xboole_0 = X2 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_363,plain,
% 2.72/0.99      ( ~ v1_funct_2(sK4,X0,X1)
% 2.72/0.99      | k1_relset_1(X0,X1,sK4) = X0
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.72/0.99      | k1_xboole_0 = X1 ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_362]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_597,plain,
% 2.72/0.99      ( k1_relset_1(X0,X1,sK4) = X0
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.72/0.99      | sK4 != sK4
% 2.72/0.99      | sK2 != X1
% 2.72/0.99      | sK1 != X0
% 2.72/0.99      | k1_xboole_0 = X1 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_363]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_598,plain,
% 2.72/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.72/0.99      | k1_xboole_0 = sK2 ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_597]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_660,plain,
% 2.72/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 2.72/0.99      inference(equality_resolution_simp,[status(thm)],[c_598]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_14,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_398,plain,
% 2.72/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.72/0.99      | sK4 != X2 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_399,plain,
% 2.72/0.99      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_398]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1100,plain,
% 2.72/0.99      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 2.72/0.99      inference(equality_resolution,[status(thm)],[c_399]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1203,plain,
% 2.72/0.99      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 2.72/0.99      inference(demodulation,[status(thm)],[c_660,c_1100]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_12,plain,
% 2.72/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.72/0.99      | ~ v1_relat_1(X0)
% 2.72/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.72/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_13,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_407,plain,
% 2.72/0.99      ( v1_relat_1(X0)
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.72/0.99      | sK4 != X0 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_408,plain,
% 2.72/0.99      ( v1_relat_1(sK4)
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_407]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_555,plain,
% 2.72/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.72/0.99      | k7_relat_1(X0,X1) = X0
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.72/0.99      | sK4 != X0 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_408]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_556,plain,
% 2.72/0.99      ( ~ r1_tarski(k1_relat_1(sK4),X0)
% 2.72/0.99      | k7_relat_1(sK4,X0) = sK4
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_555]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_727,plain,
% 2.72/0.99      ( ~ r1_tarski(k1_relat_1(sK4),X0)
% 2.72/0.99      | k7_relat_1(sK4,X0) = sK4
% 2.72/0.99      | ~ sP2_iProver_split ),
% 2.72/0.99      inference(splitting,
% 2.72/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.72/0.99                [c_556]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_971,plain,
% 2.72/0.99      ( k7_relat_1(sK4,X0) = sK4
% 2.72/0.99      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 2.72/0.99      | sP2_iProver_split != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_728,plain,
% 2.72/0.99      ( sP2_iProver_split | sP0_iProver_split ),
% 2.72/0.99      inference(splitting,
% 2.72/0.99                [splitting(split),new_symbols(definition,[])],
% 2.72/0.99                [c_556]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_757,plain,
% 2.72/0.99      ( sP2_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_758,plain,
% 2.72/0.99      ( k7_relat_1(sK4,X0) = sK4
% 2.72/0.99      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 2.72/0.99      | sP2_iProver_split != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_730,plain,( X0 = X0 ),theory(equality) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1123,plain,
% 2.72/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.72/0.99      inference(instantiation,[status(thm)],[c_730]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_11,plain,
% 2.72/0.99      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_570,plain,
% 2.72/0.99      ( r1_tarski(k7_relat_1(X0,X1),X0)
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.72/0.99      | sK4 != X0 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_408]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_571,plain,
% 2.72/0.99      ( r1_tarski(k7_relat_1(sK4,X0),sK4)
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_570]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_724,plain,
% 2.72/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.72/0.99      | ~ sP0_iProver_split ),
% 2.72/0.99      inference(splitting,
% 2.72/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.72/0.99                [c_571]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1125,plain,
% 2.72/0.99      ( ~ sP0_iProver_split
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.72/0.99      inference(instantiation,[status(thm)],[c_724]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1127,plain,
% 2.72/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.72/0.99      | sP0_iProver_split != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1577,plain,
% 2.72/0.99      ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 2.72/0.99      | k7_relat_1(sK4,X0) = sK4 ),
% 2.72/0.99      inference(global_propositional_subsumption,
% 2.72/0.99                [status(thm)],
% 2.72/0.99                [c_971,c_757,c_758,c_1123,c_1127]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1578,plain,
% 2.72/0.99      ( k7_relat_1(sK4,X0) = sK4
% 2.72/0.99      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 2.72/0.99      inference(renaming,[status(thm)],[c_1577]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1586,plain,
% 2.72/0.99      ( k7_relat_1(sK4,X0) = sK4
% 2.72/0.99      | sK2 = k1_xboole_0
% 2.72/0.99      | r1_tarski(sK1,X0) != iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_1203,c_1578]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1952,plain,
% 2.72/0.99      ( k7_relat_1(sK4,sK3) = sK4 | sK2 = k1_xboole_0 ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_974,c_1586]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_23,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.99      | ~ v1_funct_1(X0)
% 2.72/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.72/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_28,negated_conjecture,
% 2.72/0.99      ( v1_funct_1(sK4) ),
% 2.72/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_302,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 2.72/0.99      | sK4 != X0 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_303,plain,
% 2.72/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.72/0.99      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_302]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_496,plain,
% 2.72/0.99      ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 2.72/0.99      | sK4 != sK4 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_303]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_664,plain,
% 2.72/0.99      ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.72/0.99      inference(equality_resolution_simp,[status(thm)],[c_496]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1143,plain,
% 2.72/0.99      ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
% 2.72/0.99      inference(equality_resolution,[status(thm)],[c_664]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_15,plain,
% 2.72/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.72/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.72/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_24,negated_conjecture,
% 2.72/0.99      ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
% 2.72/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_349,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.99      | k2_partfun1(sK1,sK2,sK4,sK3) != X0
% 2.72/0.99      | sK4 != X0
% 2.72/0.99      | sK2 != X2
% 2.72/0.99      | sK1 != X1 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_350,plain,
% 2.72/0.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.72/0.99      | sK4 != k2_partfun1(sK1,sK2,sK4,sK3) ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_349]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_507,plain,
% 2.72/0.99      ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_350]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_663,plain,
% 2.72/0.99      ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4 ),
% 2.72/0.99      inference(equality_resolution_simp,[status(thm)],[c_507]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1433,plain,
% 2.72/0.99      ( k7_relat_1(sK4,sK3) != sK4 ),
% 2.72/0.99      inference(demodulation,[status(thm)],[c_1143,c_663]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2032,plain,
% 2.72/0.99      ( sK2 = k1_xboole_0 ),
% 2.72/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1952,c_1433]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_3,plain,
% 2.72/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_10,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.72/0.99      | ~ r2_hidden(X2,X0)
% 2.72/0.99      | ~ v1_xboole_0(X1) ),
% 2.72/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_287,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.72/0.99      | ~ r2_hidden(X2,X0)
% 2.72/0.99      | k1_xboole_0 != X1 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_10]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_288,plain,
% 2.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~ r2_hidden(X1,X0) ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_287]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_484,plain,
% 2.72/0.99      ( ~ r2_hidden(X0,X1)
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k1_xboole_0)
% 2.72/0.99      | sK4 != X1 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_288]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_485,plain,
% 2.72/0.99      ( ~ r2_hidden(X0,sK4)
% 2.72/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_484]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_973,plain,
% 2.72/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k1_xboole_0)
% 2.72/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2044,plain,
% 2.72/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 2.72/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.72/0.99      inference(demodulation,[status(thm)],[c_2032,c_973]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_7,plain,
% 2.72/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.72/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2056,plain,
% 2.72/0.99      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 2.72/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 2.72/0.99      inference(demodulation,[status(thm)],[c_2044,c_7]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2057,plain,
% 2.72/0.99      ( r2_hidden(X0,sK4) != iProver_top ),
% 2.72/0.99      inference(equality_resolution_simp,[status(thm)],[c_2056]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2232,plain,
% 2.72/0.99      ( r1_tarski(sK4,X0) = iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_978,c_2057]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_725,plain,
% 2.72/0.99      ( r1_tarski(k7_relat_1(sK4,X0),sK4) | ~ sP1_iProver_split ),
% 2.72/0.99      inference(splitting,
% 2.72/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.72/0.99                [c_571]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_968,plain,
% 2.72/0.99      ( r1_tarski(k7_relat_1(sK4,X0),sK4) = iProver_top
% 2.72/0.99      | sP1_iProver_split != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_726,plain,
% 2.72/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 2.72/0.99      inference(splitting,
% 2.72/0.99                [splitting(split),new_symbols(definition,[])],
% 2.72/0.99                [c_571]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_750,plain,
% 2.72/0.99      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_751,plain,
% 2.72/0.99      ( r1_tarski(k7_relat_1(sK4,X0),sK4) = iProver_top
% 2.72/0.99      | sP1_iProver_split != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1471,plain,
% 2.72/0.99      ( r1_tarski(k7_relat_1(sK4,X0),sK4) = iProver_top ),
% 2.72/0.99      inference(global_propositional_subsumption,
% 2.72/0.99                [status(thm)],
% 2.72/0.99                [c_968,c_750,c_751,c_1123,c_1127]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_4,plain,
% 2.72/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.72/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_976,plain,
% 2.72/0.99      ( X0 = X1
% 2.72/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.72/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1674,plain,
% 2.72/0.99      ( k7_relat_1(sK4,X0) = sK4
% 2.72/0.99      | r1_tarski(sK4,k7_relat_1(sK4,X0)) != iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_1471,c_976]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2239,plain,
% 2.72/0.99      ( k7_relat_1(sK4,X0) = sK4 ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_2232,c_1674]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2329,plain,
% 2.72/0.99      ( sK4 != sK4 ),
% 2.72/0.99      inference(demodulation,[status(thm)],[c_2239,c_1433]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2330,plain,
% 2.72/0.99      ( $false ),
% 2.72/0.99      inference(equality_resolution_simp,[status(thm)],[c_2329]) ).
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.72/0.99  
% 2.72/0.99  ------                               Statistics
% 2.72/0.99  
% 2.72/0.99  ------ General
% 2.72/0.99  
% 2.72/0.99  abstr_ref_over_cycles:                  0
% 2.72/0.99  abstr_ref_under_cycles:                 0
% 2.72/0.99  gc_basic_clause_elim:                   0
% 2.72/0.99  forced_gc_time:                         0
% 2.72/0.99  parsing_time:                           0.02
% 2.72/0.99  unif_index_cands_time:                  0.
% 2.72/0.99  unif_index_add_time:                    0.
% 2.72/0.99  orderings_time:                         0.
% 2.72/0.99  out_proof_time:                         0.013
% 2.72/0.99  total_time:                             0.127
% 2.72/0.99  num_of_symbols:                         54
% 2.72/0.99  num_of_terms:                           2014
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing
% 2.72/0.99  
% 2.72/0.99  num_of_splits:                          4
% 2.72/0.99  num_of_split_atoms:                     3
% 2.72/0.99  num_of_reused_defs:                     1
% 2.72/0.99  num_eq_ax_congr_red:                    15
% 2.72/0.99  num_of_sem_filtered_clauses:            1
% 2.72/0.99  num_of_subtypes:                        0
% 2.72/0.99  monotx_restored_types:                  0
% 2.72/0.99  sat_num_of_epr_types:                   0
% 2.72/0.99  sat_num_of_non_cyclic_types:            0
% 2.72/0.99  sat_guarded_non_collapsed_types:        0
% 2.72/0.99  num_pure_diseq_elim:                    0
% 2.72/0.99  simp_replaced_by:                       0
% 2.72/0.99  res_preprocessed:                       109
% 2.72/0.99  prep_upred:                             0
% 2.72/0.99  prep_unflattend:                        36
% 2.72/0.99  smt_new_axioms:                         0
% 2.72/0.99  pred_elim_cands:                        2
% 2.72/0.99  pred_elim:                              6
% 2.72/0.99  pred_elim_cl:                           10
% 2.72/0.99  pred_elim_cycles:                       9
% 2.72/0.99  merged_defs:                            0
% 2.72/0.99  merged_defs_ncl:                        0
% 2.72/0.99  bin_hyper_res:                          0
% 2.72/0.99  prep_cycles:                            4
% 2.72/0.99  pred_elim_time:                         0.009
% 2.72/0.99  splitting_time:                         0.
% 2.72/0.99  sem_filter_time:                        0.
% 2.72/0.99  monotx_time:                            0.
% 2.72/0.99  subtype_inf_time:                       0.
% 2.72/0.99  
% 2.72/0.99  ------ Problem properties
% 2.72/0.99  
% 2.72/0.99  clauses:                                22
% 2.72/0.99  conjectures:                            1
% 2.72/0.99  epr:                                    6
% 2.72/0.99  horn:                                   16
% 2.72/0.99  ground:                                 7
% 2.72/0.99  unary:                                  5
% 2.72/0.99  binary:                                 11
% 2.72/0.99  lits:                                   46
% 2.72/0.99  lits_eq:                                24
% 2.72/0.99  fd_pure:                                0
% 2.72/0.99  fd_pseudo:                              0
% 2.72/0.99  fd_cond:                                1
% 2.72/0.99  fd_pseudo_cond:                         1
% 2.72/0.99  ac_symbols:                             0
% 2.72/0.99  
% 2.72/0.99  ------ Propositional Solver
% 2.72/0.99  
% 2.72/0.99  prop_solver_calls:                      27
% 2.72/0.99  prop_fast_solver_calls:                 647
% 2.72/0.99  smt_solver_calls:                       0
% 2.72/0.99  smt_fast_solver_calls:                  0
% 2.72/0.99  prop_num_of_clauses:                    788
% 2.72/0.99  prop_preprocess_simplified:             3323
% 2.72/0.99  prop_fo_subsumed:                       6
% 2.72/0.99  prop_solver_time:                       0.
% 2.72/0.99  smt_solver_time:                        0.
% 2.72/0.99  smt_fast_solver_time:                   0.
% 2.72/0.99  prop_fast_solver_time:                  0.
% 2.72/0.99  prop_unsat_core_time:                   0.
% 2.72/0.99  
% 2.72/0.99  ------ QBF
% 2.72/0.99  
% 2.72/0.99  qbf_q_res:                              0
% 2.72/0.99  qbf_num_tautologies:                    0
% 2.72/0.99  qbf_prep_cycles:                        0
% 2.72/0.99  
% 2.72/0.99  ------ BMC1
% 2.72/0.99  
% 2.72/0.99  bmc1_current_bound:                     -1
% 2.72/0.99  bmc1_last_solved_bound:                 -1
% 2.72/0.99  bmc1_unsat_core_size:                   -1
% 2.72/0.99  bmc1_unsat_core_parents_size:           -1
% 2.72/0.99  bmc1_merge_next_fun:                    0
% 2.72/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.72/0.99  
% 2.72/0.99  ------ Instantiation
% 2.72/0.99  
% 2.72/0.99  inst_num_of_clauses:                    254
% 2.72/0.99  inst_num_in_passive:                    92
% 2.72/0.99  inst_num_in_active:                     129
% 2.72/0.99  inst_num_in_unprocessed:                33
% 2.72/0.99  inst_num_of_loops:                      200
% 2.72/0.99  inst_num_of_learning_restarts:          0
% 2.72/0.99  inst_num_moves_active_passive:          68
% 2.72/0.99  inst_lit_activity:                      0
% 2.72/0.99  inst_lit_activity_moves:                0
% 2.72/0.99  inst_num_tautologies:                   0
% 2.72/0.99  inst_num_prop_implied:                  0
% 2.72/0.99  inst_num_existing_simplified:           0
% 2.72/0.99  inst_num_eq_res_simplified:             0
% 2.72/0.99  inst_num_child_elim:                    0
% 2.72/0.99  inst_num_of_dismatching_blockings:      27
% 2.72/0.99  inst_num_of_non_proper_insts:           196
% 2.72/0.99  inst_num_of_duplicates:                 0
% 2.72/0.99  inst_inst_num_from_inst_to_res:         0
% 2.72/0.99  inst_dismatching_checking_time:         0.
% 2.72/0.99  
% 2.72/0.99  ------ Resolution
% 2.72/0.99  
% 2.72/0.99  res_num_of_clauses:                     0
% 2.72/0.99  res_num_in_passive:                     0
% 2.72/0.99  res_num_in_active:                      0
% 2.72/0.99  res_num_of_loops:                       113
% 2.72/0.99  res_forward_subset_subsumed:            35
% 2.72/0.99  res_backward_subset_subsumed:           0
% 2.72/0.99  res_forward_subsumed:                   0
% 2.72/0.99  res_backward_subsumed:                  0
% 2.72/0.99  res_forward_subsumption_resolution:     0
% 2.72/0.99  res_backward_subsumption_resolution:    0
% 2.72/0.99  res_clause_to_clause_subsumption:       104
% 2.72/0.99  res_orphan_elimination:                 0
% 2.72/0.99  res_tautology_del:                      23
% 2.72/0.99  res_num_eq_res_simplified:              3
% 2.72/0.99  res_num_sel_changes:                    0
% 2.72/0.99  res_moves_from_active_to_pass:          0
% 2.72/0.99  
% 2.72/0.99  ------ Superposition
% 2.72/0.99  
% 2.72/0.99  sup_time_total:                         0.
% 2.72/0.99  sup_time_generating:                    0.
% 2.72/0.99  sup_time_sim_full:                      0.
% 2.72/0.99  sup_time_sim_immed:                     0.
% 2.72/0.99  
% 2.72/0.99  sup_num_of_clauses:                     30
% 2.72/0.99  sup_num_in_active:                      20
% 2.72/0.99  sup_num_in_passive:                     10
% 2.72/0.99  sup_num_of_loops:                       38
% 2.72/0.99  sup_fw_superposition:                   18
% 2.72/0.99  sup_bw_superposition:                   9
% 2.72/0.99  sup_immediate_simplified:               16
% 2.72/0.99  sup_given_eliminated:                   0
% 2.72/0.99  comparisons_done:                       0
% 2.72/0.99  comparisons_avoided:                    9
% 2.72/0.99  
% 2.72/0.99  ------ Simplifications
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  sim_fw_subset_subsumed:                 2
% 2.72/0.99  sim_bw_subset_subsumed:                 2
% 2.72/0.99  sim_fw_subsumed:                        2
% 2.72/0.99  sim_bw_subsumed:                        2
% 2.72/0.99  sim_fw_subsumption_res:                 0
% 2.72/0.99  sim_bw_subsumption_res:                 0
% 2.72/0.99  sim_tautology_del:                      0
% 2.72/0.99  sim_eq_tautology_del:                   3
% 2.72/0.99  sim_eq_res_simp:                        8
% 2.72/0.99  sim_fw_demodulated:                     12
% 2.72/0.99  sim_bw_demodulated:                     17
% 2.72/0.99  sim_light_normalised:                   0
% 2.72/0.99  sim_joinable_taut:                      0
% 2.72/0.99  sim_joinable_simp:                      0
% 2.72/0.99  sim_ac_normalised:                      0
% 2.72/0.99  sim_smt_subsumption:                    0
% 2.72/0.99  
%------------------------------------------------------------------------------

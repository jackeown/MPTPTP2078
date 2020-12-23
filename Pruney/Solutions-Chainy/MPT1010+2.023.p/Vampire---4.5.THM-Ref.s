%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:53 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 203 expanded)
%              Number of leaves         :   17 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  279 ( 677 expanded)
%              Number of equality atoms :   96 ( 254 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(subsumption_resolution,[],[f245,f113])).

fof(f113,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f61,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f245,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f99,f170])).

fof(f170,plain,(
    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f169,f99])).

fof(f169,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
      | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ) ),
    inference(subsumption_resolution,[],[f166,f50])).

fof(f50,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f166,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
      | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
      | sK1 = k1_funct_1(sK3,sK2) ) ),
    inference(resolution,[],[f163,f49])).

fof(f49,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,k2_enumset1(sK1,sK1,sK1,sK1))
      | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
      | sK1 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f158,f100])).

fof(f100,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f57,f83])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f158,plain,(
    ! [X4,X3] :
      ( r2_hidden(k1_funct_1(sK3,X3),k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(X4,k2_enumset1(sK1,sK1,sK1,sK1))
      | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ) ),
    inference(superposition,[],[f128,f155])).

fof(f155,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f153,f84])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f48,f83])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f153,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f152,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f152,plain,
    ( sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f151,f85])).

fof(f85,plain,(
    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f47,f83])).

fof(f47,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f151,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) ),
    inference(resolution,[],[f67,f84])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | r2_hidden(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X1,k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    inference(resolution,[],[f127,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f56,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f127,plain,(
    ! [X0] :
      ( m1_subset_1(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f126,f84])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | m1_subset_1(k1_funct_1(sK3,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f125,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK3,X0)
      | ~ r2_hidden(X1,k1_relat_1(sK3))
      | m1_subset_1(k1_funct_1(sK3,X1),X0) ) ),
    inference(resolution,[],[f124,f84])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v5_relat_1(sK3,X1)
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | m1_subset_1(k1_funct_1(sK3,X0),X1) ) ),
    inference(resolution,[],[f123,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK3)
      | m1_subset_1(k1_funct_1(sK3,X0),X1)
      | ~ v5_relat_1(sK3,X1)
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

fof(f99,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f83])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:35:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (15014)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (15033)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.51  % (15027)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (15019)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (15029)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (15024)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (15009)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (15025)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (15019)Refutation not found, incomplete strategy% (15019)------------------------------
% 0.21/0.52  % (15019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15019)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15019)Memory used [KB]: 1791
% 0.21/0.52  % (15019)Time elapsed: 0.058 s
% 0.21/0.52  % (15019)------------------------------
% 0.21/0.52  % (15019)------------------------------
% 0.21/0.52  % (15018)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (15011)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.53  % (15032)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.29/0.53  % (15021)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.29/0.53  % (15013)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.29/0.53  % (15027)Refutation found. Thanks to Tanya!
% 1.29/0.53  % SZS status Theorem for theBenchmark
% 1.29/0.53  % SZS output start Proof for theBenchmark
% 1.29/0.53  fof(f251,plain,(
% 1.29/0.53    $false),
% 1.29/0.53    inference(subsumption_resolution,[],[f245,f113])).
% 1.29/0.53  fof(f113,plain,(
% 1.29/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.29/0.53    inference(resolution,[],[f61,f51])).
% 1.29/0.53  fof(f51,plain,(
% 1.29/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f2])).
% 1.29/0.53  fof(f2,axiom,(
% 1.29/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.29/0.53  fof(f61,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f21])).
% 1.29/0.53  fof(f21,plain,(
% 1.29/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.29/0.53    inference(ennf_transformation,[],[f10])).
% 1.29/0.53  fof(f10,axiom,(
% 1.29/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.29/0.53  fof(f245,plain,(
% 1.29/0.53    r2_hidden(sK1,k1_xboole_0)),
% 1.29/0.53    inference(superposition,[],[f99,f170])).
% 1.29/0.53  fof(f170,plain,(
% 1.29/0.53    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.29/0.53    inference(resolution,[],[f169,f99])).
% 1.29/0.53  fof(f169,plain,(
% 1.29/0.53    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f166,f50])).
% 1.29/0.53  fof(f50,plain,(
% 1.29/0.53    sK1 != k1_funct_1(sK3,sK2)),
% 1.29/0.53    inference(cnf_transformation,[],[f31])).
% 1.29/0.53  fof(f31,plain,(
% 1.29/0.53    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f30])).
% 1.29/0.53  fof(f30,plain,(
% 1.29/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f18,plain,(
% 1.29/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.29/0.53    inference(flattening,[],[f17])).
% 1.29/0.53  fof(f17,plain,(
% 1.29/0.53    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.29/0.53    inference(ennf_transformation,[],[f16])).
% 1.29/0.53  fof(f16,negated_conjecture,(
% 1.29/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.29/0.53    inference(negated_conjecture,[],[f15])).
% 1.29/0.53  fof(f15,conjecture,(
% 1.29/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.29/0.53  fof(f166,plain,(
% 1.29/0.53    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK1 = k1_funct_1(sK3,sK2)) )),
% 1.29/0.53    inference(resolution,[],[f163,f49])).
% 1.29/0.53  fof(f49,plain,(
% 1.29/0.53    r2_hidden(sK2,sK0)),
% 1.29/0.53    inference(cnf_transformation,[],[f31])).
% 1.29/0.53  fof(f163,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK1 = k1_funct_1(sK3,X0)) )),
% 1.29/0.53    inference(resolution,[],[f158,f100])).
% 1.29/0.53  fof(f100,plain,(
% 1.29/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.29/0.53    inference(equality_resolution,[],[f89])).
% 1.29/0.53  fof(f89,plain,(
% 1.29/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.29/0.53    inference(definition_unfolding,[],[f57,f83])).
% 1.29/0.53  fof(f83,plain,(
% 1.29/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.29/0.53    inference(definition_unfolding,[],[f52,f82])).
% 1.29/0.53  fof(f82,plain,(
% 1.29/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.29/0.53    inference(definition_unfolding,[],[f55,f62])).
% 1.29/0.53  fof(f62,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f7])).
% 1.29/0.53  fof(f7,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.29/0.53  fof(f55,plain,(
% 1.29/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f6])).
% 1.29/0.53  fof(f6,axiom,(
% 1.29/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.29/0.53  fof(f52,plain,(
% 1.29/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f5])).
% 1.29/0.53  fof(f5,axiom,(
% 1.29/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.29/0.53  fof(f57,plain,(
% 1.29/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.29/0.53    inference(cnf_transformation,[],[f39])).
% 1.29/0.53  fof(f39,plain,(
% 1.29/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 1.29/0.53  fof(f38,plain,(
% 1.29/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f37,plain,(
% 1.29/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.29/0.53    inference(rectify,[],[f36])).
% 1.29/0.53  fof(f36,plain,(
% 1.29/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.29/0.53    inference(nnf_transformation,[],[f4])).
% 1.29/0.53  fof(f4,axiom,(
% 1.29/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.29/0.53  fof(f158,plain,(
% 1.29/0.53    ( ! [X4,X3] : (r2_hidden(k1_funct_1(sK3,X3),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X3,sK0) | ~r2_hidden(X4,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)) )),
% 1.29/0.53    inference(superposition,[],[f128,f155])).
% 1.29/0.53  fof(f155,plain,(
% 1.29/0.53    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.29/0.53    inference(subsumption_resolution,[],[f153,f84])).
% 1.29/0.53  fof(f84,plain,(
% 1.29/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.29/0.53    inference(definition_unfolding,[],[f48,f83])).
% 1.29/0.53  fof(f48,plain,(
% 1.29/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.29/0.53    inference(cnf_transformation,[],[f31])).
% 1.29/0.53  fof(f153,plain,(
% 1.29/0.53    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.29/0.53    inference(superposition,[],[f152,f64])).
% 1.29/0.53  fof(f64,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f23])).
% 1.29/0.53  fof(f23,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.53    inference(ennf_transformation,[],[f13])).
% 1.29/0.53  fof(f13,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.29/0.53  fof(f152,plain,(
% 1.29/0.53    sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.29/0.53    inference(subsumption_resolution,[],[f151,f85])).
% 1.29/0.53  fof(f85,plain,(
% 1.29/0.53    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.29/0.53    inference(definition_unfolding,[],[f47,f83])).
% 1.29/0.53  fof(f47,plain,(
% 1.29/0.53    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.29/0.53    inference(cnf_transformation,[],[f31])).
% 1.29/0.53  fof(f151,plain,(
% 1.29/0.53    ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)),
% 1.29/0.53    inference(resolution,[],[f67,f84])).
% 1.29/0.53  fof(f67,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.29/0.53    inference(cnf_transformation,[],[f40])).
% 1.29/0.53  fof(f40,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.53    inference(nnf_transformation,[],[f26])).
% 1.29/0.53  fof(f26,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.53    inference(flattening,[],[f25])).
% 1.29/0.53  fof(f25,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.53    inference(ennf_transformation,[],[f14])).
% 1.29/0.53  fof(f14,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.29/0.53  fof(f128,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X1,k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 1.29/0.53    inference(resolution,[],[f127,f116])).
% 1.29/0.53  fof(f116,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | r2_hidden(X0,X1) | ~r2_hidden(X2,X1)) )),
% 1.29/0.53    inference(resolution,[],[f56,f53])).
% 1.29/0.53  fof(f53,plain,(
% 1.29/0.53    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f35])).
% 1.29/0.53  fof(f35,plain,(
% 1.29/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 1.29/0.53  fof(f34,plain,(
% 1.29/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f33,plain,(
% 1.29/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.29/0.53    inference(rectify,[],[f32])).
% 1.29/0.53  fof(f32,plain,(
% 1.29/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.29/0.53    inference(nnf_transformation,[],[f1])).
% 1.29/0.53  fof(f1,axiom,(
% 1.29/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.29/0.53  fof(f56,plain,(
% 1.29/0.53    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f20])).
% 1.29/0.53  fof(f20,plain,(
% 1.29/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.29/0.53    inference(flattening,[],[f19])).
% 1.29/0.53  fof(f19,plain,(
% 1.29/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.29/0.53    inference(ennf_transformation,[],[f8])).
% 1.29/0.53  fof(f8,axiom,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.29/0.53  fof(f127,plain,(
% 1.29/0.53    ( ! [X0] : (m1_subset_1(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 1.29/0.53    inference(resolution,[],[f126,f84])).
% 1.29/0.53  fof(f126,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 1.29/0.53    inference(resolution,[],[f125,f66])).
% 1.29/0.53  fof(f66,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f24])).
% 1.29/0.53  fof(f24,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.53    inference(ennf_transformation,[],[f12])).
% 1.29/0.53  fof(f12,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.29/0.53  fof(f125,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~v5_relat_1(sK3,X0) | ~r2_hidden(X1,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X1),X0)) )),
% 1.29/0.53    inference(resolution,[],[f124,f84])).
% 1.29/0.53  fof(f124,plain,(
% 1.29/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v5_relat_1(sK3,X1) | ~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),X1)) )),
% 1.29/0.53    inference(resolution,[],[f123,f63])).
% 1.29/0.53  fof(f63,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f22])).
% 1.29/0.53  fof(f22,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.53    inference(ennf_transformation,[],[f11])).
% 1.29/0.53  fof(f11,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.29/0.53  fof(f123,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~v1_relat_1(sK3) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~v5_relat_1(sK3,X1) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 1.29/0.53    inference(resolution,[],[f73,f46])).
% 1.29/0.53  fof(f46,plain,(
% 1.29/0.53    v1_funct_1(sK3)),
% 1.29/0.53    inference(cnf_transformation,[],[f31])).
% 1.29/0.53  fof(f73,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | m1_subset_1(k1_funct_1(X2,X1),X0) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f28])).
% 1.29/0.53  fof(f28,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 1.29/0.53    inference(flattening,[],[f27])).
% 1.29/0.53  fof(f27,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 1.29/0.53    inference(ennf_transformation,[],[f9])).
% 1.29/0.53  fof(f9,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).
% 1.29/0.53  fof(f99,plain,(
% 1.29/0.53    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.29/0.53    inference(equality_resolution,[],[f98])).
% 1.29/0.53  fof(f98,plain,(
% 1.29/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.29/0.53    inference(equality_resolution,[],[f88])).
% 1.29/0.53  fof(f88,plain,(
% 1.29/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.29/0.53    inference(definition_unfolding,[],[f58,f83])).
% 1.29/0.53  fof(f58,plain,(
% 1.29/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.29/0.53    inference(cnf_transformation,[],[f39])).
% 1.29/0.53  % SZS output end Proof for theBenchmark
% 1.29/0.53  % (15027)------------------------------
% 1.29/0.53  % (15027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (15027)Termination reason: Refutation
% 1.29/0.53  
% 1.29/0.53  % (15027)Memory used [KB]: 6396
% 1.29/0.53  % (15027)Time elapsed: 0.064 s
% 1.29/0.53  % (15027)------------------------------
% 1.29/0.53  % (15027)------------------------------
% 1.29/0.53  % (15017)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.29/0.53  % (15006)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.29/0.53  % (15028)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.29/0.54  % (15004)Success in time 0.175 s
%------------------------------------------------------------------------------

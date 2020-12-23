%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:28 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 359 expanded)
%              Number of leaves         :   25 (  94 expanded)
%              Depth                    :   21
%              Number of atoms          :  366 (1293 expanded)
%              Number of equality atoms :   74 ( 305 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(subsumption_resolution,[],[f243,f186])).

fof(f186,plain,(
    ~ r1_xboole_0(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f179,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f179,plain,(
    ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f56,f175])).

fof(f175,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f166,f170])).

fof(f170,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f169,f81])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f28,f52])).

% (23238)Refutation not found, incomplete strategy% (23238)------------------------------
% (23238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23238)Termination reason: Refutation not found, incomplete strategy

% (23238)Memory used [KB]: 10746
% (23238)Time elapsed: 0.146 s
% (23238)------------------------------
% (23238)------------------------------
% (23237)Refutation not found, incomplete strategy% (23237)------------------------------
% (23237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23237)Termination reason: Refutation not found, incomplete strategy

% (23237)Memory used [KB]: 10618
% (23237)Time elapsed: 0.144 s
% (23237)------------------------------
% (23237)------------------------------
% (23236)Refutation not found, incomplete strategy% (23236)------------------------------
% (23236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23236)Termination reason: Refutation not found, incomplete strategy

% (23236)Memory used [KB]: 10746
% (23236)Time elapsed: 0.145 s
% (23236)------------------------------
% (23236)------------------------------
% (23228)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (23244)Refutation not found, incomplete strategy% (23244)------------------------------
% (23244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23244)Termination reason: Refutation not found, incomplete strategy

% (23244)Memory used [KB]: 10618
% (23244)Time elapsed: 0.142 s
% (23244)------------------------------
% (23244)------------------------------
% (23256)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f169,plain,(
    ! [X3] : ~ r2_hidden(X3,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(resolution,[],[f167,f148])).

fof(f148,plain,(
    ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    inference(resolution,[],[f89,f126])).

fof(f126,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f59,f123])).

fof(f123,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f119,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f58,f60])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f119,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f118,f90])).

fof(f90,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f107,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f107,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK2(X2,X3),X4)
      | ~ r1_xboole_0(X2,X4)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f63,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f57,f88])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f82,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f83,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f84,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f83,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f82,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f167,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,sK1),X1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f68,f54])).

fof(f54,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK3(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
            & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
        & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f166,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f164,f55])).

fof(f55,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f164,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(superposition,[],[f56,f146])).

fof(f146,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(superposition,[],[f145,f105])).

fof(f105,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(resolution,[],[f55,f58])).

fof(f145,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)) ),
    inference(resolution,[],[f74,f54])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f56,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f243,plain,(
    r1_xboole_0(sK0,k2_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,
    ( r1_xboole_0(sK0,k2_relat_1(sK1))
    | r1_xboole_0(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f234,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f234,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(sK0,X1),k2_relat_1(sK1))
      | r1_xboole_0(sK0,X1) ) ),
    inference(resolution,[],[f232,f61])).

fof(f232,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f230,f148])).

fof(f230,plain,(
    ! [X2] :
      ( r2_hidden(sK6(sK1,X2),k1_xboole_0)
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f227,f175])).

fof(f227,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK6(sK1,X3),k10_relat_1(sK1,X4))
      | ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X3,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f225,f92])).

fof(f92,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f41,f44,f43,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X0),sK1)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X2,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f93,f54])).

fof(f93,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(X6,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK7(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK8(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0) )
                | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK9(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK9(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f47,f50,f49,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK7(X0,X1,X2),X5),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK7(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK9(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK9(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:35:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (23235)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (23227)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.17/0.52  % (23233)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.17/0.52  % (23248)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.17/0.52  % (23230)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.17/0.52  % (23250)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.17/0.52  % (23246)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.17/0.52  % (23243)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.17/0.52  % (23242)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.17/0.53  % (23238)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.17/0.53  % (23241)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.17/0.53  % (23231)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.53  % (23240)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.30/0.53  % (23232)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.53  % (23237)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.53  % (23229)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.53  % (23234)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.30/0.53  % (23232)Refutation found. Thanks to Tanya!
% 1.30/0.53  % SZS status Theorem for theBenchmark
% 1.30/0.53  % (23247)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.53  % (23251)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.54  % (23254)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.30/0.54  % (23252)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.54  % (23249)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.54  % (23255)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.30/0.54  % (23249)Refutation not found, incomplete strategy% (23249)------------------------------
% 1.30/0.54  % (23249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (23249)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (23249)Memory used [KB]: 10746
% 1.30/0.54  % (23249)Time elapsed: 0.131 s
% 1.30/0.54  % (23249)------------------------------
% 1.30/0.54  % (23249)------------------------------
% 1.30/0.54  % (23236)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.30/0.55  % (23244)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.55  % SZS output start Proof for theBenchmark
% 1.30/0.55  fof(f244,plain,(
% 1.30/0.55    $false),
% 1.30/0.55    inference(subsumption_resolution,[],[f243,f186])).
% 1.30/0.55  fof(f186,plain,(
% 1.30/0.55    ~r1_xboole_0(sK0,k2_relat_1(sK1))),
% 1.30/0.55    inference(resolution,[],[f179,f60])).
% 1.30/0.55  fof(f60,plain,(
% 1.30/0.55    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f22])).
% 1.30/0.55  fof(f22,plain,(
% 1.30/0.55    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.30/0.55    inference(ennf_transformation,[],[f2])).
% 1.30/0.55  fof(f2,axiom,(
% 1.30/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.30/0.55  fof(f179,plain,(
% 1.30/0.55    ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.30/0.55    inference(subsumption_resolution,[],[f56,f175])).
% 1.30/0.55  fof(f175,plain,(
% 1.30/0.55    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.30/0.55    inference(subsumption_resolution,[],[f166,f170])).
% 1.30/0.55  fof(f170,plain,(
% 1.30/0.55    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.30/0.55    inference(resolution,[],[f169,f81])).
% 1.30/0.55  fof(f81,plain,(
% 1.30/0.55    ( ! [X0] : (r2_hidden(sK10(X0),X0) | k1_xboole_0 = X0) )),
% 1.30/0.55    inference(cnf_transformation,[],[f53])).
% 1.30/0.55  fof(f53,plain,(
% 1.30/0.55    ! [X0] : (r2_hidden(sK10(X0),X0) | k1_xboole_0 = X0)),
% 1.30/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f28,f52])).
% 1.30/0.55  % (23238)Refutation not found, incomplete strategy% (23238)------------------------------
% 1.30/0.55  % (23238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (23238)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (23238)Memory used [KB]: 10746
% 1.30/0.55  % (23238)Time elapsed: 0.146 s
% 1.30/0.55  % (23238)------------------------------
% 1.30/0.55  % (23238)------------------------------
% 1.30/0.55  % (23237)Refutation not found, incomplete strategy% (23237)------------------------------
% 1.30/0.55  % (23237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (23237)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (23237)Memory used [KB]: 10618
% 1.30/0.55  % (23237)Time elapsed: 0.144 s
% 1.30/0.55  % (23237)------------------------------
% 1.30/0.55  % (23237)------------------------------
% 1.30/0.55  % (23236)Refutation not found, incomplete strategy% (23236)------------------------------
% 1.30/0.55  % (23236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (23236)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (23236)Memory used [KB]: 10746
% 1.30/0.55  % (23236)Time elapsed: 0.145 s
% 1.30/0.55  % (23236)------------------------------
% 1.30/0.55  % (23236)------------------------------
% 1.30/0.55  % (23228)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.55  % (23244)Refutation not found, incomplete strategy% (23244)------------------------------
% 1.30/0.55  % (23244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (23244)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (23244)Memory used [KB]: 10618
% 1.30/0.55  % (23244)Time elapsed: 0.142 s
% 1.30/0.55  % (23244)------------------------------
% 1.30/0.55  % (23244)------------------------------
% 1.30/0.55  % (23256)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.55  fof(f52,plain,(
% 1.30/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK10(X0),X0))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f28,plain,(
% 1.30/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.30/0.55    inference(ennf_transformation,[],[f4])).
% 1.30/0.55  fof(f4,axiom,(
% 1.30/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.30/0.55  fof(f169,plain,(
% 1.30/0.55    ( ! [X3] : (~r2_hidden(X3,k10_relat_1(sK1,k1_xboole_0))) )),
% 1.30/0.55    inference(resolution,[],[f167,f148])).
% 1.30/0.55  fof(f148,plain,(
% 1.30/0.55    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) )),
% 1.30/0.55    inference(resolution,[],[f89,f126])).
% 1.30/0.55  fof(f126,plain,(
% 1.30/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.30/0.55    inference(trivial_inequality_removal,[],[f125])).
% 1.30/0.55  fof(f125,plain,(
% 1.30/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X0,k1_xboole_0)) )),
% 1.30/0.55    inference(superposition,[],[f59,f123])).
% 1.30/0.55  fof(f123,plain,(
% 1.30/0.55    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.30/0.55    inference(resolution,[],[f119,f99])).
% 1.30/0.55  fof(f99,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.30/0.55    inference(resolution,[],[f58,f60])).
% 1.30/0.55  fof(f58,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.30/0.55    inference(cnf_transformation,[],[f33])).
% 1.30/0.55  fof(f33,plain,(
% 1.30/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.30/0.55    inference(nnf_transformation,[],[f1])).
% 1.30/0.55  fof(f1,axiom,(
% 1.30/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.30/0.55  fof(f119,plain,(
% 1.30/0.55    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.30/0.55    inference(resolution,[],[f118,f90])).
% 1.30/0.55  fof(f90,plain,(
% 1.30/0.55    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.30/0.55    inference(equality_resolution,[],[f64])).
% 1.30/0.55  fof(f64,plain,(
% 1.30/0.55    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f24])).
% 1.30/0.55  fof(f24,plain,(
% 1.30/0.55    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.30/0.55    inference(ennf_transformation,[],[f5])).
% 1.30/0.55  fof(f5,axiom,(
% 1.30/0.55    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.30/0.55  fof(f118,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 1.30/0.55    inference(duplicate_literal_removal,[],[f115])).
% 1.30/0.55  fof(f115,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 1.30/0.55    inference(resolution,[],[f107,f61])).
% 1.30/0.55  fof(f61,plain,(
% 1.30/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f35])).
% 1.30/0.55  fof(f35,plain,(
% 1.30/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.30/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f34])).
% 1.30/0.55  fof(f34,plain,(
% 1.30/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f23,plain,(
% 1.30/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.30/0.55    inference(ennf_transformation,[],[f19])).
% 1.30/0.55  fof(f19,plain,(
% 1.30/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.55    inference(rectify,[],[f3])).
% 1.30/0.55  fof(f3,axiom,(
% 1.30/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.30/0.55  fof(f107,plain,(
% 1.30/0.55    ( ! [X4,X2,X3] : (~r2_hidden(sK2(X2,X3),X4) | ~r1_xboole_0(X2,X4) | r1_xboole_0(X2,X3)) )),
% 1.30/0.55    inference(resolution,[],[f63,f61])).
% 1.30/0.55  fof(f63,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f35])).
% 1.30/0.55  fof(f59,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f33])).
% 1.30/0.55  fof(f89,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.30/0.55    inference(definition_unfolding,[],[f57,f88])).
% 1.30/0.55  fof(f88,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.30/0.55    inference(definition_unfolding,[],[f82,f87])).
% 1.30/0.55  fof(f87,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.30/0.55    inference(definition_unfolding,[],[f83,f86])).
% 1.30/0.55  fof(f86,plain,(
% 1.30/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.30/0.55    inference(definition_unfolding,[],[f84,f85])).
% 1.30/0.55  fof(f85,plain,(
% 1.30/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f9])).
% 1.30/0.55  fof(f9,axiom,(
% 1.30/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.30/0.55  fof(f84,plain,(
% 1.30/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f8])).
% 1.30/0.55  fof(f8,axiom,(
% 1.30/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.30/0.55  fof(f83,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f7])).
% 1.30/0.55  fof(f7,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.30/0.55  fof(f82,plain,(
% 1.30/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f6])).
% 1.30/0.55  fof(f6,axiom,(
% 1.30/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.55  fof(f57,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f21])).
% 1.30/0.55  fof(f21,plain,(
% 1.30/0.55    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.30/0.55    inference(ennf_transformation,[],[f12])).
% 1.30/0.55  fof(f12,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.30/0.55  fof(f167,plain,(
% 1.30/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,sK1),X1) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 1.30/0.55    inference(resolution,[],[f68,f54])).
% 1.30/0.55  fof(f54,plain,(
% 1.30/0.55    v1_relat_1(sK1)),
% 1.30/0.55    inference(cnf_transformation,[],[f32])).
% 1.30/0.55  fof(f32,plain,(
% 1.30/0.55    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.30/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).
% 1.30/0.55  fof(f31,plain,(
% 1.30/0.55    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f30,plain,(
% 1.30/0.55    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.30/0.55    inference(flattening,[],[f29])).
% 1.30/0.55  fof(f29,plain,(
% 1.30/0.55    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.30/0.55    inference(nnf_transformation,[],[f20])).
% 1.30/0.55  fof(f20,plain,(
% 1.30/0.55    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.30/0.55    inference(ennf_transformation,[],[f18])).
% 1.30/0.55  fof(f18,negated_conjecture,(
% 1.30/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.30/0.55    inference(negated_conjecture,[],[f17])).
% 1.30/0.55  fof(f17,conjecture,(
% 1.30/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 1.30/0.55  fof(f68,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f39])).
% 1.30/0.55  fof(f39,plain,(
% 1.30/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.30/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 1.30/0.55  fof(f38,plain,(
% 1.30/0.55    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f37,plain,(
% 1.30/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.30/0.55    inference(rectify,[],[f36])).
% 1.30/0.55  fof(f36,plain,(
% 1.30/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.30/0.55    inference(nnf_transformation,[],[f25])).
% 1.30/0.55  fof(f25,plain,(
% 1.30/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.30/0.55    inference(ennf_transformation,[],[f15])).
% 1.30/0.55  fof(f15,axiom,(
% 1.30/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 1.30/0.55  fof(f166,plain,(
% 1.30/0.55    k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.30/0.55    inference(subsumption_resolution,[],[f164,f55])).
% 1.30/0.55  fof(f55,plain,(
% 1.30/0.55    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.30/0.55    inference(cnf_transformation,[],[f32])).
% 1.30/0.55  fof(f164,plain,(
% 1.30/0.55    k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0) | ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.30/0.55    inference(superposition,[],[f56,f146])).
% 1.30/0.55  fof(f146,plain,(
% 1.30/0.55    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.30/0.55    inference(superposition,[],[f145,f105])).
% 1.30/0.55  fof(f105,plain,(
% 1.30/0.55    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.30/0.55    inference(resolution,[],[f55,f58])).
% 1.30/0.55  fof(f145,plain,(
% 1.30/0.55    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))) )),
% 1.30/0.55    inference(resolution,[],[f74,f54])).
% 1.30/0.55  fof(f74,plain,(
% 1.30/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 1.30/0.55    inference(cnf_transformation,[],[f26])).
% 1.30/0.55  fof(f26,plain,(
% 1.30/0.55    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.30/0.55    inference(ennf_transformation,[],[f16])).
% 1.30/0.55  fof(f16,axiom,(
% 1.30/0.55    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 1.30/0.55  fof(f56,plain,(
% 1.30/0.55    k1_xboole_0 != k10_relat_1(sK1,sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.30/0.55    inference(cnf_transformation,[],[f32])).
% 1.30/0.55  fof(f243,plain,(
% 1.30/0.55    r1_xboole_0(sK0,k2_relat_1(sK1))),
% 1.30/0.55    inference(duplicate_literal_removal,[],[f242])).
% 1.30/0.55  fof(f242,plain,(
% 1.30/0.55    r1_xboole_0(sK0,k2_relat_1(sK1)) | r1_xboole_0(sK0,k2_relat_1(sK1))),
% 1.30/0.55    inference(resolution,[],[f234,f62])).
% 1.30/0.55  fof(f62,plain,(
% 1.30/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f35])).
% 1.30/0.55  fof(f234,plain,(
% 1.30/0.55    ( ! [X1] : (~r2_hidden(sK2(sK0,X1),k2_relat_1(sK1)) | r1_xboole_0(sK0,X1)) )),
% 1.30/0.55    inference(resolution,[],[f232,f61])).
% 1.30/0.55  fof(f232,plain,(
% 1.30/0.55    ( ! [X2] : (~r2_hidden(X2,sK0) | ~r2_hidden(X2,k2_relat_1(sK1))) )),
% 1.30/0.55    inference(subsumption_resolution,[],[f230,f148])).
% 1.30/0.55  fof(f230,plain,(
% 1.30/0.55    ( ! [X2] : (r2_hidden(sK6(sK1,X2),k1_xboole_0) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,k2_relat_1(sK1))) )),
% 1.30/0.55    inference(superposition,[],[f227,f175])).
% 1.30/0.55  fof(f227,plain,(
% 1.30/0.55    ( ! [X4,X3] : (r2_hidden(sK6(sK1,X3),k10_relat_1(sK1,X4)) | ~r2_hidden(X3,X4) | ~r2_hidden(X3,k2_relat_1(sK1))) )),
% 1.30/0.55    inference(resolution,[],[f225,f92])).
% 1.30/0.55  fof(f92,plain,(
% 1.30/0.55    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.30/0.55    inference(equality_resolution,[],[f70])).
% 1.30/0.55  fof(f70,plain,(
% 1.30/0.55    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.30/0.55    inference(cnf_transformation,[],[f45])).
% 1.30/0.55  fof(f45,plain,(
% 1.30/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.30/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f41,f44,f43,f42])).
% 1.30/0.55  fof(f42,plain,(
% 1.30/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f43,plain,(
% 1.30/0.55    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f44,plain,(
% 1.30/0.55    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f41,plain,(
% 1.30/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.30/0.55    inference(rectify,[],[f40])).
% 1.30/0.55  fof(f40,plain,(
% 1.30/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.30/0.55    inference(nnf_transformation,[],[f14])).
% 1.30/0.55  fof(f14,axiom,(
% 1.30/0.55    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.30/0.55  fof(f225,plain,(
% 1.30/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,X0),sK1) | ~r2_hidden(X0,X1) | r2_hidden(X2,k10_relat_1(sK1,X1))) )),
% 1.30/0.55    inference(resolution,[],[f93,f54])).
% 1.30/0.55  fof(f93,plain,(
% 1.30/0.55    ( ! [X6,X0,X7,X1] : (~v1_relat_1(X0) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | r2_hidden(X6,k10_relat_1(X0,X1))) )),
% 1.30/0.55    inference(equality_resolution,[],[f77])).
% 1.30/0.55  fof(f77,plain,(
% 1.30/0.55    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.30/0.55    inference(cnf_transformation,[],[f51])).
% 1.30/0.55  fof(f51,plain,(
% 1.30/0.55    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK7(X0,X1,X2),X4),X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK9(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK9(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.30/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f47,f50,f49,f48])).
% 1.30/0.55  fof(f48,plain,(
% 1.30/0.55    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK7(X0,X1,X2),X4),X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),X5),X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f49,plain,(
% 1.30/0.55    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),X5),X0)) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f50,plain,(
% 1.30/0.55    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK9(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK9(X0,X1,X6)),X0)))),
% 1.30/0.55    introduced(choice_axiom,[])).
% 1.30/0.55  fof(f47,plain,(
% 1.30/0.55    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.30/0.55    inference(rectify,[],[f46])).
% 1.30/0.55  fof(f46,plain,(
% 1.30/0.55    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.30/0.55    inference(nnf_transformation,[],[f27])).
% 1.30/0.55  fof(f27,plain,(
% 1.30/0.55    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.30/0.55    inference(ennf_transformation,[],[f13])).
% 1.30/0.55  fof(f13,axiom,(
% 1.30/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.30/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 1.30/0.55  % SZS output end Proof for theBenchmark
% 1.30/0.55  % (23232)------------------------------
% 1.30/0.55  % (23232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (23232)Termination reason: Refutation
% 1.30/0.55  
% 1.30/0.55  % (23232)Memory used [KB]: 6396
% 1.30/0.55  % (23232)Time elapsed: 0.124 s
% 1.30/0.55  % (23232)------------------------------
% 1.30/0.55  % (23232)------------------------------
% 1.30/0.56  % (23226)Success in time 0.19 s
%------------------------------------------------------------------------------

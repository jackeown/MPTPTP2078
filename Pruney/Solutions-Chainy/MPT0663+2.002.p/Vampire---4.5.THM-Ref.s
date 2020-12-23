%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:13 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 254 expanded)
%              Number of leaves         :   18 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :  208 ( 507 expanded)
%              Number of equality atoms :   89 ( 255 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(subsumption_resolution,[],[f86,f37])).

fof(f37,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
    & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
      & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

fof(f86,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f85,f75])).

fof(f75,plain,(
    sK0 = k1_funct_1(k6_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f38,f39,f73,f69])).

fof(f69,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

% (5951)Refutation not found, incomplete strategy% (5951)------------------------------
% (5951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5951)Termination reason: Refutation not found, incomplete strategy

% (5951)Memory used [KB]: 10618
% (5951)Time elapsed: 0.119 s
% (5951)------------------------------
% (5951)------------------------------
fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f73,plain,(
    r2_hidden(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f65,f71,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f71,plain,(
    r2_hidden(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f64,f66])).

fof(f66,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f62,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f61])).

% (5974)Refutation not found, incomplete strategy% (5974)------------------------------
% (5974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5974)Termination reason: Refutation not found, incomplete strategy

% (5974)Memory used [KB]: 6268
% (5974)Time elapsed: 0.124 s
% (5974)------------------------------
% (5974)------------------------------
fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

% (5972)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

% (5952)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f64,plain,(
    r2_hidden(sK0,k1_setfam_1(k6_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1))) ),
    inference(definition_unfolding,[],[f36,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f36,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f28])).

% (5976)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f63])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f39,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

% (5970)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f85,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) ),
    inference(unit_resulting_resolution,[],[f73,f83])).

fof(f83,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2) ) ),
    inference(forward_demodulation,[],[f82,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f82,plain,(
    ! [X2,X1] :
      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X1))) ) ),
    inference(subsumption_resolution,[],[f81,f38])).

fof(f81,plain,(
    ! [X2,X1] :
      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f80,plain,(
    ! [X2,X1] :
      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f79,f34])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X2,X1] :
      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f78,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ! [X2,X1] :
      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f51,f72])).

fof(f72,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    inference(unit_resulting_resolution,[],[f34,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (5959)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (5950)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (5949)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (5967)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (5953)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (5954)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (5959)Refutation not found, incomplete strategy% (5959)------------------------------
% 0.21/0.51  % (5959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5958)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (5959)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5959)Memory used [KB]: 10618
% 0.21/0.51  % (5959)Time elapsed: 0.103 s
% 0.21/0.51  % (5959)------------------------------
% 0.21/0.51  % (5959)------------------------------
% 0.21/0.51  % (5971)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (5971)Refutation not found, incomplete strategy% (5971)------------------------------
% 0.21/0.51  % (5971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5971)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5971)Memory used [KB]: 10746
% 0.21/0.51  % (5971)Time elapsed: 0.084 s
% 0.21/0.51  % (5971)------------------------------
% 0.21/0.51  % (5971)------------------------------
% 0.21/0.51  % (5975)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (5957)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (5964)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (5961)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (5960)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (5955)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.52  % (5951)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.52  % (5974)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.52  % (5975)Refutation found. Thanks to Tanya!
% 1.32/0.52  % SZS status Theorem for theBenchmark
% 1.32/0.52  % SZS output start Proof for theBenchmark
% 1.32/0.52  fof(f87,plain,(
% 1.32/0.52    $false),
% 1.32/0.52    inference(subsumption_resolution,[],[f86,f37])).
% 1.32/0.52  fof(f37,plain,(
% 1.32/0.52    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)),
% 1.32/0.52    inference(cnf_transformation,[],[f28])).
% 1.32/0.52  fof(f28,plain,(
% 1.32/0.52    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.32/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f27])).
% 1.32/0.52  fof(f27,plain,(
% 1.32/0.52    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.32/0.52    introduced(choice_axiom,[])).
% 1.32/0.52  fof(f20,plain,(
% 1.32/0.52    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.32/0.52    inference(flattening,[],[f19])).
% 1.32/0.52  fof(f19,plain,(
% 1.32/0.52    ? [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.32/0.52    inference(ennf_transformation,[],[f17])).
% 1.32/0.52  fof(f17,negated_conjecture,(
% 1.32/0.52    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 1.32/0.52    inference(negated_conjecture,[],[f16])).
% 1.32/0.52  fof(f16,conjecture,(
% 1.32/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).
% 1.32/0.52  fof(f86,plain,(
% 1.32/0.52    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)),
% 1.32/0.52    inference(forward_demodulation,[],[f85,f75])).
% 1.32/0.52  fof(f75,plain,(
% 1.32/0.52    sK0 = k1_funct_1(k6_relat_1(sK1),sK0)),
% 1.32/0.52    inference(unit_resulting_resolution,[],[f38,f39,f73,f69])).
% 1.32/0.52  fof(f69,plain,(
% 1.32/0.52    ( ! [X0,X3] : (k1_funct_1(k6_relat_1(X0),X3) = X3 | ~r2_hidden(X3,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.32/0.52    inference(equality_resolution,[],[f48])).
% 1.32/0.52  fof(f48,plain,(
% 1.32/0.52    ( ! [X0,X3,X1] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0) | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f33])).
% 1.32/0.52  fof(f33,plain,(
% 1.32/0.52    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.32/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.32/0.52  fof(f32,plain,(
% 1.32/0.52    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 1.32/0.52    introduced(choice_axiom,[])).
% 1.32/0.52  fof(f31,plain,(
% 1.32/0.52    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.32/0.52    inference(rectify,[],[f30])).
% 1.32/0.52  fof(f30,plain,(
% 1.32/0.52    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.32/0.52    inference(flattening,[],[f29])).
% 1.32/0.52  % (5951)Refutation not found, incomplete strategy% (5951)------------------------------
% 1.32/0.52  % (5951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.52  % (5951)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.52  
% 1.32/0.52  % (5951)Memory used [KB]: 10618
% 1.32/0.52  % (5951)Time elapsed: 0.119 s
% 1.32/0.52  % (5951)------------------------------
% 1.32/0.52  % (5951)------------------------------
% 1.32/0.52  fof(f29,plain,(
% 1.32/0.52    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.32/0.52    inference(nnf_transformation,[],[f23])).
% 1.32/0.52  fof(f23,plain,(
% 1.32/0.52    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.32/0.52    inference(flattening,[],[f22])).
% 1.32/0.52  fof(f22,plain,(
% 1.32/0.52    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.32/0.52    inference(ennf_transformation,[],[f15])).
% 1.32/0.52  fof(f15,axiom,(
% 1.32/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 1.32/0.52  fof(f73,plain,(
% 1.32/0.52    r2_hidden(sK0,sK1)),
% 1.32/0.52    inference(unit_resulting_resolution,[],[f65,f71,f52])).
% 1.32/0.52  fof(f52,plain,(
% 1.32/0.52    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f26])).
% 1.32/0.52  fof(f26,plain,(
% 1.32/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.32/0.52    inference(ennf_transformation,[],[f18])).
% 1.32/0.52  fof(f18,plain,(
% 1.32/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.32/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 1.32/0.52  fof(f1,axiom,(
% 1.32/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.32/0.52  fof(f71,plain,(
% 1.32/0.52    r2_hidden(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_relat_1(sK2))))),
% 1.32/0.52    inference(forward_demodulation,[],[f64,f66])).
% 1.32/0.52  fof(f66,plain,(
% 1.32/0.52    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.32/0.52    inference(definition_unfolding,[],[f43,f62,f62])).
% 1.32/0.52  fof(f62,plain,(
% 1.32/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.32/0.52    inference(definition_unfolding,[],[f45,f61])).
% 1.32/0.52  % (5974)Refutation not found, incomplete strategy% (5974)------------------------------
% 1.32/0.52  % (5974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.52  % (5974)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.52  
% 1.32/0.52  % (5974)Memory used [KB]: 6268
% 1.32/0.52  % (5974)Time elapsed: 0.124 s
% 1.32/0.52  % (5974)------------------------------
% 1.32/0.52  % (5974)------------------------------
% 1.32/0.52  fof(f61,plain,(
% 1.32/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.32/0.52    inference(definition_unfolding,[],[f53,f60])).
% 1.32/0.52  fof(f60,plain,(
% 1.32/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.32/0.52    inference(definition_unfolding,[],[f54,f59])).
% 1.32/0.52  fof(f59,plain,(
% 1.32/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.32/0.52    inference(definition_unfolding,[],[f55,f58])).
% 1.32/0.52  fof(f58,plain,(
% 1.32/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.52    inference(definition_unfolding,[],[f56,f57])).
% 1.32/0.52  fof(f57,plain,(
% 1.32/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f9])).
% 1.32/0.52  fof(f9,axiom,(
% 1.32/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.32/0.52  fof(f56,plain,(
% 1.32/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f8])).
% 1.32/0.52  fof(f8,axiom,(
% 1.32/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.32/0.52  fof(f55,plain,(
% 1.32/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f7])).
% 1.32/0.52  fof(f7,axiom,(
% 1.32/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.32/0.52  fof(f54,plain,(
% 1.32/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f6])).
% 1.32/0.52  fof(f6,axiom,(
% 1.32/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.32/0.52  fof(f53,plain,(
% 1.32/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f5])).
% 1.32/0.52  fof(f5,axiom,(
% 1.32/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.52  fof(f45,plain,(
% 1.32/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f4])).
% 1.32/0.52  fof(f4,axiom,(
% 1.32/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.52  fof(f43,plain,(
% 1.32/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f3])).
% 1.32/0.52  % (5972)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.32/0.52  fof(f3,axiom,(
% 1.32/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.32/0.52  % (5952)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.52  fof(f64,plain,(
% 1.32/0.52    r2_hidden(sK0,k1_setfam_1(k6_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1)))),
% 1.32/0.52    inference(definition_unfolding,[],[f36,f63])).
% 1.32/0.52  fof(f63,plain,(
% 1.32/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.32/0.52    inference(definition_unfolding,[],[f44,f62])).
% 1.32/0.52  fof(f44,plain,(
% 1.32/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.32/0.52    inference(cnf_transformation,[],[f10])).
% 1.32/0.52  fof(f10,axiom,(
% 1.32/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.32/0.52  fof(f36,plain,(
% 1.32/0.52    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 1.32/0.52    inference(cnf_transformation,[],[f28])).
% 1.32/0.52  % (5976)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.52  fof(f65,plain,(
% 1.32/0.52    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.32/0.52    inference(definition_unfolding,[],[f42,f63])).
% 1.32/0.52  fof(f42,plain,(
% 1.32/0.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.32/0.52    inference(cnf_transformation,[],[f2])).
% 1.32/0.52  fof(f2,axiom,(
% 1.32/0.52    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.32/0.52  fof(f39,plain,(
% 1.32/0.52    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.32/0.52    inference(cnf_transformation,[],[f13])).
% 1.32/0.52  fof(f13,axiom,(
% 1.32/0.52    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.32/0.52  fof(f38,plain,(
% 1.32/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.32/0.52    inference(cnf_transformation,[],[f13])).
% 1.32/0.52  % (5970)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.52  fof(f85,plain,(
% 1.32/0.52    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))),
% 1.32/0.52    inference(unit_resulting_resolution,[],[f73,f83])).
% 1.32/0.52  fof(f83,plain,(
% 1.32/0.52    ( ! [X2,X1] : (~r2_hidden(X2,X1) | k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2)) )),
% 1.32/0.52    inference(forward_demodulation,[],[f82,f40])).
% 1.32/0.52  fof(f40,plain,(
% 1.32/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.32/0.52    inference(cnf_transformation,[],[f11])).
% 1.32/0.52  fof(f11,axiom,(
% 1.32/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.32/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.32/0.52  fof(f82,plain,(
% 1.32/0.52    ( ! [X2,X1] : (k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X1)))) )),
% 1.32/0.52    inference(subsumption_resolution,[],[f81,f38])).
% 1.32/0.52  fof(f81,plain,(
% 1.32/0.52    ( ! [X2,X1] : (k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.32/0.52    inference(subsumption_resolution,[],[f80,f39])).
% 1.32/0.52  fof(f80,plain,(
% 1.32/0.52    ( ! [X2,X1] : (k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X1))) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.32/0.52    inference(subsumption_resolution,[],[f79,f34])).
% 1.32/0.52  fof(f34,plain,(
% 1.32/0.52    v1_relat_1(sK2)),
% 1.32/0.52    inference(cnf_transformation,[],[f28])).
% 1.32/0.52  fof(f79,plain,(
% 1.32/0.52    ( ! [X2,X1] : (k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.32/0.52    inference(subsumption_resolution,[],[f78,f35])).
% 1.32/0.52  fof(f35,plain,(
% 1.32/0.52    v1_funct_1(sK2)),
% 1.32/0.52    inference(cnf_transformation,[],[f28])).
% 1.32/0.52  fof(f78,plain,(
% 1.32/0.52    ( ! [X2,X1] : (k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.32/0.52    inference(superposition,[],[f51,f72])).
% 1.32/0.53  fof(f72,plain,(
% 1.32/0.53    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) )),
% 1.32/0.53    inference(unit_resulting_resolution,[],[f34,f46])).
% 1.32/0.53  fof(f46,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f21])).
% 1.32/0.53  fof(f21,plain,(
% 1.32/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f12])).
% 1.32/0.53  fof(f12,axiom,(
% 1.32/0.53    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.32/0.53  fof(f51,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f25])).
% 1.32/0.53  fof(f25,plain,(
% 1.32/0.53    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.32/0.53    inference(flattening,[],[f24])).
% 1.32/0.53  fof(f24,plain,(
% 1.32/0.53    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.32/0.53    inference(ennf_transformation,[],[f14])).
% 1.32/0.53  fof(f14,axiom,(
% 1.32/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 1.32/0.53  % SZS output end Proof for theBenchmark
% 1.32/0.53  % (5975)------------------------------
% 1.32/0.53  % (5975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (5975)Termination reason: Refutation
% 1.32/0.53  
% 1.32/0.53  % (5975)Memory used [KB]: 10746
% 1.32/0.53  % (5975)Time elapsed: 0.118 s
% 1.32/0.53  % (5975)------------------------------
% 1.32/0.53  % (5975)------------------------------
% 1.32/0.53  % (5966)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.53  % (5965)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.53  % (5969)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.53  % (5966)Refutation not found, incomplete strategy% (5966)------------------------------
% 1.32/0.53  % (5966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (5966)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (5966)Memory used [KB]: 10618
% 1.32/0.53  % (5966)Time elapsed: 0.134 s
% 1.32/0.53  % (5966)------------------------------
% 1.32/0.53  % (5966)------------------------------
% 1.32/0.53  % (5963)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.53  % (5948)Success in time 0.174 s
%------------------------------------------------------------------------------

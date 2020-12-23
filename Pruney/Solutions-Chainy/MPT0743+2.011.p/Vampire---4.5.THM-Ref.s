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
% DateTime   : Thu Dec  3 12:55:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 221 expanded)
%              Number of leaves         :   17 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  304 ( 802 expanded)
%              Number of equality atoms :   28 (  63 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f70,f86,f89,f161,f199])).

fof(f199,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f196,f71])).

fof(f71,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f49,f58])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f196,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f63,f191])).

fof(f191,plain,
    ( sK0 = sK1
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f189,f178])).

fof(f178,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f63,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f189,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f185,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f50,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

% (6877)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f4,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f185,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f184,f80])).

fof(f80,plain,
    ( v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_3
  <=> v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f184,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f183,f32])).

% (6868)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f32,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f183,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | spl2_2 ),
    inference(resolution,[],[f68,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f68,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_2
  <=> r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f63,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f161,plain,
    ( spl2_1
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f156,f53])).

fof(f53,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f35,f50])).

fof(f35,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f156,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | spl2_1
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f96,f148])).

fof(f148,plain,
    ( sK0 = sK1
    | spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f147,f31])).

fof(f31,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f147,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f146,f32])).

fof(f146,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f135,f64])).

fof(f64,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f135,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f126,f109])).

fof(f109,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f96,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f50])).

% (6880)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f126,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | r2_hidden(X1,X2)
      | X1 = X2
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X2,X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(X2,X1)
      | X1 = X2
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X2)
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f113,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f41,f39])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f113,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ v3_ordinal1(X3)
      | r2_hidden(X2,X3)
      | X2 = X3
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f76,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f85,f49])).

fof(f85,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_4
  <=> r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f89,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f87,f31])).

fof(f87,plain,
    ( ~ v3_ordinal1(sK0)
    | spl2_3 ),
    inference(resolution,[],[f81,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f38,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f81,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f79])).

% (6880)Refutation not found, incomplete strategy% (6880)------------------------------
% (6880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6880)Termination reason: Refutation not found, incomplete strategy

% (6880)Memory used [KB]: 1663
% (6880)Time elapsed: 0.131 s
% (6880)------------------------------
% (6880)------------------------------
fof(f86,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f77,f66,f83,f79])).

fof(f77,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f74,f32])).

fof(f74,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ spl2_2 ),
    inference(resolution,[],[f41,f67])).

fof(f67,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f70,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f52,f66,f62])).

fof(f52,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f33,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f51,f66,f62])).

fof(f51,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f34,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:26:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (6865)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (6869)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (6863)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (6875)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (6871)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (6885)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (6882)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (6892)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (6881)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (6884)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (6876)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (6874)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (6869)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (6866)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f69,f70,f86,f89,f161,f199])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    ~spl2_1 | spl2_2 | ~spl2_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f198])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    $false | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f196,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f49,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.54  fof(f196,plain,(
% 0.22/0.54    r2_hidden(sK0,sK0) | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.22/0.54    inference(backward_demodulation,[],[f63,f191])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    sK0 = sK1 | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f189,f178])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    ~r2_hidden(sK1,sK0) | ~spl2_1),
% 0.22/0.54    inference(resolution,[],[f63,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    r2_hidden(sK1,sK0) | sK0 = sK1 | (spl2_2 | ~spl2_3)),
% 0.22/0.54    inference(resolution,[],[f185,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f46,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f37,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  % (6877)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | (spl2_2 | ~spl2_3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f184,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~spl2_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    spl2_3 <=> v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | spl2_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f183,f32])).
% 0.22/0.54  % (6868)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    v3_ordinal1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | spl2_2),
% 0.22/0.54    inference(resolution,[],[f68,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ~r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | spl2_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    spl2_2 <=> r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    spl2_1 | ~spl2_4),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f160])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    $false | (spl2_1 | ~spl2_4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f156,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f35,f50])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | (spl2_1 | ~spl2_4)),
% 0.22/0.54    inference(backward_demodulation,[],[f96,f148])).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    sK0 = sK1 | (spl2_1 | ~spl2_4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f147,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    v3_ordinal1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    sK0 = sK1 | ~v3_ordinal1(sK0) | (spl2_1 | ~spl2_4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f146,f32])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | (spl2_1 | ~spl2_4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f135,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ~r2_hidden(sK0,sK1) | spl2_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f62])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl2_4),
% 0.22/0.54    inference(resolution,[],[f126,f109])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ~r2_hidden(sK1,sK0) | ~spl2_4),
% 0.22/0.54    inference(resolution,[],[f96,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f47,f50])).
% 0.22/0.54  % (6880)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ( ! [X2,X1] : (r2_hidden(X2,X1) | r2_hidden(X1,X2) | X1 = X2 | ~v3_ordinal1(X2) | ~v3_ordinal1(X1)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f124])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ( ! [X2,X1] : (~v3_ordinal1(X1) | r2_hidden(X2,X1) | X1 = X2 | ~v3_ordinal1(X2) | ~v3_ordinal1(X1) | ~v3_ordinal1(X2) | r2_hidden(X1,X2)) )),
% 0.22/0.54    inference(resolution,[],[f113,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(resolution,[],[f41,f39])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r1_tarski(X2,X3) | ~v3_ordinal1(X3) | r2_hidden(X2,X3) | X2 = X3 | ~v3_ordinal1(X2)) )),
% 0.22/0.54    inference(resolution,[],[f76,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~spl2_4),
% 0.22/0.54    inference(resolution,[],[f85,f49])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | ~spl2_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    spl2_4 <=> r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    spl2_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f88])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    $false | spl2_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f87,f31])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ~v3_ordinal1(sK0) | spl2_3),
% 0.22/0.54    inference(resolution,[],[f81,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f38,f50])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | spl2_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f79])).
% 0.22/0.54  % (6880)Refutation not found, incomplete strategy% (6880)------------------------------
% 0.22/0.54  % (6880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6880)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (6880)Memory used [KB]: 1663
% 0.22/0.54  % (6880)Time elapsed: 0.131 s
% 0.22/0.54  % (6880)------------------------------
% 0.22/0.54  % (6880)------------------------------
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ~spl2_3 | spl2_4 | ~spl2_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f77,f66,f83,f79])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~spl2_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f74,f32])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) | ~spl2_2),
% 0.22/0.54    inference(resolution,[],[f41,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | ~spl2_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f66])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    spl2_1 | spl2_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f52,f66,f62])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.54    inference(definition_unfolding,[],[f33,f50])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ~spl2_1 | ~spl2_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f51,f66,f62])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ~r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 0.22/0.54    inference(definition_unfolding,[],[f34,f50])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (6869)------------------------------
% 0.22/0.54  % (6869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6869)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (6867)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (6869)Memory used [KB]: 10746
% 0.22/0.54  % (6869)Time elapsed: 0.116 s
% 0.22/0.54  % (6869)------------------------------
% 0.22/0.54  % (6869)------------------------------
% 0.22/0.54  % (6862)Success in time 0.178 s
%------------------------------------------------------------------------------

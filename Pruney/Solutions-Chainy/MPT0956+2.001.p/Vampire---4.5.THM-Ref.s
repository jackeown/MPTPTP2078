%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 (  78 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   15
%              Number of atoms          :  230 ( 276 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(subsumption_resolution,[],[f122,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f122,plain,(
    ~ v1_relat_1(k1_wellord2(sK6)) ),
    inference(resolution,[],[f120,f45])).

fof(f45,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f8,f12,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),X0)
          | ~ r2_hidden(X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (20967)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (20975)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (20977)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (20961)Termination reason: Refutation not found, incomplete strategy

% (20961)Memory used [KB]: 10490
% (20961)Time elapsed: 0.093 s
% (20961)------------------------------
% (20961)------------------------------
% (20980)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(f120,plain,(
    ~ sP1(k1_wellord2(sK6)) ),
    inference(resolution,[],[f118,f38])).

fof(f38,plain,(
    ~ r1_relat_2(k1_wellord2(sK6),sK6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ~ r1_relat_2(k1_wellord2(sK6),sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f7,f19])).

fof(f19,plain,
    ( ? [X0] : ~ r1_relat_2(k1_wellord2(X0),X0)
   => ~ r1_relat_2(k1_wellord2(sK6),sK6) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : ~ r1_relat_2(k1_wellord2(X0),X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_relat_2(k1_wellord2(X0),X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r1_relat_2(k1_wellord2(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord2)).

fof(f118,plain,(
    ! [X0] :
      ( r1_relat_2(k1_wellord2(X0),X0)
      | ~ sP1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f117,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r1_relat_2(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r1_relat_2(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f117,plain,(
    ! [X0] : sP0(k1_wellord2(X0),X0) ),
    inference(resolution,[],[f116,f72])).

fof(f72,plain,(
    ! [X0] : sP3(k1_wellord2(X0),X0) ),
    inference(resolution,[],[f71,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | sP3(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ~ sP3(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP3(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP4(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ~ sP3(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP3(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP4(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
    <=> ( sP3(X1,X0)
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f71,plain,(
    ! [X0] : sP4(X0,k1_wellord2(X0)) ),
    inference(subsumption_resolution,[],[f70,f39])).

fof(f70,plain,(
    ! [X0] :
      ( sP4(X0,k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP5(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( sP5(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f10,f17,f16,f15,f14])).

fof(f14,plain,(
    ! [X3,X2,X1] :
      ( sP2(X3,X2,X1)
    <=> ( r2_hidden(k4_tarski(X2,X3),X1)
      <=> r1_tarski(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f15,plain,(
    ! [X1,X0] :
      ( sP3(X1,X0)
    <=> ! [X2,X3] :
          ( sP2(X3,X2,X1)
          | ~ r2_hidden(X3,X0)
          | ~ r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ( k1_wellord2(X0) = X1
      <=> sP4(X0,X1) )
      | ~ sP5(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

% (20982)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f63,plain,(
    ! [X1] :
      ( ~ sP5(k1_wellord2(X1),X1)
      | sP4(X1,k1_wellord2(X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0)
      | k1_wellord2(X1) != X0
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X1) = X0
          | ~ sP4(X1,X0) )
        & ( sP4(X1,X0)
          | k1_wellord2(X1) != X0 ) )
      | ~ sP5(X0,X1) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP4(X0,X1) )
        & ( sP4(X0,X1)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP5(X1,X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | sP0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | sP0(X0,X1)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f113,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK7(X0,X1)),X0)
          & r2_hidden(sK7(X0,X1),X1) ) )
      & ( ! [X3] :
            ( r2_hidden(k4_tarski(X3,X3),X0)
            | ~ r2_hidden(X3,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK7(X0,X1)),X0)
        & r2_hidden(sK7(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(k4_tarski(X2,X2),X0)
            & r2_hidden(X2,X1) ) )
      & ( ! [X3] :
            ( r2_hidden(k4_tarski(X3,X3),X0)
            | ~ r2_hidden(X3,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(k4_tarski(X2,X2),X0)
            & r2_hidden(X2,X1) ) )
      & ( ! [X2] :
            ( r2_hidden(k4_tarski(X2,X2),X0)
            | ~ r2_hidden(X2,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f113,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK7(X3,X4),X5)
      | ~ sP3(X3,X5)
      | sP0(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK7(X3,X4),X5)
      | ~ r2_hidden(sK7(X3,X4),X5)
      | ~ sP3(X3,X5)
      | sP0(X3,X4) ) ),
    inference(resolution,[],[f51,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ sP2(sK7(X0,X1),sK7(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f97,f65])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK7(X0,X1),sK7(X0,X1))
      | ~ sP2(sK7(X0,X1),sK7(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f56,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK7(X0,X1)),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),X2)
      | ~ r1_tarski(X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ r1_tarski(X1,X0)
            | ~ r2_hidden(k4_tarski(X1,X0),X2) )
          & ( r1_tarski(X1,X0)
            | r2_hidden(k4_tarski(X1,X0),X2) ) ) )
      & ( ( ( r2_hidden(k4_tarski(X1,X0),X2)
            | ~ r1_tarski(X1,X0) )
          & ( r1_tarski(X1,X0)
            | ~ r2_hidden(k4_tarski(X1,X0),X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X3,X2,X1] :
      ( ( sP2(X3,X2,X1)
        | ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r1_tarski(X2,X3) )
          & ( r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
        | ~ sP2(X3,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X4,X0,X5,X1] :
      ( sP2(X5,X4,X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ~ sP2(sK9(X0,X1),sK8(X0,X1),X0)
          & r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X1) ) )
      & ( ! [X4,X5] :
            ( sP2(X5,X4,X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ sP2(X3,X2,X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ sP2(sK9(X0,X1),sK8(X0,X1),X0)
        & r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2,X3] :
            ( ~ sP2(X3,X2,X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4,X5] :
            ( sP2(X5,X4,X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ( sP3(X1,X0)
        | ? [X2,X3] :
            ( ~ sP2(X3,X2,X1)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2,X3] :
            ( sP2(X3,X2,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ sP3(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:25:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (20964)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (20966)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (20961)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (20964)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (20974)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (20985)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (20966)Refutation not found, incomplete strategy% (20966)------------------------------
% 0.22/0.51  % (20966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20966)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20966)Memory used [KB]: 10490
% 0.22/0.51  % (20966)Time elapsed: 0.093 s
% 0.22/0.51  % (20966)------------------------------
% 0.22/0.51  % (20966)------------------------------
% 0.22/0.51  % (20983)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (20961)Refutation not found, incomplete strategy% (20961)------------------------------
% 0.22/0.51  % (20961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20972)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f122,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ~v1_relat_1(k1_wellord2(sK6))),
% 0.22/0.51    inference(resolution,[],[f120,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(definition_folding,[],[f8,f12,f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1)))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  % (20967)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (20975)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (20977)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (20961)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20961)Memory used [KB]: 10490
% 0.22/0.51  % (20961)Time elapsed: 0.093 s
% 0.22/0.51  % (20961)------------------------------
% 0.22/0.51  % (20961)------------------------------
% 0.22/0.51  % (20980)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_relat_2(X0,X1) <=> sP0(X0,X1)) | ~sP1(X0))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k4_tarski(X2,X2),X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    ~sP1(k1_wellord2(sK6))),
% 0.22/0.51    inference(resolution,[],[f118,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ~r1_relat_2(k1_wellord2(sK6),sK6)),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ~r1_relat_2(k1_wellord2(sK6),sK6)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f7,f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0] : ~r1_relat_2(k1_wellord2(X0),X0) => ~r1_relat_2(k1_wellord2(sK6),sK6)),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0] : ~r1_relat_2(k1_wellord2(X0),X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,negated_conjecture,(
% 0.22/0.51    ~! [X0] : r1_relat_2(k1_wellord2(X0),X0)),
% 0.22/0.51    inference(negated_conjecture,[],[f5])).
% 0.22/0.51  fof(f5,conjecture,(
% 0.22/0.51    ! [X0] : r1_relat_2(k1_wellord2(X0),X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord2)).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    ( ! [X0] : (r1_relat_2(k1_wellord2(X0),X0) | ~sP1(k1_wellord2(X0))) )),
% 0.22/0.51    inference(resolution,[],[f117,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~sP0(X0,X1) | r1_relat_2(X0,X1) | ~sP1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~r1_relat_2(X0,X1))) | ~sP1(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f12])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    ( ! [X0] : (sP0(k1_wellord2(X0),X0)) )),
% 0.22/0.51    inference(resolution,[],[f116,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0] : (sP3(k1_wellord2(X0),X0)) )),
% 0.22/0.51    inference(resolution,[],[f71,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~sP4(X0,X1) | sP3(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP4(X0,X1) | ~sP3(X1,X0) | k3_relat_1(X1) != X0) & ((sP3(X1,X0) & k3_relat_1(X1) = X0) | ~sP4(X0,X1)))),
% 0.22/0.51    inference(flattening,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP4(X0,X1) | (~sP3(X1,X0) | k3_relat_1(X1) != X0)) & ((sP3(X1,X0) & k3_relat_1(X1) = X0) | ~sP4(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (sP4(X0,X1) <=> (sP3(X1,X0) & k3_relat_1(X1) = X0))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0] : (sP4(X0,k1_wellord2(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f70,f39])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0] : (sP4(X0,k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.51    inference(resolution,[],[f63,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP5(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : (sP5(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(definition_folding,[],[f10,f17,f16,f15,f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X3,X2,X1] : (sP2(X3,X2,X1) <=> (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X1,X0] : (sP3(X1,X0) <=> ! [X2,X3] : (sP2(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X1,X0] : ((k1_wellord2(X0) = X1 <=> sP4(X0,X1)) | ~sP5(X1,X0))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.51  % (20982)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X1] : (~sP5(k1_wellord2(X1),X1) | sP4(X1,k1_wellord2(X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP4(X1,X0) | k1_wellord2(X1) != X0 | ~sP5(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1] : (((k1_wellord2(X1) = X0 | ~sP4(X1,X0)) & (sP4(X1,X0) | k1_wellord2(X1) != X0)) | ~sP5(X0,X1))),
% 0.22/0.51    inference(rectify,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X1,X0] : (((k1_wellord2(X0) = X1 | ~sP4(X0,X1)) & (sP4(X0,X1) | k1_wellord2(X0) != X1)) | ~sP5(X1,X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f17])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~sP3(X0,X1) | sP0(X0,X1)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f115])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~sP3(X0,X1) | sP0(X0,X1) | sP0(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f113,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | sP0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP0(X0,X1) | (~r2_hidden(k4_tarski(sK7(X0,X1),sK7(X0,X1)),X0) & r2_hidden(sK7(X0,X1),X1))) & (! [X3] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1)) | ~sP0(X0,X1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK7(X0,X1),sK7(X0,X1)),X0) & r2_hidden(sK7(X0,X1),X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1))) & (! [X3] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1)) | ~sP0(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1)) | ~sP0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f11])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ( ! [X4,X5,X3] : (~r2_hidden(sK7(X3,X4),X5) | ~sP3(X3,X5) | sP0(X3,X4)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f112])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ( ! [X4,X5,X3] : (~r2_hidden(sK7(X3,X4),X5) | ~r2_hidden(sK7(X3,X4),X5) | ~sP3(X3,X5) | sP0(X3,X4)) )),
% 0.22/0.51    inference(resolution,[],[f51,f100])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~sP2(sK7(X0,X1),sK7(X0,X1),X0) | sP0(X0,X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f97,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(sK7(X0,X1),sK7(X0,X1)) | ~sP2(sK7(X0,X1),sK7(X0,X1),X0) | sP0(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f56,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK7(X0,X1),sK7(X0,X1)),X0) | sP0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X0),X2) | ~r1_tarski(X1,X0) | ~sP2(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~r1_tarski(X1,X0) | ~r2_hidden(k4_tarski(X1,X0),X2)) & (r1_tarski(X1,X0) | r2_hidden(k4_tarski(X1,X0),X2)))) & (((r2_hidden(k4_tarski(X1,X0),X2) | ~r1_tarski(X1,X0)) & (r1_tarski(X1,X0) | ~r2_hidden(k4_tarski(X1,X0),X2))) | ~sP2(X0,X1,X2)))),
% 0.22/0.51    inference(rectify,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X3,X2,X1] : ((sP2(X3,X2,X1) | ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)))) & (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~sP2(X3,X2,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f14])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X4,X0,X5,X1] : (sP2(X5,X4,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~sP3(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP3(X0,X1) | (~sP2(sK9(X0,X1),sK8(X0,X1),X0) & r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK8(X0,X1),X1))) & (! [X4,X5] : (sP2(X5,X4,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP3(X0,X1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f31,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2,X3] : (~sP2(X3,X2,X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (~sP2(sK9(X0,X1),sK8(X0,X1),X0) & r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK8(X0,X1),X1)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP3(X0,X1) | ? [X2,X3] : (~sP2(X3,X2,X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (sP2(X5,X4,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP3(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X1,X0] : ((sP3(X1,X0) | ? [X2,X3] : (~sP2(X3,X2,X1) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & (! [X2,X3] : (sP2(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | ~sP3(X1,X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f15])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (20964)------------------------------
% 0.22/0.52  % (20964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20964)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (20964)Memory used [KB]: 6140
% 0.22/0.52  % (20964)Time elapsed: 0.088 s
% 0.22/0.52  % (20964)------------------------------
% 0.22/0.52  % (20964)------------------------------
% 0.22/0.52  % (20959)Success in time 0.154 s
%------------------------------------------------------------------------------

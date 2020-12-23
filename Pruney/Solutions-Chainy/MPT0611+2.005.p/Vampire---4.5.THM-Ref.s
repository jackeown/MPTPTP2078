%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:34 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 138 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  206 ( 404 expanded)
%              Number of equality atoms :   37 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f681,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f200,f236,f258,f589,f680])).

fof(f680,plain,(
    ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f675])).

fof(f675,plain,
    ( $false
    | ~ spl4_19 ),
    inference(resolution,[],[f666,f33])).

fof(f33,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

fof(f666,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_19 ),
    inference(trivial_inequality_removal,[],[f664])).

fof(f664,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1)
    | ~ spl4_19 ),
    inference(superposition,[],[f48,f199])).

fof(f199,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl4_19
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f589,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | spl4_20 ),
    inference(resolution,[],[f525,f256])).

fof(f256,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl4_20
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f525,plain,(
    ! [X2] : r1_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f523,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
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

% (29223)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (29223)Refutation not found, incomplete strategy% (29223)------------------------------
% (29223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29223)Termination reason: Refutation not found, incomplete strategy

% (29223)Memory used [KB]: 6012
% (29223)Time elapsed: 0.101 s
% (29223)------------------------------
% (29223)------------------------------
fof(f523,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_subsumption,[],[f31,f522])).

fof(f522,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v1_relat_1(sK1) ) ),
    inference(forward_demodulation,[],[f521,f95])).

fof(f95,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(global_subsumption,[],[f31,f92])).

fof(f92,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k10_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(resolution,[],[f45,f80])).

fof(f80,plain,(
    r1_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) ),
    inference(superposition,[],[f48,f69])).

fof(f69,plain,(
    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) ),
    inference(resolution,[],[f58,f32])).

fof(f32,plain,(
    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f49,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k10_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f521,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,k2_relat_1(sK0)))
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f520])).

fof(f520,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,k2_relat_1(sK0)))
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,k2_relat_1(sK0))) ) ),
    inference(resolution,[],[f137,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,sK1),k2_relat_1(sK0))
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(global_subsumption,[],[f31,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | ~ r2_hidden(sK3(X0,X1,sK1),k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f50,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ r2_hidden(X0,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f38,f32])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f258,plain,
    ( spl4_4
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f252,f255,f124])).

fof(f124,plain,
    ( spl4_4
  <=> k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f252,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f107,f119])).

fof(f119,plain,(
    r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    inference(global_subsumption,[],[f31,f34,f117])).

fof(f117,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f37,f57])).

fof(f57,plain,(
    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f49,f32])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(f34,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X1)
      | k1_xboole_0 = X0 ) ),
    inference(factoring,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f236,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f229,f34])).

fof(f229,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_13 ),
    inference(resolution,[],[f176,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f176,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_13
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f200,plain,
    ( spl4_19
    | ~ spl4_13
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f162,f124,f175,f198])).

fof(f162,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f161])).

fof(f161,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(superposition,[],[f36,f125])).

fof(f125,plain,
    ( k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (29231)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (29217)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (29220)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (29221)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (29232)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (29232)Refutation not found, incomplete strategy% (29232)------------------------------
% 0.21/0.50  % (29232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29232)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29232)Memory used [KB]: 1535
% 0.21/0.50  % (29232)Time elapsed: 0.094 s
% 0.21/0.50  % (29232)------------------------------
% 0.21/0.50  % (29232)------------------------------
% 0.21/0.50  % (29237)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (29216)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (29236)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.22/0.51  % (29238)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.22/0.51  % (29229)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.22/0.51  % (29222)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.22/0.51  % (29226)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.22/0.52  % (29228)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.22/0.52  % (29226)Refutation not found, incomplete strategy% (29226)------------------------------
% 1.22/0.52  % (29226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (29226)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (29226)Memory used [KB]: 10490
% 1.22/0.52  % (29226)Time elapsed: 0.101 s
% 1.22/0.52  % (29226)------------------------------
% 1.22/0.52  % (29226)------------------------------
% 1.22/0.52  % (29233)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.22/0.52  % (29224)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.22/0.52  % (29224)Refutation not found, incomplete strategy% (29224)------------------------------
% 1.22/0.52  % (29224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (29224)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (29224)Memory used [KB]: 10490
% 1.22/0.52  % (29224)Time elapsed: 0.114 s
% 1.22/0.52  % (29224)------------------------------
% 1.22/0.52  % (29224)------------------------------
% 1.22/0.52  % (29239)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.22/0.52  % (29230)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.37/0.53  % (29234)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.37/0.53  % (29218)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.37/0.53  % (29227)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.37/0.54  % (29219)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.37/0.54  % (29225)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.37/0.54  % (29219)Refutation not found, incomplete strategy% (29219)------------------------------
% 1.37/0.54  % (29219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (29219)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (29219)Memory used [KB]: 10618
% 1.37/0.54  % (29219)Time elapsed: 0.135 s
% 1.37/0.54  % (29219)------------------------------
% 1.37/0.54  % (29219)------------------------------
% 1.37/0.54  % (29235)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.37/0.55  % (29228)Refutation found. Thanks to Tanya!
% 1.37/0.55  % SZS status Theorem for theBenchmark
% 1.37/0.55  % SZS output start Proof for theBenchmark
% 1.37/0.55  fof(f681,plain,(
% 1.37/0.55    $false),
% 1.37/0.55    inference(avatar_sat_refutation,[],[f200,f236,f258,f589,f680])).
% 1.37/0.55  fof(f680,plain,(
% 1.37/0.55    ~spl4_19),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f675])).
% 1.37/0.55  fof(f675,plain,(
% 1.37/0.55    $false | ~spl4_19),
% 1.37/0.55    inference(resolution,[],[f666,f33])).
% 1.37/0.55  fof(f33,plain,(
% 1.37/0.55    ~r1_xboole_0(sK0,sK1)),
% 1.37/0.55    inference(cnf_transformation,[],[f17])).
% 1.37/0.55  fof(f17,plain,(
% 1.37/0.55    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.37/0.55    inference(flattening,[],[f16])).
% 1.37/0.55  fof(f16,plain,(
% 1.37/0.55    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f14])).
% 1.37/0.55  fof(f14,negated_conjecture,(
% 1.37/0.55    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 1.37/0.55    inference(negated_conjecture,[],[f13])).
% 1.37/0.55  fof(f13,conjecture,(
% 1.37/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).
% 1.37/0.55  fof(f666,plain,(
% 1.37/0.55    r1_xboole_0(sK0,sK1) | ~spl4_19),
% 1.37/0.55    inference(trivial_inequality_removal,[],[f664])).
% 1.37/0.55  fof(f664,plain,(
% 1.37/0.55    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1) | ~spl4_19),
% 1.37/0.55    inference(superposition,[],[f48,f199])).
% 1.37/0.55  fof(f199,plain,(
% 1.37/0.55    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl4_19),
% 1.37/0.55    inference(avatar_component_clause,[],[f198])).
% 1.37/0.55  fof(f198,plain,(
% 1.37/0.55    spl4_19 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.37/0.55  fof(f48,plain,(
% 1.37/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f1])).
% 1.37/0.55  fof(f1,axiom,(
% 1.37/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.37/0.55  fof(f589,plain,(
% 1.37/0.55    spl4_20),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f577])).
% 1.37/0.55  fof(f577,plain,(
% 1.37/0.55    $false | spl4_20),
% 1.37/0.55    inference(resolution,[],[f525,f256])).
% 1.37/0.55  fof(f256,plain,(
% 1.37/0.55    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl4_20),
% 1.37/0.55    inference(avatar_component_clause,[],[f255])).
% 1.37/0.55  fof(f255,plain,(
% 1.37/0.55    spl4_20 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.37/0.55  fof(f525,plain,(
% 1.37/0.55    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2)) )),
% 1.37/0.55    inference(resolution,[],[f523,f39])).
% 1.37/0.55  fof(f39,plain,(
% 1.37/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f21])).
% 1.37/0.55  fof(f21,plain,(
% 1.37/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.37/0.55    inference(ennf_transformation,[],[f15])).
% 1.37/0.55  fof(f15,plain,(
% 1.37/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.37/0.55    inference(rectify,[],[f3])).
% 1.37/0.55  fof(f3,axiom,(
% 1.37/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.37/0.55  % (29223)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.37/0.55  % (29223)Refutation not found, incomplete strategy% (29223)------------------------------
% 1.37/0.55  % (29223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (29223)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (29223)Memory used [KB]: 6012
% 1.37/0.55  % (29223)Time elapsed: 0.101 s
% 1.37/0.55  % (29223)------------------------------
% 1.37/0.55  % (29223)------------------------------
% 1.37/0.56  fof(f523,plain,(
% 1.37/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.37/0.56    inference(global_subsumption,[],[f31,f522])).
% 1.37/0.56  fof(f522,plain,(
% 1.37/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~v1_relat_1(sK1)) )),
% 1.37/0.56    inference(forward_demodulation,[],[f521,f95])).
% 1.37/0.56  fof(f95,plain,(
% 1.37/0.56    k1_xboole_0 = k10_relat_1(sK1,k2_relat_1(sK0))),
% 1.37/0.56    inference(global_subsumption,[],[f31,f92])).
% 1.37/0.56  fof(f92,plain,(
% 1.37/0.56    ~v1_relat_1(sK1) | k1_xboole_0 = k10_relat_1(sK1,k2_relat_1(sK0))),
% 1.37/0.56    inference(resolution,[],[f45,f80])).
% 1.37/0.56  fof(f80,plain,(
% 1.37/0.56    r1_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f78])).
% 1.37/0.56  fof(f78,plain,(
% 1.37/0.56    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))),
% 1.37/0.56    inference(superposition,[],[f48,f69])).
% 1.37/0.56  fof(f69,plain,(
% 1.37/0.56    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))),
% 1.37/0.56    inference(resolution,[],[f58,f32])).
% 1.37/0.56  fof(f32,plain,(
% 1.37/0.56    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.37/0.56    inference(cnf_transformation,[],[f17])).
% 1.37/0.56  fof(f58,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.37/0.56    inference(resolution,[],[f49,f47])).
% 1.37/0.56  fof(f47,plain,(
% 1.37/0.56    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f27])).
% 1.37/0.56  fof(f27,plain,(
% 1.37/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.37/0.56    inference(ennf_transformation,[],[f2])).
% 1.37/0.56  fof(f2,axiom,(
% 1.37/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.37/0.56  fof(f49,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.37/0.56    inference(cnf_transformation,[],[f1])).
% 1.37/0.56  fof(f45,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k10_relat_1(X1,X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f26])).
% 1.37/0.56  fof(f26,plain,(
% 1.37/0.56    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.37/0.56    inference(ennf_transformation,[],[f10])).
% 1.37/0.56  fof(f10,axiom,(
% 1.37/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 1.37/0.56  fof(f521,plain,(
% 1.37/0.56    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,k2_relat_1(sK0))) | ~v1_relat_1(sK1)) )),
% 1.37/0.56    inference(duplicate_literal_removal,[],[f520])).
% 1.37/0.56  fof(f520,plain,(
% 1.37/0.56    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,k2_relat_1(sK0))) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k10_relat_1(sK1,k2_relat_1(sK0)))) )),
% 1.37/0.56    inference(resolution,[],[f137,f52])).
% 1.37/0.56  fof(f52,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.37/0.56    inference(cnf_transformation,[],[f28])).
% 1.37/0.56  fof(f28,plain,(
% 1.37/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.37/0.56    inference(ennf_transformation,[],[f9])).
% 1.37/0.56  fof(f9,axiom,(
% 1.37/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 1.37/0.56  fof(f137,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,sK1),k2_relat_1(sK0)) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 1.37/0.56    inference(global_subsumption,[],[f31,f134])).
% 1.37/0.56  fof(f134,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k10_relat_1(sK1,X1)) | ~r2_hidden(sK3(X0,X1,sK1),k2_relat_1(sK0))) )),
% 1.37/0.56    inference(resolution,[],[f50,f75])).
% 1.37/0.56  fof(f75,plain,(
% 1.37/0.56    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,k2_relat_1(sK0))) )),
% 1.37/0.56    inference(resolution,[],[f38,f32])).
% 1.37/0.56  fof(f38,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f21])).
% 1.37/0.56  fof(f50,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.37/0.56    inference(cnf_transformation,[],[f28])).
% 1.37/0.56  fof(f31,plain,(
% 1.37/0.56    v1_relat_1(sK1)),
% 1.37/0.56    inference(cnf_transformation,[],[f17])).
% 1.37/0.56  fof(f258,plain,(
% 1.37/0.56    spl4_4 | ~spl4_20),
% 1.37/0.56    inference(avatar_split_clause,[],[f252,f255,f124])).
% 1.37/0.56  fof(f124,plain,(
% 1.37/0.56    spl4_4 <=> k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1))),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.37/0.56  fof(f252,plain,(
% 1.37/0.56    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1))),
% 1.37/0.56    inference(resolution,[],[f107,f119])).
% 1.37/0.56  fof(f119,plain,(
% 1.37/0.56    r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 1.37/0.56    inference(global_subsumption,[],[f31,f34,f117])).
% 1.37/0.56  fof(f117,plain,(
% 1.37/0.56    r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 1.37/0.56    inference(superposition,[],[f37,f57])).
% 1.37/0.56  fof(f57,plain,(
% 1.37/0.56    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.37/0.56    inference(resolution,[],[f49,f32])).
% 1.37/0.56  fof(f37,plain,(
% 1.37/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f20])).
% 1.37/0.56  fof(f20,plain,(
% 1.37/0.56    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.37/0.56    inference(ennf_transformation,[],[f11])).
% 1.37/0.56  fof(f11,axiom,(
% 1.37/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).
% 1.37/0.56  fof(f34,plain,(
% 1.37/0.56    v1_relat_1(sK0)),
% 1.37/0.56    inference(cnf_transformation,[],[f17])).
% 1.37/0.56  fof(f107,plain,(
% 1.37/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X1) | k1_xboole_0 = X0) )),
% 1.37/0.56    inference(factoring,[],[f54])).
% 1.37/0.56  fof(f54,plain,(
% 1.37/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0) )),
% 1.37/0.56    inference(cnf_transformation,[],[f30])).
% 1.37/0.56  fof(f30,plain,(
% 1.37/0.56    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.37/0.56    inference(flattening,[],[f29])).
% 1.37/0.56  fof(f29,plain,(
% 1.37/0.56    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.37/0.56    inference(ennf_transformation,[],[f4])).
% 1.37/0.56  fof(f4,axiom,(
% 1.37/0.56    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 1.37/0.56  fof(f236,plain,(
% 1.37/0.56    spl4_13),
% 1.37/0.56    inference(avatar_contradiction_clause,[],[f235])).
% 1.37/0.56  fof(f235,plain,(
% 1.37/0.56    $false | spl4_13),
% 1.37/0.56    inference(resolution,[],[f229,f34])).
% 1.37/0.56  fof(f229,plain,(
% 1.37/0.56    ~v1_relat_1(sK0) | spl4_13),
% 1.37/0.56    inference(resolution,[],[f176,f41])).
% 1.37/0.56  fof(f41,plain,(
% 1.37/0.56    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.37/0.56    inference(cnf_transformation,[],[f22])).
% 1.37/0.56  fof(f22,plain,(
% 1.37/0.56    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.37/0.56    inference(ennf_transformation,[],[f5])).
% 1.37/0.56  fof(f5,axiom,(
% 1.37/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.37/0.56  fof(f176,plain,(
% 1.37/0.56    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl4_13),
% 1.37/0.56    inference(avatar_component_clause,[],[f175])).
% 1.37/0.56  fof(f175,plain,(
% 1.37/0.56    spl4_13 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 1.37/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.37/0.56  fof(f200,plain,(
% 1.37/0.56    spl4_19 | ~spl4_13 | ~spl4_4),
% 1.37/0.56    inference(avatar_split_clause,[],[f162,f124,f175,f198])).
% 1.37/0.56  fof(f162,plain,(
% 1.37/0.56    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl4_4),
% 1.37/0.56    inference(trivial_inequality_removal,[],[f161])).
% 1.37/0.56  fof(f161,plain,(
% 1.37/0.56    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl4_4),
% 1.37/0.56    inference(superposition,[],[f36,f125])).
% 1.37/0.56  fof(f125,plain,(
% 1.37/0.56    k1_xboole_0 = k2_relat_1(k3_xboole_0(sK0,sK1)) | ~spl4_4),
% 1.37/0.56    inference(avatar_component_clause,[],[f124])).
% 1.37/0.56  fof(f36,plain,(
% 1.37/0.56    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.37/0.56    inference(cnf_transformation,[],[f19])).
% 1.37/0.56  fof(f19,plain,(
% 1.37/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.37/0.56    inference(flattening,[],[f18])).
% 1.37/0.56  fof(f18,plain,(
% 1.37/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.37/0.56    inference(ennf_transformation,[],[f12])).
% 1.37/0.56  fof(f12,axiom,(
% 1.37/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.37/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.37/0.56  % SZS output end Proof for theBenchmark
% 1.37/0.56  % (29228)------------------------------
% 1.37/0.56  % (29228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (29228)Termination reason: Refutation
% 1.37/0.56  
% 1.37/0.56  % (29228)Memory used [KB]: 11257
% 1.37/0.56  % (29228)Time elapsed: 0.131 s
% 1.37/0.56  % (29228)------------------------------
% 1.37/0.56  % (29228)------------------------------
% 1.37/0.56  % (29215)Success in time 0.204 s
%------------------------------------------------------------------------------

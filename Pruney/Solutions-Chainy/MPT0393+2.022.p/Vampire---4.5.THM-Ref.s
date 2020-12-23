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
% DateTime   : Thu Dec  3 12:45:54 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 150 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  192 ( 293 expanded)
%              Number of equality atoms :   63 ( 120 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f98,f127,f148,f1064,f1296,f1505,f1573,f2258])).

fof(f2258,plain,
    ( ~ spl5_22
    | spl5_39 ),
    inference(avatar_contradiction_clause,[],[f2238])).

fof(f2238,plain,
    ( $false
    | ~ spl5_22
    | spl5_39 ),
    inference(resolution,[],[f2041,f1572])).

fof(f1572,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0)))
    | spl5_39 ),
    inference(avatar_component_clause,[],[f1570])).

fof(f1570,plain,
    ( spl5_39
  <=> r2_hidden(sK0,k2_enumset1(k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f2041,plain,
    ( ! [X0] : r2_hidden(sK0,k2_enumset1(X0,X0,X0,X0))
    | ~ spl5_22 ),
    inference(resolution,[],[f1518,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f1518,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | r2_hidden(sK0,X1) )
    | ~ spl5_22 ),
    inference(superposition,[],[f58,f628])).

fof(f628,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f626])).

fof(f626,plain,
    ( spl5_22
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1573,plain,
    ( ~ spl5_39
    | spl5_5
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f1507,f626,f124,f1570])).

fof(f124,plain,
    ( spl5_5
  <=> r2_hidden(sK0,k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1507,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0)))
    | spl5_5
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f126,f628])).

fof(f126,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f1505,plain,(
    spl5_37 ),
    inference(avatar_contradiction_clause,[],[f1504])).

fof(f1504,plain,
    ( $false
    | spl5_37 ),
    inference(resolution,[],[f1295,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1295,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_37 ),
    inference(avatar_component_clause,[],[f1293])).

fof(f1293,plain,
    ( spl5_37
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f1296,plain,
    ( spl5_3
    | spl5_22
    | ~ spl5_37
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f1289,f622,f1293,f626,f94])).

fof(f94,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f622,plain,
    ( spl5_21
  <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1289,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl5_21 ),
    inference(superposition,[],[f24,f624])).

fof(f624,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f622])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK1(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f1064,plain,
    ( spl5_22
    | spl5_21
    | spl5_3 ),
    inference(avatar_split_clause,[],[f1063,f94,f622,f626])).

fof(f1063,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl5_3 ),
    inference(duplicate_literal_removal,[],[f1054])).

fof(f1054,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | spl5_3 ),
    inference(resolution,[],[f140,f96])).

fof(f96,plain,
    ( ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f140,plain,(
    ! [X10,X8,X9] :
      ( r1_tarski(X10,k1_setfam_1(k2_enumset1(X9,X9,X9,X8)))
      | sK1(k2_enumset1(X9,X9,X9,X8),X10) = X9
      | k1_xboole_0 = k2_enumset1(X9,X9,X9,X8)
      | sK1(k2_enumset1(X9,X9,X9,X8),X10) = X8 ) ),
    inference(resolution,[],[f77,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f148,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl5_2 ),
    inference(resolution,[],[f142,f92])).

fof(f92,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_2
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f142,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
    inference(resolution,[],[f103,f66])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X1) ) ),
    inference(resolution,[],[f41,f70])).

fof(f70,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f127,plain,
    ( ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f113,f79,f124])).

fof(f79,plain,
    ( spl5_1
  <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f113,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))))
    | spl5_1 ),
    inference(extensionality_resolution,[],[f68,f81])).

fof(f81,plain,
    ( sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f98,plain,
    ( ~ spl5_3
    | ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f86,f79,f90,f94])).

% (22536)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
fof(f86,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl5_1 ),
    inference(extensionality_resolution,[],[f27,f81])).

% (22535)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f82,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f50,f79])).

fof(f50,plain,(
    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f20,f49])).

fof(f20,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:25:51 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.48  % (22506)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (22514)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (22506)Refutation not found, incomplete strategy% (22506)------------------------------
% 0.21/0.50  % (22506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22506)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22506)Memory used [KB]: 10618
% 0.21/0.50  % (22506)Time elapsed: 0.089 s
% 0.21/0.50  % (22506)------------------------------
% 0.21/0.50  % (22506)------------------------------
% 0.21/0.50  % (22514)Refutation not found, incomplete strategy% (22514)------------------------------
% 0.21/0.50  % (22514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22522)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (22514)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22514)Memory used [KB]: 10618
% 0.21/0.51  % (22514)Time elapsed: 0.095 s
% 0.21/0.51  % (22514)------------------------------
% 0.21/0.51  % (22514)------------------------------
% 0.21/0.51  % (22504)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (22520)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (22519)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (22511)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (22510)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (22504)Refutation not found, incomplete strategy% (22504)------------------------------
% 0.21/0.53  % (22504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22504)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22504)Memory used [KB]: 1663
% 0.21/0.53  % (22504)Time elapsed: 0.113 s
% 0.21/0.53  % (22504)------------------------------
% 0.21/0.53  % (22504)------------------------------
% 0.21/0.53  % (22517)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (22525)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (22508)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (22505)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (22509)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (22526)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (22528)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (22527)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (22512)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (22530)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (22512)Refutation not found, incomplete strategy% (22512)------------------------------
% 0.21/0.54  % (22512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22512)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22512)Memory used [KB]: 10618
% 0.21/0.54  % (22512)Time elapsed: 0.112 s
% 0.21/0.54  % (22512)------------------------------
% 0.21/0.54  % (22512)------------------------------
% 0.21/0.55  % (22525)Refutation not found, incomplete strategy% (22525)------------------------------
% 0.21/0.55  % (22525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22525)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22525)Memory used [KB]: 1663
% 0.21/0.55  % (22525)Time elapsed: 0.102 s
% 0.21/0.55  % (22525)------------------------------
% 0.21/0.55  % (22525)------------------------------
% 0.21/0.55  % (22527)Refutation not found, incomplete strategy% (22527)------------------------------
% 0.21/0.55  % (22527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22507)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (22527)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22527)Memory used [KB]: 1791
% 0.21/0.55  % (22527)Time elapsed: 0.116 s
% 0.21/0.55  % (22527)------------------------------
% 0.21/0.55  % (22527)------------------------------
% 0.21/0.55  % (22518)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (22521)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.56  % (22531)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.56  % (22513)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  % (22523)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (22529)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.57  % (22515)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.50/0.57  % (22516)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.62/0.57  % (22524)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.62/0.57  % (22524)Refutation not found, incomplete strategy% (22524)------------------------------
% 1.62/0.57  % (22524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (22524)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.57  
% 1.62/0.57  % (22524)Memory used [KB]: 10618
% 1.62/0.57  % (22524)Time elapsed: 0.160 s
% 1.62/0.57  % (22524)------------------------------
% 1.62/0.57  % (22524)------------------------------
% 1.62/0.58  % (22532)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.62/0.58  % (22533)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.62/0.62  % (22534)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.98/0.63  % (22520)Refutation found. Thanks to Tanya!
% 1.98/0.63  % SZS status Theorem for theBenchmark
% 1.98/0.63  % SZS output start Proof for theBenchmark
% 1.98/0.63  fof(f2260,plain,(
% 1.98/0.63    $false),
% 1.98/0.63    inference(avatar_sat_refutation,[],[f82,f98,f127,f148,f1064,f1296,f1505,f1573,f2258])).
% 1.98/0.63  fof(f2258,plain,(
% 1.98/0.63    ~spl5_22 | spl5_39),
% 1.98/0.63    inference(avatar_contradiction_clause,[],[f2238])).
% 1.98/0.63  fof(f2238,plain,(
% 1.98/0.63    $false | (~spl5_22 | spl5_39)),
% 1.98/0.63    inference(resolution,[],[f2041,f1572])).
% 1.98/0.63  fof(f1572,plain,(
% 1.98/0.63    ~r2_hidden(sK0,k2_enumset1(k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0))) | spl5_39),
% 1.98/0.63    inference(avatar_component_clause,[],[f1570])).
% 1.98/0.63  fof(f1570,plain,(
% 1.98/0.63    spl5_39 <=> r2_hidden(sK0,k2_enumset1(k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0)))),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.98/0.63  fof(f2041,plain,(
% 1.98/0.63    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(X0,X0,X0,X0))) ) | ~spl5_22),
% 1.98/0.63    inference(resolution,[],[f1518,f72])).
% 1.98/0.63  fof(f72,plain,(
% 1.98/0.63    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.98/0.63    inference(equality_resolution,[],[f56])).
% 1.98/0.63  fof(f56,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.98/0.63    inference(definition_unfolding,[],[f36,f49])).
% 1.98/0.63  fof(f49,plain,(
% 1.98/0.63    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.98/0.63    inference(definition_unfolding,[],[f21,f48])).
% 1.98/0.63  fof(f48,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.98/0.63    inference(definition_unfolding,[],[f22,f40])).
% 1.98/0.63  fof(f40,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f7])).
% 1.98/0.63  fof(f7,axiom,(
% 1.98/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.98/0.63  fof(f22,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f6])).
% 1.98/0.63  fof(f6,axiom,(
% 1.98/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.98/0.63  fof(f21,plain,(
% 1.98/0.63    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f5])).
% 1.98/0.63  fof(f5,axiom,(
% 1.98/0.63    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.98/0.63  fof(f36,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f9])).
% 1.98/0.63  fof(f9,axiom,(
% 1.98/0.63    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.98/0.63  fof(f1518,plain,(
% 1.98/0.63    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | r2_hidden(sK0,X1)) ) | ~spl5_22),
% 1.98/0.63    inference(superposition,[],[f58,f628])).
% 1.98/0.63  fof(f628,plain,(
% 1.98/0.63    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_22),
% 1.98/0.63    inference(avatar_component_clause,[],[f626])).
% 1.98/0.63  fof(f626,plain,(
% 1.98/0.63    spl5_22 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.98/0.63  fof(f58,plain,(
% 1.98/0.63    ( ! [X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.98/0.63    inference(definition_unfolding,[],[f39,f49])).
% 1.98/0.63  fof(f39,plain,(
% 1.98/0.63    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f8])).
% 1.98/0.63  fof(f8,axiom,(
% 1.98/0.63    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.98/0.63  fof(f1573,plain,(
% 1.98/0.63    ~spl5_39 | spl5_5 | ~spl5_22),
% 1.98/0.63    inference(avatar_split_clause,[],[f1507,f626,f124,f1570])).
% 1.98/0.63  fof(f124,plain,(
% 1.98/0.63    spl5_5 <=> r2_hidden(sK0,k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))))),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.98/0.63  fof(f1507,plain,(
% 1.98/0.63    ~r2_hidden(sK0,k2_enumset1(k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0),k1_setfam_1(k1_xboole_0))) | (spl5_5 | ~spl5_22)),
% 1.98/0.63    inference(backward_demodulation,[],[f126,f628])).
% 1.98/0.63  fof(f126,plain,(
% 1.98/0.63    ~r2_hidden(sK0,k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))) | spl5_5),
% 1.98/0.63    inference(avatar_component_clause,[],[f124])).
% 1.98/0.63  fof(f1505,plain,(
% 1.98/0.63    spl5_37),
% 1.98/0.63    inference(avatar_contradiction_clause,[],[f1504])).
% 1.98/0.63  fof(f1504,plain,(
% 1.98/0.63    $false | spl5_37),
% 1.98/0.63    inference(resolution,[],[f1295,f66])).
% 1.98/0.63  fof(f66,plain,(
% 1.98/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.98/0.63    inference(equality_resolution,[],[f26])).
% 1.98/0.63  fof(f26,plain,(
% 1.98/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.98/0.63    inference(cnf_transformation,[],[f2])).
% 1.98/0.63  fof(f2,axiom,(
% 1.98/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.98/0.63  fof(f1295,plain,(
% 1.98/0.63    ~r1_tarski(sK0,sK0) | spl5_37),
% 1.98/0.63    inference(avatar_component_clause,[],[f1293])).
% 1.98/0.63  fof(f1293,plain,(
% 1.98/0.63    spl5_37 <=> r1_tarski(sK0,sK0)),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 1.98/0.63  fof(f1296,plain,(
% 1.98/0.63    spl5_3 | spl5_22 | ~spl5_37 | ~spl5_21),
% 1.98/0.63    inference(avatar_split_clause,[],[f1289,f622,f1293,f626,f94])).
% 1.98/0.63  fof(f94,plain,(
% 1.98/0.63    spl5_3 <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.98/0.63  fof(f622,plain,(
% 1.98/0.63    spl5_21 <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.98/0.63  fof(f1289,plain,(
% 1.98/0.63    ~r1_tarski(sK0,sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl5_21),
% 1.98/0.63    inference(superposition,[],[f24,f624])).
% 1.98/0.63  fof(f624,plain,(
% 1.98/0.63    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | ~spl5_21),
% 1.98/0.63    inference(avatar_component_clause,[],[f622])).
% 1.98/0.63  fof(f24,plain,(
% 1.98/0.63    ( ! [X0,X1] : (~r1_tarski(X1,sK1(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f16])).
% 1.98/0.63  fof(f16,plain,(
% 1.98/0.63    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.98/0.63    inference(flattening,[],[f15])).
% 1.98/0.63  fof(f15,plain,(
% 1.98/0.63    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.98/0.63    inference(ennf_transformation,[],[f10])).
% 1.98/0.63  fof(f10,axiom,(
% 1.98/0.63    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 1.98/0.63  fof(f1064,plain,(
% 1.98/0.63    spl5_22 | spl5_21 | spl5_3),
% 1.98/0.63    inference(avatar_split_clause,[],[f1063,f94,f622,f626])).
% 1.98/0.63  fof(f1063,plain,(
% 1.98/0.63    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | spl5_3),
% 1.98/0.63    inference(duplicate_literal_removal,[],[f1054])).
% 1.98/0.63  fof(f1054,plain,(
% 1.98/0.63    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | spl5_3),
% 1.98/0.63    inference(resolution,[],[f140,f96])).
% 1.98/0.63  fof(f96,plain,(
% 1.98/0.63    ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl5_3),
% 1.98/0.63    inference(avatar_component_clause,[],[f94])).
% 1.98/0.63  fof(f140,plain,(
% 1.98/0.63    ( ! [X10,X8,X9] : (r1_tarski(X10,k1_setfam_1(k2_enumset1(X9,X9,X9,X8))) | sK1(k2_enumset1(X9,X9,X9,X8),X10) = X9 | k1_xboole_0 = k2_enumset1(X9,X9,X9,X8) | sK1(k2_enumset1(X9,X9,X9,X8),X10) = X8) )),
% 1.98/0.63    inference(resolution,[],[f77,f23])).
% 1.98/0.63  fof(f23,plain,(
% 1.98/0.63    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f16])).
% 1.98/0.63  fof(f77,plain,(
% 1.98/0.63    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.98/0.63    inference(equality_resolution,[],[f62])).
% 1.98/0.63  fof(f62,plain,(
% 1.98/0.63    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.98/0.63    inference(definition_unfolding,[],[f45,f48])).
% 1.98/0.63  fof(f45,plain,(
% 1.98/0.63    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.98/0.63    inference(cnf_transformation,[],[f4])).
% 1.98/0.63  fof(f4,axiom,(
% 1.98/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.98/0.63  fof(f148,plain,(
% 1.98/0.63    spl5_2),
% 1.98/0.63    inference(avatar_contradiction_clause,[],[f144])).
% 1.98/0.63  fof(f144,plain,(
% 1.98/0.63    $false | spl5_2),
% 1.98/0.63    inference(resolution,[],[f142,f92])).
% 1.98/0.63  fof(f92,plain,(
% 1.98/0.63    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | spl5_2),
% 1.98/0.63    inference(avatar_component_clause,[],[f90])).
% 1.98/0.63  fof(f90,plain,(
% 1.98/0.63    spl5_2 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.98/0.63  fof(f142,plain,(
% 1.98/0.63    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0)) )),
% 1.98/0.63    inference(resolution,[],[f103,f66])).
% 1.98/0.63  fof(f103,plain,(
% 1.98/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X1)) )),
% 1.98/0.63    inference(resolution,[],[f41,f70])).
% 1.98/0.63  fof(f70,plain,(
% 1.98/0.63    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 1.98/0.63    inference(equality_resolution,[],[f69])).
% 1.98/0.63  fof(f69,plain,(
% 1.98/0.63    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 1.98/0.63    inference(equality_resolution,[],[f54])).
% 1.98/0.63  fof(f54,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.98/0.63    inference(definition_unfolding,[],[f31,f49])).
% 1.98/0.63  fof(f31,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.98/0.63    inference(cnf_transformation,[],[f3])).
% 1.98/0.63  fof(f3,axiom,(
% 1.98/0.63    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.98/0.63  fof(f41,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(k1_setfam_1(X1),X2)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f19])).
% 1.98/0.63  fof(f19,plain,(
% 1.98/0.63    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 1.98/0.63    inference(flattening,[],[f18])).
% 1.98/0.63  fof(f18,plain,(
% 1.98/0.63    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 1.98/0.63    inference(ennf_transformation,[],[f11])).
% 1.98/0.63  fof(f11,axiom,(
% 1.98/0.63    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).
% 1.98/0.63  fof(f127,plain,(
% 1.98/0.63    ~spl5_5 | spl5_1),
% 1.98/0.63    inference(avatar_split_clause,[],[f113,f79,f124])).
% 1.98/0.63  fof(f79,plain,(
% 1.98/0.63    spl5_1 <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.98/0.63  fof(f113,plain,(
% 1.98/0.63    ~r2_hidden(sK0,k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))) | spl5_1),
% 1.98/0.63    inference(extensionality_resolution,[],[f68,f81])).
% 1.98/0.63  fof(f81,plain,(
% 1.98/0.63    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_1),
% 1.98/0.63    inference(avatar_component_clause,[],[f79])).
% 1.98/0.63  fof(f68,plain,(
% 1.98/0.63    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 1.98/0.63    inference(equality_resolution,[],[f53])).
% 1.98/0.63  fof(f53,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.98/0.63    inference(definition_unfolding,[],[f32,f49])).
% 1.98/0.63  fof(f32,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.98/0.63    inference(cnf_transformation,[],[f3])).
% 1.98/0.63  fof(f98,plain,(
% 1.98/0.63    ~spl5_3 | ~spl5_2 | spl5_1),
% 1.98/0.63    inference(avatar_split_clause,[],[f86,f79,f90,f94])).
% 1.98/0.63  % (22536)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.98/0.63  fof(f86,plain,(
% 1.98/0.63    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl5_1),
% 1.98/0.63    inference(extensionality_resolution,[],[f27,f81])).
% 1.98/0.63  % (22535)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.98/0.63  fof(f27,plain,(
% 1.98/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.98/0.63    inference(cnf_transformation,[],[f2])).
% 1.98/0.63  fof(f82,plain,(
% 1.98/0.63    ~spl5_1),
% 1.98/0.63    inference(avatar_split_clause,[],[f50,f79])).
% 1.98/0.63  fof(f50,plain,(
% 1.98/0.63    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.98/0.63    inference(definition_unfolding,[],[f20,f49])).
% 1.98/0.63  fof(f20,plain,(
% 1.98/0.63    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 1.98/0.63    inference(cnf_transformation,[],[f14])).
% 1.98/0.63  fof(f14,plain,(
% 1.98/0.63    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 1.98/0.63    inference(ennf_transformation,[],[f13])).
% 1.98/0.63  fof(f13,negated_conjecture,(
% 1.98/0.63    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.98/0.63    inference(negated_conjecture,[],[f12])).
% 1.98/0.63  fof(f12,conjecture,(
% 1.98/0.63    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.98/0.63  % SZS output end Proof for theBenchmark
% 1.98/0.63  % (22520)------------------------------
% 1.98/0.63  % (22520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.63  % (22520)Termination reason: Refutation
% 1.98/0.63  
% 1.98/0.63  % (22520)Memory used [KB]: 12537
% 1.98/0.63  % (22520)Time elapsed: 0.216 s
% 1.98/0.63  % (22520)------------------------------
% 1.98/0.63  % (22520)------------------------------
% 1.98/0.64  % (22534)Refutation not found, incomplete strategy% (22534)------------------------------
% 1.98/0.64  % (22534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.64  % (22503)Success in time 0.266 s
%------------------------------------------------------------------------------

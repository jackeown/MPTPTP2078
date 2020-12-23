%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:51 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 210 expanded)
%              Number of leaves         :   15 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 430 expanded)
%              Number of equality atoms :   62 ( 212 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1549,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f140,f142,f1156,f1325,f1534,f1546])).

fof(f1546,plain,
    ( ~ spl9_87
    | spl9_88 ),
    inference(avatar_contradiction_clause,[],[f1539])).

fof(f1539,plain,
    ( $false
    | ~ spl9_87
    | spl9_88 ),
    inference(unit_resulting_resolution,[],[f18,f19,f59,f1535,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f1535,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ spl9_87
    | spl9_88 ),
    inference(forward_demodulation,[],[f1154,f1151])).

fof(f1151,plain,
    ( k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ spl9_87 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f1149,plain,
    ( spl9_87
  <=> k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f1154,plain,
    ( ~ r2_hidden(sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | spl9_88 ),
    inference(avatar_component_clause,[],[f1153])).

fof(f1153,plain,
    ( spl9_88
  <=> r2_hidden(sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f59,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f55,f46])).

fof(f46,plain,(
    k1_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f20,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f55,plain,(
    ! [X2] : r2_hidden(X2,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k3_enumset1(X2,X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f29,f44])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f1534,plain,
    ( ~ spl9_87
    | ~ spl9_88 ),
    inference(avatar_contradiction_clause,[],[f1521])).

fof(f1521,plain,
    ( $false
    | ~ spl9_87
    | ~ spl9_88 ),
    inference(unit_resulting_resolution,[],[f1155,f45,f1151,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k3_enumset1(X0,X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    k2_relat_1(sK1) != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f21,f44])).

fof(f21,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f1155,plain,
    ( r2_hidden(sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f1153])).

fof(f1325,plain,
    ( ~ spl9_8
    | spl9_87
    | ~ spl9_88 ),
    inference(avatar_contradiction_clause,[],[f1317])).

fof(f1317,plain,
    ( $false
    | ~ spl9_8
    | spl9_87
    | ~ spl9_88 ),
    inference(unit_resulting_resolution,[],[f1155,f1150,f133])).

fof(f133,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,sK0) = X2
        | ~ r2_hidden(X2,k2_relat_1(sK1)) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl9_8
  <=> ! [X2] :
        ( k1_funct_1(sK1,sK0) = X2
        | ~ r2_hidden(X2,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f1150,plain,
    ( k1_funct_1(sK1,sK0) != sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | spl9_87 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f1156,plain,
    ( spl9_87
    | spl9_88 ),
    inference(avatar_split_clause,[],[f1147,f1153,f1149])).

fof(f1147,plain,
    ( r2_hidden(sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(equality_resolution,[],[f806])).

fof(f806,plain,(
    ! [X0] :
      ( k2_relat_1(sK1) != X0
      | r2_hidden(sK5(k1_funct_1(sK1,sK0),X0),X0)
      | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),X0) ) ),
    inference(superposition,[],[f45,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | r2_hidden(sK5(X0,X1),X1)
      | sK5(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f31,f44])).

fof(f31,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f142,plain,(
    spl9_9 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl9_9 ),
    inference(subsumption_resolution,[],[f19,f137])).

fof(f137,plain,
    ( ~ v1_funct_1(sK1)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl9_9
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f140,plain,(
    spl9_7 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl9_7 ),
    inference(subsumption_resolution,[],[f18,f130])).

fof(f130,plain,
    ( ~ v1_relat_1(sK1)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl9_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f138,plain,
    ( ~ spl9_7
    | spl9_8
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f122,f135,f132,f128])).

fof(f122,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK1)
      | k1_funct_1(sK1,sK0) = X2
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X2,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f39,f72])).

fof(f72,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK0,X1),sK1)
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK0,X1),sK1)
      | ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f51,f69])).

fof(f69,plain,(
    ! [X1] :
      ( sK0 = sK3(sK1,X1)
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f66,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(resolution,[],[f51,f57])).

fof(f57,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0 ) ),
    inference(superposition,[],[f53,f46])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f30,f44])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (5074)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (5066)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (5058)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (5064)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (5052)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (5055)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (5065)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (5060)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (5056)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (5071)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (5054)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (5053)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (5051)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (5057)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (5077)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (5063)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (5065)Refutation not found, incomplete strategy% (5065)------------------------------
% 0.21/0.54  % (5065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5065)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5065)Memory used [KB]: 1791
% 0.21/0.54  % (5065)Time elapsed: 0.137 s
% 0.21/0.54  % (5065)------------------------------
% 0.21/0.54  % (5065)------------------------------
% 0.21/0.54  % (5073)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (5076)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (5078)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (5075)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (5080)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (5080)Refutation not found, incomplete strategy% (5080)------------------------------
% 0.21/0.54  % (5080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5080)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5080)Memory used [KB]: 1663
% 0.21/0.54  % (5080)Time elapsed: 0.137 s
% 0.21/0.54  % (5080)------------------------------
% 0.21/0.54  % (5080)------------------------------
% 0.21/0.54  % (5068)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (5062)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (5072)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (5070)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (5067)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (5067)Refutation not found, incomplete strategy% (5067)------------------------------
% 0.21/0.55  % (5067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5067)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5067)Memory used [KB]: 10618
% 0.21/0.55  % (5067)Time elapsed: 0.150 s
% 0.21/0.55  % (5067)------------------------------
% 0.21/0.55  % (5067)------------------------------
% 0.21/0.55  % (5059)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (5069)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (5079)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (5061)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.76/0.60  % (5064)Refutation found. Thanks to Tanya!
% 1.76/0.60  % SZS status Theorem for theBenchmark
% 1.76/0.62  % SZS output start Proof for theBenchmark
% 1.76/0.62  fof(f1549,plain,(
% 1.76/0.62    $false),
% 1.76/0.62    inference(avatar_sat_refutation,[],[f138,f140,f142,f1156,f1325,f1534,f1546])).
% 1.76/0.62  fof(f1546,plain,(
% 1.76/0.62    ~spl9_87 | spl9_88),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f1539])).
% 1.76/0.62  fof(f1539,plain,(
% 1.76/0.62    $false | (~spl9_87 | spl9_88)),
% 1.76/0.62    inference(unit_resulting_resolution,[],[f18,f19,f59,f1535,f24])).
% 1.76/0.62  fof(f24,plain,(
% 1.76/0.62    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f15])).
% 1.76/0.62  fof(f15,plain,(
% 1.76/0.62    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.76/0.62    inference(flattening,[],[f14])).
% 1.76/0.62  fof(f14,plain,(
% 1.76/0.62    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.76/0.62    inference(ennf_transformation,[],[f8])).
% 1.76/0.62  fof(f8,axiom,(
% 1.76/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 1.76/0.62  fof(f1535,plain,(
% 1.76/0.62    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | (~spl9_87 | spl9_88)),
% 1.76/0.62    inference(forward_demodulation,[],[f1154,f1151])).
% 1.76/0.62  fof(f1151,plain,(
% 1.76/0.62    k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~spl9_87),
% 1.76/0.62    inference(avatar_component_clause,[],[f1149])).
% 1.76/0.62  fof(f1149,plain,(
% 1.76/0.62    spl9_87 <=> k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).
% 1.76/0.62  fof(f1154,plain,(
% 1.76/0.62    ~r2_hidden(sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | spl9_88),
% 1.76/0.62    inference(avatar_component_clause,[],[f1153])).
% 1.76/0.62  fof(f1153,plain,(
% 1.76/0.62    spl9_88 <=> r2_hidden(sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).
% 1.76/0.62  fof(f59,plain,(
% 1.76/0.62    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.76/0.62    inference(superposition,[],[f55,f46])).
% 1.76/0.62  fof(f46,plain,(
% 1.76/0.62    k1_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.76/0.62    inference(definition_unfolding,[],[f20,f44])).
% 1.76/0.62  fof(f44,plain,(
% 1.76/0.62    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.76/0.62    inference(definition_unfolding,[],[f22,f43])).
% 1.76/0.62  fof(f43,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.76/0.62    inference(definition_unfolding,[],[f23,f42])).
% 1.76/0.62  fof(f42,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.76/0.62    inference(definition_unfolding,[],[f37,f41])).
% 1.76/0.62  fof(f41,plain,(
% 1.76/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f5])).
% 1.76/0.62  fof(f5,axiom,(
% 1.76/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.76/0.62  fof(f37,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f4])).
% 1.76/0.62  fof(f4,axiom,(
% 1.76/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.76/0.62  fof(f23,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f3])).
% 1.76/0.62  fof(f3,axiom,(
% 1.76/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.76/0.62  fof(f22,plain,(
% 1.76/0.62    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f2])).
% 1.76/0.62  fof(f2,axiom,(
% 1.76/0.62    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.76/0.62  fof(f20,plain,(
% 1.76/0.62    k1_tarski(sK0) = k1_relat_1(sK1)),
% 1.76/0.62    inference(cnf_transformation,[],[f13])).
% 1.76/0.62  fof(f13,plain,(
% 1.76/0.62    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.76/0.62    inference(flattening,[],[f12])).
% 1.76/0.62  fof(f12,plain,(
% 1.76/0.62    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.76/0.62    inference(ennf_transformation,[],[f11])).
% 1.76/0.62  fof(f11,negated_conjecture,(
% 1.76/0.62    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.76/0.62    inference(negated_conjecture,[],[f10])).
% 1.76/0.62  fof(f10,conjecture,(
% 1.76/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.76/0.62  fof(f55,plain,(
% 1.76/0.62    ( ! [X2] : (r2_hidden(X2,k3_enumset1(X2,X2,X2,X2,X2))) )),
% 1.76/0.62    inference(equality_resolution,[],[f54])).
% 1.76/0.62  fof(f54,plain,(
% 1.76/0.62    ( ! [X2,X1] : (r2_hidden(X2,X1) | k3_enumset1(X2,X2,X2,X2,X2) != X1) )),
% 1.76/0.62    inference(equality_resolution,[],[f50])).
% 1.76/0.62  fof(f50,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.76/0.62    inference(definition_unfolding,[],[f29,f44])).
% 1.76/0.62  fof(f29,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.76/0.62    inference(cnf_transformation,[],[f1])).
% 1.76/0.62  fof(f1,axiom,(
% 1.76/0.62    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.76/0.62  fof(f19,plain,(
% 1.76/0.62    v1_funct_1(sK1)),
% 1.76/0.62    inference(cnf_transformation,[],[f13])).
% 1.76/0.62  fof(f18,plain,(
% 1.76/0.62    v1_relat_1(sK1)),
% 1.76/0.62    inference(cnf_transformation,[],[f13])).
% 1.76/0.62  fof(f1534,plain,(
% 1.76/0.62    ~spl9_87 | ~spl9_88),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f1521])).
% 1.76/0.62  fof(f1521,plain,(
% 1.76/0.62    $false | (~spl9_87 | ~spl9_88)),
% 1.76/0.62    inference(unit_resulting_resolution,[],[f1155,f45,f1151,f47])).
% 1.76/0.62  fof(f47,plain,(
% 1.76/0.62    ( ! [X0,X1] : (sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1) | k3_enumset1(X0,X0,X0,X0,X0) = X1) )),
% 1.76/0.62    inference(definition_unfolding,[],[f32,f44])).
% 1.76/0.62  fof(f32,plain,(
% 1.76/0.62    ( ! [X0,X1] : (sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 1.76/0.62    inference(cnf_transformation,[],[f1])).
% 1.76/0.62  fof(f45,plain,(
% 1.76/0.62    k2_relat_1(sK1) != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.76/0.62    inference(definition_unfolding,[],[f21,f44])).
% 1.76/0.62  fof(f21,plain,(
% 1.76/0.62    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.76/0.62    inference(cnf_transformation,[],[f13])).
% 1.76/0.62  fof(f1155,plain,(
% 1.76/0.62    r2_hidden(sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | ~spl9_88),
% 1.76/0.62    inference(avatar_component_clause,[],[f1153])).
% 1.76/0.62  fof(f1325,plain,(
% 1.76/0.62    ~spl9_8 | spl9_87 | ~spl9_88),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f1317])).
% 1.76/0.62  fof(f1317,plain,(
% 1.76/0.62    $false | (~spl9_8 | spl9_87 | ~spl9_88)),
% 1.76/0.62    inference(unit_resulting_resolution,[],[f1155,f1150,f133])).
% 1.76/0.62  fof(f133,plain,(
% 1.76/0.62    ( ! [X2] : (k1_funct_1(sK1,sK0) = X2 | ~r2_hidden(X2,k2_relat_1(sK1))) ) | ~spl9_8),
% 1.76/0.62    inference(avatar_component_clause,[],[f132])).
% 1.76/0.62  fof(f132,plain,(
% 1.76/0.62    spl9_8 <=> ! [X2] : (k1_funct_1(sK1,sK0) = X2 | ~r2_hidden(X2,k2_relat_1(sK1)))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.76/0.62  fof(f1150,plain,(
% 1.76/0.62    k1_funct_1(sK1,sK0) != sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | spl9_87),
% 1.76/0.62    inference(avatar_component_clause,[],[f1149])).
% 1.76/0.62  fof(f1156,plain,(
% 1.76/0.62    spl9_87 | spl9_88),
% 1.76/0.62    inference(avatar_split_clause,[],[f1147,f1153,f1149])).
% 1.76/0.62  fof(f1147,plain,(
% 1.76/0.62    r2_hidden(sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 1.76/0.62    inference(equality_resolution,[],[f806])).
% 1.76/0.62  fof(f806,plain,(
% 1.76/0.62    ( ! [X0] : (k2_relat_1(sK1) != X0 | r2_hidden(sK5(k1_funct_1(sK1,sK0),X0),X0) | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),X0)) )),
% 1.76/0.62    inference(superposition,[],[f45,f48])).
% 1.76/0.62  fof(f48,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | r2_hidden(sK5(X0,X1),X1) | sK5(X0,X1) = X0) )),
% 1.76/0.62    inference(definition_unfolding,[],[f31,f44])).
% 1.76/0.62  fof(f31,plain,(
% 1.76/0.62    ( ! [X0,X1] : (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 1.76/0.62    inference(cnf_transformation,[],[f1])).
% 1.76/0.62  fof(f142,plain,(
% 1.76/0.62    spl9_9),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f141])).
% 1.76/0.62  fof(f141,plain,(
% 1.76/0.62    $false | spl9_9),
% 1.76/0.62    inference(subsumption_resolution,[],[f19,f137])).
% 1.76/0.62  fof(f137,plain,(
% 1.76/0.62    ~v1_funct_1(sK1) | spl9_9),
% 1.76/0.62    inference(avatar_component_clause,[],[f135])).
% 1.76/0.62  fof(f135,plain,(
% 1.76/0.62    spl9_9 <=> v1_funct_1(sK1)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.76/0.62  fof(f140,plain,(
% 1.76/0.62    spl9_7),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f139])).
% 1.76/0.62  fof(f139,plain,(
% 1.76/0.62    $false | spl9_7),
% 1.76/0.62    inference(subsumption_resolution,[],[f18,f130])).
% 1.76/0.62  fof(f130,plain,(
% 1.76/0.62    ~v1_relat_1(sK1) | spl9_7),
% 1.76/0.62    inference(avatar_component_clause,[],[f128])).
% 1.76/0.62  fof(f128,plain,(
% 1.76/0.62    spl9_7 <=> v1_relat_1(sK1)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.76/0.62  fof(f138,plain,(
% 1.76/0.62    ~spl9_7 | spl9_8 | ~spl9_9),
% 1.76/0.62    inference(avatar_split_clause,[],[f122,f135,f132,f128])).
% 1.76/0.62  fof(f122,plain,(
% 1.76/0.62    ( ! [X2] : (~v1_funct_1(sK1) | k1_funct_1(sK1,sK0) = X2 | ~v1_relat_1(sK1) | ~r2_hidden(X2,k2_relat_1(sK1))) )),
% 1.76/0.62    inference(resolution,[],[f39,f72])).
% 1.76/0.62  fof(f72,plain,(
% 1.76/0.62    ( ! [X1] : (r2_hidden(k4_tarski(sK0,X1),sK1) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 1.76/0.62    inference(duplicate_literal_removal,[],[f71])).
% 1.76/0.62  fof(f71,plain,(
% 1.76/0.62    ( ! [X1] : (r2_hidden(k4_tarski(sK0,X1),sK1) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 1.76/0.62    inference(superposition,[],[f51,f69])).
% 1.76/0.62  fof(f69,plain,(
% 1.76/0.62    ( ! [X1] : (sK0 = sK3(sK1,X1) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 1.76/0.62    inference(resolution,[],[f66,f62])).
% 1.76/0.62  fof(f62,plain,(
% 1.76/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X1,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 1.76/0.62    inference(resolution,[],[f51,f57])).
% 1.76/0.62  fof(f57,plain,(
% 1.76/0.62    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 1.76/0.62    inference(equality_resolution,[],[f33])).
% 1.76/0.62  fof(f33,plain,(
% 1.76/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.76/0.62    inference(cnf_transformation,[],[f6])).
% 1.76/0.62  fof(f6,axiom,(
% 1.76/0.62    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.76/0.62  fof(f66,plain,(
% 1.76/0.62    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0) )),
% 1.76/0.62    inference(superposition,[],[f53,f46])).
% 1.76/0.62  fof(f53,plain,(
% 1.76/0.62    ( ! [X2,X0] : (~r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X2) )),
% 1.76/0.62    inference(equality_resolution,[],[f49])).
% 1.76/0.62  fof(f49,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.76/0.62    inference(definition_unfolding,[],[f30,f44])).
% 1.76/0.62  fof(f30,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.76/0.62    inference(cnf_transformation,[],[f1])).
% 1.76/0.62  fof(f51,plain,(
% 1.76/0.62    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.76/0.62    inference(equality_resolution,[],[f26])).
% 1.76/0.62  fof(f26,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.76/0.62    inference(cnf_transformation,[],[f7])).
% 1.76/0.62  fof(f7,axiom,(
% 1.76/0.62    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.76/0.62  fof(f39,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f17])).
% 1.76/0.62  fof(f17,plain,(
% 1.76/0.62    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.76/0.62    inference(flattening,[],[f16])).
% 1.76/0.62  fof(f16,plain,(
% 1.76/0.62    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.76/0.62    inference(ennf_transformation,[],[f9])).
% 1.76/0.62  fof(f9,axiom,(
% 1.76/0.62    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.76/0.62  % SZS output end Proof for theBenchmark
% 1.76/0.62  % (5064)------------------------------
% 1.76/0.62  % (5064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.62  % (5064)Termination reason: Refutation
% 1.76/0.62  
% 1.76/0.62  % (5064)Memory used [KB]: 7036
% 1.76/0.62  % (5064)Time elapsed: 0.200 s
% 1.76/0.62  % (5064)------------------------------
% 1.76/0.62  % (5064)------------------------------
% 1.76/0.62  % (5050)Success in time 0.259 s
%------------------------------------------------------------------------------

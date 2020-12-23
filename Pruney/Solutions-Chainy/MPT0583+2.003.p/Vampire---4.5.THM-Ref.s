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
% DateTime   : Thu Dec  3 12:50:51 EST 2020

% Result     : Theorem 0.10s
% Output     : Refutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 790 expanded)
%              Number of leaves         :   29 ( 243 expanded)
%              Depth                    :   21
%              Number of atoms          :  252 (1248 expanded)
%              Number of equality atoms :   94 ( 560 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2339,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f537,f717,f1486,f1744,f1874,f2338])).

fof(f2338,plain,
    ( spl3_2
    | ~ spl3_1
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f2337,f1871,f86,f91])).

% (23390)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% (23391)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
fof(f91,plain,
    ( spl3_2
  <=> k1_xboole_0 = k7_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f86,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1871,plain,
    ( spl3_35
  <=> k1_xboole_0 = k9_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f2337,plain,
    ( k1_xboole_0 = k7_relat_1(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_35 ),
    inference(trivial_inequality_removal,[],[f2336])).

fof(f2336,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_35 ),
    inference(superposition,[],[f2311,f1873])).

fof(f1873,plain,
    ( k1_xboole_0 = k9_relat_1(sK0,sK1)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f1871])).

fof(f2311,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK0,X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl3_1 ),
    inference(superposition,[],[f124,f136])).

fof(f136,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl3_1 ),
    inference(resolution,[],[f54,f88])).

fof(f88,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f124,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(k7_relat_1(sK0,X0))
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f46,f100])).

fof(f100,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK0,X0))
    | ~ spl3_1 ),
    inference(resolution,[],[f53,f88])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1874,plain,
    ( spl3_35
    | ~ spl3_1
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f1867,f1741,f86,f1871])).

fof(f1741,plain,
    ( spl3_34
  <=> r1_xboole_0(k1_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f1867,plain,
    ( ~ v1_relat_1(sK0)
    | k1_xboole_0 = k9_relat_1(sK0,sK1)
    | ~ spl3_34 ),
    inference(resolution,[],[f1743,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f1743,plain,
    ( r1_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f1741])).

fof(f1744,plain,
    ( spl3_34
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f1738,f1483,f96,f1741])).

fof(f96,plain,
    ( spl3_3
  <=> r1_xboole_0(sK1,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1483,plain,
    ( spl3_26
  <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK1,k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1738,plain,
    ( r1_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(resolution,[],[f1729,f104])).

fof(f104,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f60,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1729,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,k1_relat_1(sK0))
        | r1_xboole_0(X4,sK1) )
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f1728,f80])).

fof(f80,plain,(
    ! [X0,X1] : k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f47,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f1728,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,k1_relat_1(sK0))
        | r1_xboole_0(X4,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k2_xboole_0(sK1,k1_relat_1(sK0))))) )
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f1727,f355])).

fof(f355,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(forward_demodulation,[],[f354,f142])).

fof(f142,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f140,f105])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f61,f104])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f140,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(resolution,[],[f57,f104])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f354,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = k2_xboole_0(X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f353,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f353,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = k2_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f349,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f349,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(k1_xboole_0,X2),X2)) ),
    inference(resolution,[],[f308,f57])).

fof(f308,plain,(
    ! [X3] : r1_tarski(X3,k2_xboole_0(k1_xboole_0,X3)) ),
    inference(resolution,[],[f280,f154])).

fof(f154,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[],[f150,f141])).

fof(f141,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(resolution,[],[f57,f107])).

fof(f107,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f62,f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f150,plain,(
    ! [X2,X3] : r1_tarski(k2_xboole_0(k1_xboole_0,X2),k2_xboole_0(X3,X2)) ),
    inference(resolution,[],[f64,f107])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f280,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(backward_demodulation,[],[f84,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))))
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f65,f75])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f74])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f1727,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,k2_xboole_0(k1_xboole_0,k1_relat_1(sK0)))
        | r1_xboole_0(X4,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k2_xboole_0(sK1,k1_relat_1(sK0))))) )
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f1726,f105])).

fof(f1726,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,k2_xboole_0(k4_xboole_0(sK1,sK1),k1_relat_1(sK0)))
        | r1_xboole_0(X4,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k2_xboole_0(sK1,k1_relat_1(sK0))))) )
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f1725,f200])).

fof(f200,plain,
    ( ! [X0] : k2_xboole_0(k4_xboole_0(X0,sK1),k1_relat_1(sK0)) = k4_xboole_0(k2_xboole_0(X0,k1_relat_1(sK0)),sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f63,f98])).

fof(f98,plain,
    ( r1_xboole_0(sK1,k1_relat_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f1725,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,k4_xboole_0(k2_xboole_0(sK1,k1_relat_1(sK0)),sK1))
        | r1_xboole_0(X4,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k2_xboole_0(sK1,k1_relat_1(sK0))))) )
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f1674,f355])).

fof(f1674,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK1,k1_relat_1(sK0)),sK1)))
        | r1_xboole_0(X4,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k2_xboole_0(sK1,k1_relat_1(sK0))))) )
    | ~ spl3_26 ),
    inference(superposition,[],[f367,f1485])).

fof(f1485,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK1,k1_relat_1(sK0)))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f1483])).

fof(f367,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))
      | r1_xboole_0(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ) ),
    inference(forward_demodulation,[],[f83,f81])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,k4_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) ) ),
    inference(definition_unfolding,[],[f66,f74,f75])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1486,plain,
    ( spl3_26
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f1444,f714,f1483])).

fof(f714,plain,
    ( spl3_8
  <=> k2_xboole_0(k1_relat_1(sK0),sK1) = k2_xboole_0(sK1,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f1444,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK1,k1_relat_1(sK0)))
    | ~ spl3_8 ),
    inference(superposition,[],[f371,f716])).

fof(f716,plain,
    ( k2_xboole_0(k1_relat_1(sK0),sK1) = k2_xboole_0(sK1,k1_relat_1(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f714])).

fof(f371,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(backward_demodulation,[],[f153,f355])).

fof(f153,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X5),k2_xboole_0(X6,X5)) ),
    inference(resolution,[],[f150,f61])).

fof(f717,plain,
    ( spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f691,f534,f714])).

fof(f534,plain,
    ( spl3_7
  <=> k1_relat_1(sK0) = k4_xboole_0(k1_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f691,plain,
    ( k2_xboole_0(k1_relat_1(sK0),sK1) = k2_xboole_0(sK1,k1_relat_1(sK0))
    | ~ spl3_7 ),
    inference(superposition,[],[f440,f536])).

fof(f536,plain,
    ( k1_relat_1(sK0) = k4_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f534])).

fof(f440,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k2_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f435,f49])).

fof(f435,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k2_xboole_0(X7,k4_xboole_0(k2_xboole_0(X8,X7),X7)) ),
    inference(resolution,[],[f372,f57])).

fof(f372,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    inference(backward_demodulation,[],[f150,f355])).

fof(f537,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f532,f96,f534])).

fof(f532,plain,
    ( k1_relat_1(sK0) = k4_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f531,f355])).

fof(f531,plain,
    ( k2_xboole_0(k1_xboole_0,k1_relat_1(sK0)) = k4_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f524,f40])).

fof(f524,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,sK1),k1_relat_1(sK0)) = k4_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f200,f355])).

fof(f99,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f96])).

fof(f37,plain,(
    r1_xboole_0(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(X0,X1)
          & r1_xboole_0(X1,k1_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r1_xboole_0(X1,k1_relat_1(X0))
           => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f94,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f38,f91])).

fof(f38,plain,(
    k1_xboole_0 != k7_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.07  % Command    : run_vampire %s %d
% 0.06/0.25  % Computer   : n004.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 12:51:53 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.10/0.38  % (23370)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.10/0.39  % (23360)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.10/0.39  % (23362)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.10/0.39  % (23357)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.10/0.39  % (23361)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.10/0.40  % (23359)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.10/0.40  % (23358)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.10/0.41  % (23381)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.10/0.41  % (23383)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.10/0.41  % (23380)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.10/0.41  % (23385)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.10/0.41  % (23374)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.10/0.41  % (23376)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.10/0.42  % (23374)Refutation not found, incomplete strategy% (23374)------------------------------
% 0.10/0.42  % (23374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.42  % (23374)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.42  
% 0.10/0.42  % (23374)Memory used [KB]: 10618
% 0.10/0.42  % (23374)Time elapsed: 0.117 s
% 0.10/0.42  % (23374)------------------------------
% 0.10/0.42  % (23374)------------------------------
% 0.10/0.42  % (23372)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.10/0.42  % (23379)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.10/0.42  % (23382)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.10/0.42  % (23379)Refutation not found, incomplete strategy% (23379)------------------------------
% 0.10/0.42  % (23379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.42  % (23379)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.42  
% 0.10/0.42  % (23379)Memory used [KB]: 10746
% 0.10/0.42  % (23379)Time elapsed: 0.081 s
% 0.10/0.42  % (23379)------------------------------
% 0.10/0.42  % (23379)------------------------------
% 0.10/0.42  % (23386)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.10/0.42  % (23373)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.10/0.43  % (23364)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.10/0.43  % (23368)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.10/0.43  % (23378)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.10/0.43  % (23378)Refutation not found, incomplete strategy% (23378)------------------------------
% 0.10/0.43  % (23378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.43  % (23378)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.43  
% 0.10/0.43  % (23378)Memory used [KB]: 1791
% 0.10/0.43  % (23378)Time elapsed: 0.126 s
% 0.10/0.43  % (23378)------------------------------
% 0.10/0.43  % (23378)------------------------------
% 0.10/0.43  % (23366)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.10/0.43  % (23363)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.10/0.43  % (23365)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.10/0.43  % (23369)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.10/0.43  % (23377)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.10/0.43  % (23377)Refutation not found, incomplete strategy% (23377)------------------------------
% 0.10/0.43  % (23377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.43  % (23377)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.43  
% 0.10/0.43  % (23377)Memory used [KB]: 10746
% 0.10/0.43  % (23377)Time elapsed: 0.093 s
% 0.10/0.43  % (23377)------------------------------
% 0.10/0.43  % (23377)------------------------------
% 0.10/0.44  % (23375)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.10/0.45  % (23367)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.10/0.45  % (23384)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.10/0.46  % (23371)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.10/0.54  % (23373)Refutation found. Thanks to Tanya!
% 0.10/0.54  % SZS status Theorem for theBenchmark
% 0.10/0.54  % SZS output start Proof for theBenchmark
% 0.10/0.54  fof(f2339,plain,(
% 0.10/0.54    $false),
% 0.10/0.54    inference(avatar_sat_refutation,[],[f89,f94,f99,f537,f717,f1486,f1744,f1874,f2338])).
% 0.10/0.54  fof(f2338,plain,(
% 0.10/0.54    spl3_2 | ~spl3_1 | ~spl3_35),
% 0.10/0.54    inference(avatar_split_clause,[],[f2337,f1871,f86,f91])).
% 0.10/0.55  % (23390)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 0.10/0.55  % (23391)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 0.10/0.56  fof(f91,plain,(
% 0.10/0.56    spl3_2 <=> k1_xboole_0 = k7_relat_1(sK0,sK1)),
% 0.10/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.10/0.56  fof(f86,plain,(
% 0.10/0.56    spl3_1 <=> v1_relat_1(sK0)),
% 0.10/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.10/0.56  fof(f1871,plain,(
% 0.10/0.56    spl3_35 <=> k1_xboole_0 = k9_relat_1(sK0,sK1)),
% 0.10/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.10/0.56  fof(f2337,plain,(
% 0.10/0.56    k1_xboole_0 = k7_relat_1(sK0,sK1) | (~spl3_1 | ~spl3_35)),
% 0.10/0.56    inference(trivial_inequality_removal,[],[f2336])).
% 0.10/0.56  fof(f2336,plain,(
% 0.10/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK0,sK1) | (~spl3_1 | ~spl3_35)),
% 0.10/0.56    inference(superposition,[],[f2311,f1873])).
% 0.10/0.56  fof(f1873,plain,(
% 0.10/0.56    k1_xboole_0 = k9_relat_1(sK0,sK1) | ~spl3_35),
% 0.10/0.56    inference(avatar_component_clause,[],[f1871])).
% 0.10/0.56  fof(f2311,plain,(
% 0.10/0.56    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK0,X0) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | ~spl3_1),
% 0.10/0.56    inference(superposition,[],[f124,f136])).
% 0.10/0.56  fof(f136,plain,(
% 0.10/0.56    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | ~spl3_1),
% 0.10/0.56    inference(resolution,[],[f54,f88])).
% 0.10/0.56  fof(f88,plain,(
% 0.10/0.56    v1_relat_1(sK0) | ~spl3_1),
% 0.10/0.56    inference(avatar_component_clause,[],[f86])).
% 0.10/0.56  fof(f54,plain,(
% 0.10/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.10/0.56    inference(cnf_transformation,[],[f31])).
% 0.10/0.56  fof(f31,plain,(
% 0.10/0.56    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.10/0.56    inference(ennf_transformation,[],[f22])).
% 0.10/0.56  fof(f22,axiom,(
% 0.10/0.56    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.10/0.56  fof(f124,plain,(
% 0.10/0.56    ( ! [X0] : (k1_xboole_0 != k2_relat_1(k7_relat_1(sK0,X0)) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | ~spl3_1),
% 0.10/0.56    inference(resolution,[],[f46,f100])).
% 0.10/0.56  fof(f100,plain,(
% 0.10/0.56    ( ! [X0] : (v1_relat_1(k7_relat_1(sK0,X0))) ) | ~spl3_1),
% 0.10/0.56    inference(resolution,[],[f53,f88])).
% 0.10/0.56  fof(f53,plain,(
% 0.10/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.10/0.56    inference(cnf_transformation,[],[f30])).
% 0.10/0.56  fof(f30,plain,(
% 0.10/0.56    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.10/0.56    inference(ennf_transformation,[],[f21])).
% 0.10/0.56  fof(f21,axiom,(
% 0.10/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.10/0.56  fof(f46,plain,(
% 0.10/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.10/0.56    inference(cnf_transformation,[],[f29])).
% 0.10/0.56  fof(f29,plain,(
% 0.10/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.10/0.56    inference(flattening,[],[f28])).
% 0.10/0.56  fof(f28,plain,(
% 0.10/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.10/0.56    inference(ennf_transformation,[],[f24])).
% 0.10/0.56  fof(f24,axiom,(
% 0.10/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.10/0.56  fof(f1874,plain,(
% 0.10/0.56    spl3_35 | ~spl3_1 | ~spl3_34),
% 0.10/0.56    inference(avatar_split_clause,[],[f1867,f1741,f86,f1871])).
% 0.10/0.56  fof(f1741,plain,(
% 0.10/0.56    spl3_34 <=> r1_xboole_0(k1_relat_1(sK0),sK1)),
% 0.10/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.10/0.56  fof(f1867,plain,(
% 0.10/0.56    ~v1_relat_1(sK0) | k1_xboole_0 = k9_relat_1(sK0,sK1) | ~spl3_34),
% 0.10/0.56    inference(resolution,[],[f1743,f55])).
% 0.10/0.56  fof(f55,plain,(
% 0.10/0.56    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k9_relat_1(X1,X0)) )),
% 0.10/0.56    inference(cnf_transformation,[],[f32])).
% 0.10/0.56  fof(f32,plain,(
% 0.10/0.56    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.10/0.56    inference(ennf_transformation,[],[f23])).
% 0.10/0.56  fof(f23,axiom,(
% 0.10/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.10/0.56  fof(f1743,plain,(
% 0.10/0.56    r1_xboole_0(k1_relat_1(sK0),sK1) | ~spl3_34),
% 0.10/0.56    inference(avatar_component_clause,[],[f1741])).
% 0.10/0.56  fof(f1744,plain,(
% 0.10/0.56    spl3_34 | ~spl3_3 | ~spl3_26),
% 0.10/0.56    inference(avatar_split_clause,[],[f1738,f1483,f96,f1741])).
% 0.10/0.56  fof(f96,plain,(
% 0.10/0.56    spl3_3 <=> r1_xboole_0(sK1,k1_relat_1(sK0))),
% 0.10/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.10/0.56  fof(f1483,plain,(
% 0.10/0.56    spl3_26 <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK1,k1_relat_1(sK0)))),
% 0.10/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.10/0.56  fof(f1738,plain,(
% 0.10/0.56    r1_xboole_0(k1_relat_1(sK0),sK1) | (~spl3_3 | ~spl3_26)),
% 0.10/0.56    inference(resolution,[],[f1729,f104])).
% 0.10/0.56  fof(f104,plain,(
% 0.10/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.10/0.56    inference(duplicate_literal_removal,[],[f103])).
% 0.10/0.56  fof(f103,plain,(
% 0.10/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.10/0.56    inference(resolution,[],[f60,f59])).
% 0.10/0.56  fof(f59,plain,(
% 0.10/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.10/0.56    inference(cnf_transformation,[],[f34])).
% 0.10/0.56  fof(f34,plain,(
% 0.10/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.10/0.56    inference(ennf_transformation,[],[f1])).
% 0.10/0.56  fof(f1,axiom,(
% 0.10/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.10/0.56  fof(f60,plain,(
% 0.10/0.56    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.10/0.56    inference(cnf_transformation,[],[f34])).
% 0.10/0.56  fof(f1729,plain,(
% 0.10/0.56    ( ! [X4] : (~r1_tarski(X4,k1_relat_1(sK0)) | r1_xboole_0(X4,sK1)) ) | (~spl3_3 | ~spl3_26)),
% 0.10/0.56    inference(forward_demodulation,[],[f1728,f80])).
% 0.10/0.56  fof(f80,plain,(
% 0.10/0.56    ( ! [X0,X1] : (k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.10/0.56    inference(definition_unfolding,[],[f47,f74])).
% 0.10/0.56  fof(f74,plain,(
% 0.10/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.10/0.56    inference(definition_unfolding,[],[f48,f73])).
% 0.10/0.56  fof(f73,plain,(
% 0.10/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.10/0.56    inference(definition_unfolding,[],[f50,f72])).
% 0.10/0.56  fof(f72,plain,(
% 0.10/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.10/0.56    inference(definition_unfolding,[],[f68,f71])).
% 0.10/0.56  fof(f71,plain,(
% 0.10/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.10/0.56    inference(definition_unfolding,[],[f69,f70])).
% 0.10/0.56  fof(f70,plain,(
% 0.10/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.10/0.56    inference(cnf_transformation,[],[f16])).
% 0.10/0.56  fof(f16,axiom,(
% 0.10/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.10/0.56  fof(f69,plain,(
% 0.10/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.10/0.56    inference(cnf_transformation,[],[f15])).
% 0.10/0.56  fof(f15,axiom,(
% 0.10/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.10/0.56  fof(f68,plain,(
% 0.10/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.10/0.56    inference(cnf_transformation,[],[f14])).
% 0.10/0.56  fof(f14,axiom,(
% 0.10/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.10/0.56  fof(f50,plain,(
% 0.10/0.56    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.10/0.56    inference(cnf_transformation,[],[f17])).
% 0.10/0.56  fof(f17,axiom,(
% 0.10/0.56    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.10/0.56  fof(f48,plain,(
% 0.10/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.10/0.56    inference(cnf_transformation,[],[f20])).
% 0.10/0.56  fof(f20,axiom,(
% 0.10/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.10/0.56  fof(f47,plain,(
% 0.10/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.10/0.56    inference(cnf_transformation,[],[f4])).
% 0.10/0.56  fof(f4,axiom,(
% 0.10/0.56    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.10/0.56  fof(f1728,plain,(
% 0.10/0.56    ( ! [X4] : (~r1_tarski(X4,k1_relat_1(sK0)) | r1_xboole_0(X4,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k2_xboole_0(sK1,k1_relat_1(sK0)))))) ) | (~spl3_3 | ~spl3_26)),
% 0.10/0.56    inference(forward_demodulation,[],[f1727,f355])).
% 0.10/0.56  fof(f355,plain,(
% 0.10/0.56    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) )),
% 0.10/0.56    inference(forward_demodulation,[],[f354,f142])).
% 0.10/0.56  fof(f142,plain,(
% 0.10/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.10/0.56    inference(forward_demodulation,[],[f140,f105])).
% 0.10/0.56  fof(f105,plain,(
% 0.10/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.10/0.56    inference(resolution,[],[f61,f104])).
% 0.10/0.56  fof(f61,plain,(
% 0.10/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.10/0.56    inference(cnf_transformation,[],[f5])).
% 0.10/0.56  fof(f5,axiom,(
% 0.10/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.10/0.56  fof(f140,plain,(
% 0.10/0.56    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.10/0.56    inference(resolution,[],[f57,f104])).
% 0.10/0.56  fof(f57,plain,(
% 0.10/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.10/0.56    inference(cnf_transformation,[],[f33])).
% 0.10/0.56  fof(f33,plain,(
% 0.10/0.56    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.10/0.56    inference(ennf_transformation,[],[f7])).
% 0.10/0.56  fof(f7,axiom,(
% 0.10/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.10/0.56  fof(f354,plain,(
% 0.10/0.56    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = k2_xboole_0(X2,k1_xboole_0)) )),
% 0.10/0.56    inference(forward_demodulation,[],[f353,f40])).
% 0.10/0.56  fof(f40,plain,(
% 0.10/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.10/0.56    inference(cnf_transformation,[],[f8])).
% 0.10/0.56  fof(f8,axiom,(
% 0.10/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.10/0.56  fof(f353,plain,(
% 0.10/0.56    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = k2_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2))) )),
% 0.10/0.56    inference(forward_demodulation,[],[f349,f49])).
% 0.10/0.56  fof(f49,plain,(
% 0.10/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.10/0.56    inference(cnf_transformation,[],[f6])).
% 0.10/0.56  fof(f6,axiom,(
% 0.10/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.10/0.56  fof(f349,plain,(
% 0.10/0.56    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(k1_xboole_0,X2),X2))) )),
% 0.10/0.56    inference(resolution,[],[f308,f57])).
% 0.10/0.56  fof(f308,plain,(
% 0.10/0.56    ( ! [X3] : (r1_tarski(X3,k2_xboole_0(k1_xboole_0,X3))) )),
% 0.10/0.56    inference(resolution,[],[f280,f154])).
% 0.10/0.56  fof(f154,plain,(
% 0.10/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)))) )),
% 0.10/0.56    inference(superposition,[],[f150,f141])).
% 0.10/0.56  fof(f141,plain,(
% 0.10/0.56    ( ! [X1] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = X1) )),
% 0.10/0.56    inference(resolution,[],[f57,f107])).
% 0.10/0.56  fof(f107,plain,(
% 0.10/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.10/0.56    inference(trivial_inequality_removal,[],[f106])).
% 0.10/0.56  fof(f106,plain,(
% 0.10/0.56    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) )),
% 0.10/0.56    inference(superposition,[],[f62,f40])).
% 0.10/0.56  fof(f62,plain,(
% 0.10/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.10/0.56    inference(cnf_transformation,[],[f5])).
% 0.10/0.56  fof(f150,plain,(
% 0.10/0.56    ( ! [X2,X3] : (r1_tarski(k2_xboole_0(k1_xboole_0,X2),k2_xboole_0(X3,X2))) )),
% 0.10/0.56    inference(resolution,[],[f64,f107])).
% 0.10/0.56  fof(f64,plain,(
% 0.10/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 0.10/0.56    inference(cnf_transformation,[],[f36])).
% 0.10/0.56  fof(f36,plain,(
% 0.10/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.10/0.56    inference(ennf_transformation,[],[f13])).
% 0.10/0.56  fof(f13,axiom,(
% 0.10/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 0.10/0.56  fof(f280,plain,(
% 0.10/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.10/0.56    inference(backward_demodulation,[],[f84,f81])).
% 0.10/0.56  fof(f81,plain,(
% 0.10/0.56    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.10/0.56    inference(definition_unfolding,[],[f52,f74])).
% 0.10/0.56  fof(f52,plain,(
% 0.10/0.56    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.10/0.56    inference(cnf_transformation,[],[f9])).
% 0.10/0.56  fof(f9,axiom,(
% 0.10/0.56    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
% 0.10/0.56  fof(f84,plain,(
% 0.10/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.10/0.56    inference(definition_unfolding,[],[f65,f75])).
% 0.10/0.56  fof(f75,plain,(
% 0.10/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.10/0.56    inference(definition_unfolding,[],[f51,f74])).
% 0.10/0.56  fof(f51,plain,(
% 0.10/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.10/0.56    inference(cnf_transformation,[],[f2])).
% 0.10/0.56  fof(f2,axiom,(
% 0.10/0.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.10/0.56  fof(f65,plain,(
% 0.10/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 0.10/0.56    inference(cnf_transformation,[],[f3])).
% 0.10/0.56  fof(f3,axiom,(
% 0.10/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 0.10/0.56  fof(f1727,plain,(
% 0.10/0.56    ( ! [X4] : (~r1_tarski(X4,k2_xboole_0(k1_xboole_0,k1_relat_1(sK0))) | r1_xboole_0(X4,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k2_xboole_0(sK1,k1_relat_1(sK0)))))) ) | (~spl3_3 | ~spl3_26)),
% 0.10/0.56    inference(forward_demodulation,[],[f1726,f105])).
% 0.10/0.56  fof(f1726,plain,(
% 0.10/0.56    ( ! [X4] : (~r1_tarski(X4,k2_xboole_0(k4_xboole_0(sK1,sK1),k1_relat_1(sK0))) | r1_xboole_0(X4,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k2_xboole_0(sK1,k1_relat_1(sK0)))))) ) | (~spl3_3 | ~spl3_26)),
% 0.10/0.56    inference(forward_demodulation,[],[f1725,f200])).
% 0.10/0.56  fof(f200,plain,(
% 0.10/0.56    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,sK1),k1_relat_1(sK0)) = k4_xboole_0(k2_xboole_0(X0,k1_relat_1(sK0)),sK1)) ) | ~spl3_3),
% 0.10/0.56    inference(resolution,[],[f63,f98])).
% 0.10/0.56  fof(f98,plain,(
% 0.10/0.56    r1_xboole_0(sK1,k1_relat_1(sK0)) | ~spl3_3),
% 0.10/0.56    inference(avatar_component_clause,[],[f96])).
% 0.10/0.56  fof(f63,plain,(
% 0.10/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)) )),
% 0.10/0.56    inference(cnf_transformation,[],[f35])).
% 0.10/0.56  fof(f35,plain,(
% 0.10/0.56    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 0.10/0.56    inference(ennf_transformation,[],[f11])).
% 0.10/0.56  fof(f11,axiom,(
% 0.10/0.56    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).
% 0.10/0.56  fof(f1725,plain,(
% 0.10/0.56    ( ! [X4] : (~r1_tarski(X4,k4_xboole_0(k2_xboole_0(sK1,k1_relat_1(sK0)),sK1)) | r1_xboole_0(X4,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k2_xboole_0(sK1,k1_relat_1(sK0)))))) ) | ~spl3_26),
% 0.10/0.56    inference(forward_demodulation,[],[f1674,f355])).
% 0.10/0.56  fof(f1674,plain,(
% 0.10/0.56    ( ! [X4] : (~r1_tarski(X4,k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK1,k1_relat_1(sK0)),sK1))) | r1_xboole_0(X4,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k2_xboole_0(sK1,k1_relat_1(sK0)))))) ) | ~spl3_26),
% 0.10/0.56    inference(superposition,[],[f367,f1485])).
% 0.10/0.56  fof(f1485,plain,(
% 0.10/0.56    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK1,k1_relat_1(sK0))) | ~spl3_26),
% 0.10/0.56    inference(avatar_component_clause,[],[f1483])).
% 0.10/0.56  fof(f367,plain,(
% 0.10/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) | r1_xboole_0(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) )),
% 0.10/0.56    inference(forward_demodulation,[],[f83,f81])).
% 0.10/0.56  fof(f83,plain,(
% 0.10/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,k4_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))))) )),
% 0.10/0.56    inference(definition_unfolding,[],[f66,f74,f75])).
% 0.10/0.56  fof(f66,plain,(
% 0.10/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 0.10/0.56    inference(cnf_transformation,[],[f3])).
% 0.10/0.56  fof(f1486,plain,(
% 0.10/0.56    spl3_26 | ~spl3_8),
% 0.10/0.56    inference(avatar_split_clause,[],[f1444,f714,f1483])).
% 0.10/0.56  fof(f714,plain,(
% 0.10/0.56    spl3_8 <=> k2_xboole_0(k1_relat_1(sK0),sK1) = k2_xboole_0(sK1,k1_relat_1(sK0))),
% 0.10/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.10/0.56  fof(f1444,plain,(
% 0.10/0.56    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK1,k1_relat_1(sK0))) | ~spl3_8),
% 0.10/0.56    inference(superposition,[],[f371,f716])).
% 0.10/0.56  fof(f716,plain,(
% 0.10/0.56    k2_xboole_0(k1_relat_1(sK0),sK1) = k2_xboole_0(sK1,k1_relat_1(sK0)) | ~spl3_8),
% 0.10/0.56    inference(avatar_component_clause,[],[f714])).
% 0.10/0.56  fof(f371,plain,(
% 0.10/0.56    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 0.10/0.56    inference(backward_demodulation,[],[f153,f355])).
% 0.10/0.56  fof(f153,plain,(
% 0.10/0.56    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X5),k2_xboole_0(X6,X5))) )),
% 0.10/0.56    inference(resolution,[],[f150,f61])).
% 0.10/0.56  fof(f717,plain,(
% 0.10/0.56    spl3_8 | ~spl3_7),
% 0.10/0.56    inference(avatar_split_clause,[],[f691,f534,f714])).
% 0.10/0.56  fof(f534,plain,(
% 0.10/0.56    spl3_7 <=> k1_relat_1(sK0) = k4_xboole_0(k1_relat_1(sK0),sK1)),
% 0.10/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.10/0.56  fof(f691,plain,(
% 0.10/0.56    k2_xboole_0(k1_relat_1(sK0),sK1) = k2_xboole_0(sK1,k1_relat_1(sK0)) | ~spl3_7),
% 0.10/0.56    inference(superposition,[],[f440,f536])).
% 0.10/0.56  fof(f536,plain,(
% 0.10/0.56    k1_relat_1(sK0) = k4_xboole_0(k1_relat_1(sK0),sK1) | ~spl3_7),
% 0.10/0.56    inference(avatar_component_clause,[],[f534])).
% 0.10/0.56  fof(f440,plain,(
% 0.10/0.56    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = k2_xboole_0(X7,k4_xboole_0(X8,X7))) )),
% 0.10/0.56    inference(forward_demodulation,[],[f435,f49])).
% 0.10/0.56  fof(f435,plain,(
% 0.10/0.56    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = k2_xboole_0(X7,k4_xboole_0(k2_xboole_0(X8,X7),X7))) )),
% 0.10/0.56    inference(resolution,[],[f372,f57])).
% 0.10/0.56  fof(f372,plain,(
% 0.10/0.56    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) )),
% 0.10/0.56    inference(backward_demodulation,[],[f150,f355])).
% 0.10/0.56  fof(f537,plain,(
% 0.10/0.56    spl3_7 | ~spl3_3),
% 0.10/0.56    inference(avatar_split_clause,[],[f532,f96,f534])).
% 0.10/0.56  fof(f532,plain,(
% 0.10/0.56    k1_relat_1(sK0) = k4_xboole_0(k1_relat_1(sK0),sK1) | ~spl3_3),
% 0.10/0.56    inference(forward_demodulation,[],[f531,f355])).
% 0.10/0.56  fof(f531,plain,(
% 0.10/0.56    k2_xboole_0(k1_xboole_0,k1_relat_1(sK0)) = k4_xboole_0(k1_relat_1(sK0),sK1) | ~spl3_3),
% 0.10/0.56    inference(forward_demodulation,[],[f524,f40])).
% 0.10/0.56  fof(f524,plain,(
% 0.10/0.56    k2_xboole_0(k4_xboole_0(k1_xboole_0,sK1),k1_relat_1(sK0)) = k4_xboole_0(k1_relat_1(sK0),sK1) | ~spl3_3),
% 0.10/0.56    inference(superposition,[],[f200,f355])).
% 0.10/0.56  fof(f99,plain,(
% 0.10/0.56    spl3_3),
% 0.10/0.56    inference(avatar_split_clause,[],[f37,f96])).
% 0.10/0.56  fof(f37,plain,(
% 0.10/0.56    r1_xboole_0(sK1,k1_relat_1(sK0))),
% 0.10/0.56    inference(cnf_transformation,[],[f27])).
% 0.10/0.56  fof(f27,plain,(
% 0.10/0.56    ? [X0] : (? [X1] : (k1_xboole_0 != k7_relat_1(X0,X1) & r1_xboole_0(X1,k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.10/0.56    inference(ennf_transformation,[],[f26])).
% 0.10/0.56  fof(f26,negated_conjecture,(
% 0.10/0.56    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.10/0.56    inference(negated_conjecture,[],[f25])).
% 0.10/0.56  fof(f25,conjecture,(
% 0.10/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.10/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.10/0.56  fof(f94,plain,(
% 0.10/0.56    ~spl3_2),
% 0.10/0.56    inference(avatar_split_clause,[],[f38,f91])).
% 0.10/0.56  fof(f38,plain,(
% 0.10/0.56    k1_xboole_0 != k7_relat_1(sK0,sK1)),
% 0.10/0.56    inference(cnf_transformation,[],[f27])).
% 0.10/0.56  fof(f89,plain,(
% 0.10/0.56    spl3_1),
% 0.10/0.56    inference(avatar_split_clause,[],[f39,f86])).
% 0.10/0.56  fof(f39,plain,(
% 0.10/0.56    v1_relat_1(sK0)),
% 0.10/0.56    inference(cnf_transformation,[],[f27])).
% 0.10/0.56  % SZS output end Proof for theBenchmark
% 0.10/0.56  % (23373)------------------------------
% 0.10/0.56  % (23373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.56  % (23373)Termination reason: Refutation
% 0.10/0.56  
% 0.10/0.56  % (23373)Memory used [KB]: 12409
% 0.10/0.56  % (23373)Time elapsed: 0.242 s
% 0.10/0.56  % (23373)------------------------------
% 0.10/0.56  % (23373)------------------------------
% 0.10/0.56  % (23356)Success in time 0.298 s
%------------------------------------------------------------------------------

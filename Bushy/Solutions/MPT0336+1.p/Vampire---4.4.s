%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t149_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:02 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 356 expanded)
%              Number of leaves         :   48 ( 147 expanded)
%              Depth                    :   10
%              Number of atoms          :  402 ( 777 expanded)
%              Number of equality atoms :   66 ( 135 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f82,f89,f96,f106,f115,f125,f132,f142,f152,f160,f187,f196,f216,f227,f253,f265,f277,f285,f319,f335,f342,f387,f489,f577,f622,f957,f1018,f1185,f1292])).

fof(f1292,plain,
    ( ~ spl4_8
    | ~ spl4_32
    | spl4_45
    | ~ spl4_50 ),
    inference(avatar_contradiction_clause,[],[f1291])).

fof(f1291,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_32
    | ~ spl4_45
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f1278,f105])).

fof(f105,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1278,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_32
    | ~ spl4_45
    | ~ spl4_50 ),
    inference(backward_demodulation,[],[f1273,f386])).

fof(f386,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl4_45
  <=> ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f1273,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl4_32
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f1272,f264])).

fof(f264,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl4_32
  <=> k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1272,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,sK2)
    | ~ spl4_32
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f1245,f959])).

fof(f959,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f290,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',commutativity_k3_xboole_0)).

fof(f290,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f65,f53])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',idempotence_k3_xboole_0)).

fof(f65,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',t16_xboole_1)).

fof(f1245,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl4_32
    | ~ spl4_50 ),
    inference(superposition,[],[f370,f621])).

fof(f621,plain,
    ( k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) = sK2
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f620])).

fof(f620,plain,
    ( spl4_50
  <=> k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f370,plain,
    ( ! [X16] : k3_xboole_0(sK1,X16) = k3_xboole_0(sK1,k2_xboole_0(sK2,X16))
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f349,f163])).

fof(f163,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f54,f49])).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',t1_boole)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(f349,plain,
    ( ! [X16] : k3_xboole_0(sK1,k2_xboole_0(sK2,X16)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X16))
    | ~ spl4_32 ),
    inference(superposition,[],[f66,f264])).

fof(f66,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',t23_xboole_1)).

fof(f1185,plain,
    ( spl4_56
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f751,f575,f1183])).

fof(f1183,plain,
    ( spl4_56
  <=> k1_tarski(sK3) = k2_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f575,plain,
    ( spl4_48
  <=> k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f751,plain,
    ( k1_tarski(sK3) = k2_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | ~ spl4_48 ),
    inference(superposition,[],[f576,f54])).

fof(f576,plain,
    ( k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f575])).

fof(f1018,plain,
    ( spl4_54
    | ~ spl4_14
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f441,f283,f130,f1016])).

fof(f1016,plain,
    ( spl4_54
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f130,plain,
    ( spl4_14
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f283,plain,
    ( spl4_36
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f441,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,k1_tarski(sK3)))
    | ~ spl4_14
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f440,f53])).

fof(f440,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK2,k1_tarski(sK3)))
    | ~ spl4_14
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f415,f55])).

fof(f415,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_tarski(sK3),sK2))
    | ~ spl4_14
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f131,f284,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',t27_xboole_1)).

fof(f284,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f283])).

fof(f131,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f130])).

fof(f957,plain,
    ( spl4_52
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f430,f283,f194,f955])).

fof(f955,plain,
    ( spl4_52
  <=> r1_tarski(k3_xboole_0(sK0,k3_xboole_0(sK1,k1_tarski(sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f194,plain,
    ( spl4_24
  <=> r1_tarski(k1_tarski(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f430,plain,
    ( r1_tarski(k3_xboole_0(sK0,k3_xboole_0(sK1,k1_tarski(sK3))),sK2)
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f429,f299])).

fof(f299,plain,(
    ! [X8,X7,X9] : k3_xboole_0(X7,k3_xboole_0(X8,X9)) = k3_xboole_0(X9,k3_xboole_0(X7,X8)) ),
    inference(superposition,[],[f65,f55])).

fof(f429,plain,
    ( r1_tarski(k3_xboole_0(sK1,k3_xboole_0(k1_tarski(sK3),sK0)),sK2)
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f428,f299])).

fof(f428,plain,
    ( r1_tarski(k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)),sK2)
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f427,f55])).

fof(f427,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)),sK2)
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f419,f53])).

fof(f419,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)),k3_xboole_0(sK2,sK2))
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f284,f195,f68])).

fof(f195,plain,
    ( r1_tarski(k1_tarski(sK3),sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f622,plain,
    ( spl4_50
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f595,f487,f620])).

fof(f487,plain,
    ( spl4_46
  <=> k2_xboole_0(k3_xboole_0(sK0,sK1),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f595,plain,
    ( k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) = sK2
    | ~ spl4_46 ),
    inference(superposition,[],[f488,f54])).

fof(f488,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),sK2) = sK2
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f487])).

fof(f577,plain,
    ( spl4_48
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f205,f130,f575])).

fof(f205,plain,
    ( k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f131,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',t12_xboole_1)).

fof(f489,plain,
    ( spl4_46
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f286,f283,f487])).

fof(f286,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),sK2) = sK2
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f284,f58])).

fof(f387,plain,
    ( ~ spl4_45
    | ~ spl4_32
    | spl4_41 ),
    inference(avatar_split_clause,[],[f379,f333,f263,f385])).

fof(f333,plain,
    ( spl4_41
  <=> ~ v1_xboole_0(k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f379,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    | ~ spl4_32
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f378,f55])).

fof(f378,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK1,sK0))
    | ~ spl4_32
    | ~ spl4_41 ),
    inference(backward_demodulation,[],[f377,f334])).

fof(f334,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f333])).

fof(f377,plain,
    ( ! [X16] : k3_xboole_0(sK1,X16) = k3_xboole_0(sK1,k2_xboole_0(X16,sK2))
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f357,f49])).

fof(f357,plain,
    ( ! [X16] : k3_xboole_0(sK1,k2_xboole_0(X16,sK2)) = k2_xboole_0(k3_xboole_0(sK1,X16),k1_xboole_0)
    | ~ spl4_32 ),
    inference(superposition,[],[f66,f264])).

fof(f342,plain,
    ( ~ spl4_43
    | spl4_21 ),
    inference(avatar_split_clause,[],[f234,f158,f340])).

fof(f340,plain,
    ( spl4_43
  <=> k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f158,plain,
    ( spl4_21
  <=> ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f234,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k1_xboole_0
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f159,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',d7_xboole_0)).

fof(f159,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f158])).

fof(f335,plain,
    ( ~ spl4_41
    | ~ spl4_8
    | spl4_39 ),
    inference(avatar_split_clause,[],[f326,f317,f104,f333])).

fof(f317,plain,
    ( spl4_39
  <=> k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f326,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)))
    | ~ spl4_8
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f323,f55])).

fof(f323,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK2),sK1))
    | ~ spl4_8
    | ~ spl4_39 ),
    inference(unit_resulting_resolution,[],[f105,f318,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',t8_boole)).

fof(f318,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k1_xboole_0
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f317])).

fof(f319,plain,
    ( ~ spl4_39
    | spl4_7 ),
    inference(avatar_split_clause,[],[f233,f94,f317])).

fof(f94,plain,
    ( spl4_7
  <=> ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f233,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k1_xboole_0
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f95,f60])).

fof(f95,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f285,plain,
    ( spl4_36
    | ~ spl4_14
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f267,f194,f130,f283])).

fof(f267,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl4_14
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f131,f195,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',t1_xboole_1)).

fof(f277,plain,
    ( ~ spl4_35
    | ~ spl4_8
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f266,f194,f104,f275])).

fof(f275,plain,
    ( spl4_35
  <=> ~ r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f266,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_8
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f195,f179,f67])).

fof(f179,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(X0),k1_xboole_0)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f117,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',l1_zfmisc_1)).

fof(f117,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f105,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',t7_boole)).

fof(f265,plain,
    ( spl4_32
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f229,f150,f263])).

fof(f150,plain,
    ( spl4_18
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f229,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f151,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f151,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f150])).

fof(f253,plain,
    ( spl4_30
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f228,f87,f251])).

fof(f251,plain,
    ( spl4_30
  <=> k3_xboole_0(sK2,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f87,plain,
    ( spl4_4
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f228,plain,
    ( k3_xboole_0(sK2,sK1) = k1_xboole_0
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f88,f59])).

fof(f88,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f227,plain,
    ( spl4_28
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f217,f214,f225])).

fof(f225,plain,
    ( spl4_28
  <=> k2_xboole_0(sK2,k1_tarski(sK3)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f214,plain,
    ( spl4_26
  <=> k2_xboole_0(k1_tarski(sK3),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f217,plain,
    ( k2_xboole_0(sK2,k1_tarski(sK3)) = sK2
    | ~ spl4_26 ),
    inference(superposition,[],[f215,f54])).

fof(f215,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK2) = sK2
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( spl4_26
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f206,f194,f214])).

fof(f206,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK2) = sK2
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f195,f58])).

fof(f196,plain,
    ( spl4_24
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f188,f80,f194])).

fof(f80,plain,
    ( spl4_2
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f188,plain,
    ( r1_tarski(k1_tarski(sK3),sK2)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f81,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f187,plain,
    ( ~ spl4_23
    | spl4_17 ),
    inference(avatar_split_clause,[],[f180,f140,f185])).

fof(f185,plain,
    ( spl4_23
  <=> ~ r1_tarski(k1_tarski(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f140,plain,
    ( spl4_17
  <=> ~ r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f180,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK3)
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f141,f61])).

fof(f141,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f160,plain,
    ( ~ spl4_21
    | spl4_7 ),
    inference(avatar_split_clause,[],[f144,f94,f158])).

fof(f144,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f95,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',symmetry_r1_xboole_0)).

fof(f152,plain,
    ( spl4_18
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f143,f87,f150])).

fof(f143,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f88,f57])).

fof(f142,plain,
    ( ~ spl4_17
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f134,f80,f140])).

fof(f134,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f81,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f132,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f44,f130])).

fof(f44,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',t149_zfmisc_1)).

fof(f125,plain,
    ( ~ spl4_13
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f116,f80,f123])).

fof(f123,plain,
    ( spl4_13
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f116,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f81,f64])).

fof(f115,plain,
    ( spl4_10
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f97,f73,f113])).

fof(f113,plain,
    ( spl4_10
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f73,plain,
    ( spl4_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f97,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f74,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',t6_boole)).

fof(f74,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f73])).

fof(f106,plain,
    ( spl4_8
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f99,f73,f104])).

fof(f99,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_0 ),
    inference(backward_demodulation,[],[f97,f74])).

fof(f96,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f47,f94])).

fof(f47,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f46,f87])).

fof(f46,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f45,f80])).

fof(f45,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f48,f73])).

fof(f48,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t149_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------

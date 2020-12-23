%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0777+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:38 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 105 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :    6
%              Number of atoms          :  146 ( 233 expanded)
%              Number of equality atoms :   44 (  76 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f31,f35,f39,f43,f49,f53,f59,f70,f80,f156,f168,f184])).

fof(f184,plain,
    ( spl3_1
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl3_1
    | ~ spl3_27 ),
    inference(trivial_inequality_removal,[],[f181])).

fof(f181,plain,
    ( k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_27 ),
    inference(superposition,[],[f21,f166])).

fof(f166,plain,
    ( ! [X2,X3] : k2_wellord1(k2_wellord1(sK2,X2),X3) = k2_wellord1(sK2,k3_xboole_0(X2,X3))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl3_27
  <=> ! [X3,X2] : k2_wellord1(k2_wellord1(sK2,X2),X3) = k2_wellord1(sK2,k3_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f21,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl3_1
  <=> k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f168,plain,
    ( spl3_27
    | ~ spl3_12
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f160,f153,f78,f165])).

fof(f78,plain,
    ( spl3_12
  <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k3_xboole_0(k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f153,plain,
    ( spl3_26
  <=> ! [X3,X4] : k2_wellord1(sK2,k3_xboole_0(X3,X4)) = k3_xboole_0(k2_wellord1(sK2,X3),k2_zfmisc_1(X4,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f160,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_12
    | ~ spl3_26 ),
    inference(superposition,[],[f79,f154])).

fof(f154,plain,
    ( ! [X4,X3] : k2_wellord1(sK2,k3_xboole_0(X3,X4)) = k3_xboole_0(k2_wellord1(sK2,X3),k2_zfmisc_1(X4,X4))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f153])).

% (30614)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
fof(f79,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k3_xboole_0(k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f156,plain,
    ( spl3_26
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f103,f68,f47,f153])).

fof(f47,plain,
    ( spl3_7
  <=> ! [X0] : k2_wellord1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f68,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] : k3_xboole_0(k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X2)) = k3_xboole_0(sK2,k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f103,plain,
    ( ! [X0,X1] : k3_xboole_0(k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1)) = k2_wellord1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(superposition,[],[f48,f69])).

fof(f69,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X2)) = k3_xboole_0(sK2,k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f48,plain,
    ( ! [X0] : k2_wellord1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,X0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f47])).

fof(f80,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f75,f51,f24,f78])).

fof(f24,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f51,plain,
    ( spl3_8
  <=> ! [X1,X3,X2] :
        ( k2_wellord1(k2_wellord1(X1,X2),X3) = k3_xboole_0(k2_wellord1(X1,X2),k2_zfmisc_1(X3,X3))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f75,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k3_xboole_0(k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1))
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f52,f26])).

fof(f26,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f52,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_relat_1(X1)
        | k2_wellord1(k2_wellord1(X1,X2),X3) = k3_xboole_0(k2_wellord1(X1,X2),k2_zfmisc_1(X3,X3)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f51])).

fof(f70,plain,
    ( spl3_10
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f65,f57,f41,f68])).

fof(f41,plain,
    ( spl3_6
  <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f57,plain,
    ( spl3_9
  <=> ! [X1,X0] : k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(X0,X0),X1)) = k3_xboole_0(k2_wellord1(sK2,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f65,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X2)) = k3_xboole_0(sK2,k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f58,f42])).

fof(f42,plain,
    ( ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f41])).

fof(f58,plain,
    ( ! [X0,X1] : k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(X0,X0),X1)) = k3_xboole_0(k2_wellord1(sK2,X0),X1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f54,f47,f37,f57])).

fof(f37,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f54,plain,
    ( ! [X0,X1] : k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(X0,X0),X1)) = k3_xboole_0(k2_wellord1(sK2,X0),X1)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(superposition,[],[f38,f48])).

fof(f38,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f37])).

fof(f53,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f45,f33,f29,f51])).

fof(f29,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f33,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( v1_relat_1(k2_wellord1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f45,plain,
    ( ! [X2,X3,X1] :
        ( k2_wellord1(k2_wellord1(X1,X2),X3) = k3_xboole_0(k2_wellord1(X1,X2),k2_zfmisc_1(X3,X3))
        | ~ v1_relat_1(X1) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k2_wellord1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f30,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f49,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f44,f29,f24,f47])).

fof(f44,plain,
    ( ! [X0] : k2_wellord1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,X0))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f30,f26])).

fof(f43,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f39,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f35,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f31,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(f27,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f24])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(X2,k3_xboole_0(X0,X1))
        & v1_relat_1(X2) )
   => ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(X2,k3_xboole_0(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

fof(f22,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f13,f19])).

fof(f13,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------

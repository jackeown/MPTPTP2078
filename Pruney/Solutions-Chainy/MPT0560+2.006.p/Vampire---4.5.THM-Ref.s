%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:00 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 133 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :    6
%              Number of atoms          :  195 ( 324 expanded)
%              Number of equality atoms :   57 (  98 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f41,f45,f50,f54,f60,f64,f70,f74,f80,f90,f131,f146,f195,f209])).

fof(f209,plain,
    ( spl3_5
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl3_5
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f207,f49])).

fof(f49,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_5
  <=> k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f207,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f203,f69])).

fof(f69,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_9
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f203,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k2_relat_1(k7_relat_1(sK0,sK1))
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(superposition,[],[f194,f145])).

fof(f145,plain,
    ( k7_relat_1(sK0,sK1) = k7_relat_1(k7_relat_1(sK0,sK2),sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_19
  <=> k7_relat_1(sK0,sK1) = k7_relat_1(k7_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f194,plain,
    ( ! [X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl3_23
  <=> ! [X1,X0] : k2_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f195,plain,
    ( spl3_23
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f184,f88,f29,f193])).

fof(f29,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f88,plain,
    ( spl3_12
  <=> ! [X1,X3,X2] :
        ( k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f184,plain,
    ( ! [X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1)
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(resolution,[],[f89,f31])).

fof(f31,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f89,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f146,plain,
    ( spl3_19
    | ~ spl3_7
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f134,f129,f57,f143])).

fof(f57,plain,
    ( spl3_7
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f129,plain,
    ( spl3_18
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f134,plain,
    ( k7_relat_1(sK0,sK1) = k7_relat_1(k7_relat_1(sK0,sK2),sK1)
    | ~ spl3_7
    | ~ spl3_18 ),
    inference(superposition,[],[f130,f59])).

fof(f59,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f130,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X1,X0)))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f129])).

fof(f131,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f81,f78,f43,f129])).

fof(f43,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f78,plain,
    ( spl3_11
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f81,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X1,X0)))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(superposition,[],[f79,f44])).

fof(f44,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f79,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f90,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f66,f62,f39,f88])).

fof(f39,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f62,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f66,plain,
    ( ! [X2,X3,X1] :
        ( k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3)
        | ~ v1_relat_1(X1) )
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f63,f40])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f80,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f75,f72,f29,f78])).

fof(f72,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f75,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(resolution,[],[f73,f31])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f27,f72])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f25,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f70,plain,
    ( spl3_9
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f65,f62,f29,f68])).

fof(f65,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(resolution,[],[f63,f31])).

fof(f64,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f23,f62])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f60,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f55,f52,f34,f57])).

fof(f34,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f52,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k1_setfam_1(k2_tarski(X0,X1)) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f55,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f53,f36])).

fof(f36,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_setfam_1(k2_tarski(X0,X1)) = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f54,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f52])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f50,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f45,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f41,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f37,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n014.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:45:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.40  % (21844)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.18/0.41  % (21844)Refutation found. Thanks to Tanya!
% 0.18/0.41  % SZS status Theorem for theBenchmark
% 0.18/0.41  % SZS output start Proof for theBenchmark
% 0.18/0.41  fof(f210,plain,(
% 0.18/0.41    $false),
% 0.18/0.41    inference(avatar_sat_refutation,[],[f32,f37,f41,f45,f50,f54,f60,f64,f70,f74,f80,f90,f131,f146,f195,f209])).
% 0.18/0.41  fof(f209,plain,(
% 0.18/0.41    spl3_5 | ~spl3_9 | ~spl3_19 | ~spl3_23),
% 0.18/0.41    inference(avatar_contradiction_clause,[],[f208])).
% 0.18/0.41  fof(f208,plain,(
% 0.18/0.41    $false | (spl3_5 | ~spl3_9 | ~spl3_19 | ~spl3_23)),
% 0.18/0.41    inference(subsumption_resolution,[],[f207,f49])).
% 0.18/0.41  fof(f49,plain,(
% 0.18/0.41    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) | spl3_5),
% 0.18/0.41    inference(avatar_component_clause,[],[f47])).
% 0.18/0.41  fof(f47,plain,(
% 0.18/0.41    spl3_5 <=> k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.18/0.41  fof(f207,plain,(
% 0.18/0.41    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) | (~spl3_9 | ~spl3_19 | ~spl3_23)),
% 0.18/0.41    inference(forward_demodulation,[],[f203,f69])).
% 0.18/0.41  fof(f69,plain,(
% 0.18/0.41    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | ~spl3_9),
% 0.18/0.41    inference(avatar_component_clause,[],[f68])).
% 0.18/0.41  fof(f68,plain,(
% 0.18/0.41    spl3_9 <=> ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.18/0.41  fof(f203,plain,(
% 0.18/0.41    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k2_relat_1(k7_relat_1(sK0,sK1)) | (~spl3_19 | ~spl3_23)),
% 0.18/0.41    inference(superposition,[],[f194,f145])).
% 0.18/0.41  fof(f145,plain,(
% 0.18/0.41    k7_relat_1(sK0,sK1) = k7_relat_1(k7_relat_1(sK0,sK2),sK1) | ~spl3_19),
% 0.18/0.41    inference(avatar_component_clause,[],[f143])).
% 0.18/0.41  fof(f143,plain,(
% 0.18/0.41    spl3_19 <=> k7_relat_1(sK0,sK1) = k7_relat_1(k7_relat_1(sK0,sK2),sK1)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.18/0.41  fof(f194,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1)) ) | ~spl3_23),
% 0.18/0.41    inference(avatar_component_clause,[],[f193])).
% 0.18/0.41  fof(f193,plain,(
% 0.18/0.41    spl3_23 <=> ! [X1,X0] : k2_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.18/0.41  fof(f195,plain,(
% 0.18/0.41    spl3_23 | ~spl3_1 | ~spl3_12),
% 0.18/0.41    inference(avatar_split_clause,[],[f184,f88,f29,f193])).
% 0.18/0.41  fof(f29,plain,(
% 0.18/0.41    spl3_1 <=> v1_relat_1(sK0)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.18/0.41  fof(f88,plain,(
% 0.18/0.41    spl3_12 <=> ! [X1,X3,X2] : (k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3) | ~v1_relat_1(X1))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.18/0.41  fof(f184,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1)) ) | (~spl3_1 | ~spl3_12)),
% 0.18/0.41    inference(resolution,[],[f89,f31])).
% 0.18/0.41  fof(f31,plain,(
% 0.18/0.41    v1_relat_1(sK0) | ~spl3_1),
% 0.18/0.41    inference(avatar_component_clause,[],[f29])).
% 0.18/0.41  fof(f89,plain,(
% 0.18/0.41    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3)) ) | ~spl3_12),
% 0.18/0.41    inference(avatar_component_clause,[],[f88])).
% 0.18/0.41  fof(f146,plain,(
% 0.18/0.41    spl3_19 | ~spl3_7 | ~spl3_18),
% 0.18/0.41    inference(avatar_split_clause,[],[f134,f129,f57,f143])).
% 0.18/0.41  fof(f57,plain,(
% 0.18/0.41    spl3_7 <=> sK1 = k1_setfam_1(k2_tarski(sK1,sK2))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.18/0.41  fof(f129,plain,(
% 0.18/0.41    spl3_18 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X1,X0)))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.18/0.41  fof(f134,plain,(
% 0.18/0.41    k7_relat_1(sK0,sK1) = k7_relat_1(k7_relat_1(sK0,sK2),sK1) | (~spl3_7 | ~spl3_18)),
% 0.18/0.41    inference(superposition,[],[f130,f59])).
% 0.18/0.41  fof(f59,plain,(
% 0.18/0.41    sK1 = k1_setfam_1(k2_tarski(sK1,sK2)) | ~spl3_7),
% 0.18/0.41    inference(avatar_component_clause,[],[f57])).
% 0.18/0.41  fof(f130,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X1,X0)))) ) | ~spl3_18),
% 0.18/0.41    inference(avatar_component_clause,[],[f129])).
% 0.18/0.41  fof(f131,plain,(
% 0.18/0.41    spl3_18 | ~spl3_4 | ~spl3_11),
% 0.18/0.41    inference(avatar_split_clause,[],[f81,f78,f43,f129])).
% 0.18/0.41  fof(f43,plain,(
% 0.18/0.41    spl3_4 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.18/0.41  fof(f78,plain,(
% 0.18/0.41    spl3_11 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1)))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.18/0.41  fof(f81,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X1,X0)))) ) | (~spl3_4 | ~spl3_11)),
% 0.18/0.41    inference(superposition,[],[f79,f44])).
% 0.18/0.41  fof(f44,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl3_4),
% 0.18/0.41    inference(avatar_component_clause,[],[f43])).
% 0.18/0.41  fof(f79,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl3_11),
% 0.18/0.41    inference(avatar_component_clause,[],[f78])).
% 0.18/0.41  fof(f90,plain,(
% 0.18/0.41    spl3_12 | ~spl3_3 | ~spl3_8),
% 0.18/0.41    inference(avatar_split_clause,[],[f66,f62,f39,f88])).
% 0.18/0.41  fof(f39,plain,(
% 0.18/0.41    spl3_3 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.18/0.41  fof(f62,plain,(
% 0.18/0.41    spl3_8 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.18/0.41  fof(f66,plain,(
% 0.18/0.41    ( ! [X2,X3,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3) | ~v1_relat_1(X1)) ) | (~spl3_3 | ~spl3_8)),
% 0.18/0.41    inference(resolution,[],[f63,f40])).
% 0.18/0.41  fof(f40,plain,(
% 0.18/0.41    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_3),
% 0.18/0.41    inference(avatar_component_clause,[],[f39])).
% 0.18/0.41  fof(f63,plain,(
% 0.18/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl3_8),
% 0.18/0.41    inference(avatar_component_clause,[],[f62])).
% 0.18/0.41  fof(f80,plain,(
% 0.18/0.41    spl3_11 | ~spl3_1 | ~spl3_10),
% 0.18/0.41    inference(avatar_split_clause,[],[f75,f72,f29,f78])).
% 0.18/0.41  fof(f72,plain,(
% 0.18/0.41    spl3_10 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.18/0.41  fof(f75,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1)))) ) | (~spl3_1 | ~spl3_10)),
% 0.18/0.41    inference(resolution,[],[f73,f31])).
% 0.18/0.41  fof(f73,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl3_10),
% 0.18/0.41    inference(avatar_component_clause,[],[f72])).
% 0.18/0.41  fof(f74,plain,(
% 0.18/0.41    spl3_10),
% 0.18/0.41    inference(avatar_split_clause,[],[f27,f72])).
% 0.18/0.41  fof(f27,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 0.18/0.41    inference(definition_unfolding,[],[f25,f21])).
% 0.18/0.41  fof(f21,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.18/0.41    inference(cnf_transformation,[],[f3])).
% 0.18/0.41  fof(f3,axiom,(
% 0.18/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.18/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.18/0.41  fof(f25,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f13])).
% 0.18/0.41  fof(f13,plain,(
% 0.18/0.41    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.18/0.41    inference(ennf_transformation,[],[f5])).
% 0.18/0.41  fof(f5,axiom,(
% 0.18/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.18/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.18/0.41  fof(f70,plain,(
% 0.18/0.41    spl3_9 | ~spl3_1 | ~spl3_8),
% 0.18/0.41    inference(avatar_split_clause,[],[f65,f62,f29,f68])).
% 0.18/0.41  fof(f65,plain,(
% 0.18/0.41    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | (~spl3_1 | ~spl3_8)),
% 0.18/0.41    inference(resolution,[],[f63,f31])).
% 0.18/0.41  fof(f64,plain,(
% 0.18/0.41    spl3_8),
% 0.18/0.41    inference(avatar_split_clause,[],[f23,f62])).
% 0.18/0.41  fof(f23,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f11])).
% 0.18/0.41  fof(f11,plain,(
% 0.18/0.41    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.18/0.41    inference(ennf_transformation,[],[f6])).
% 0.18/0.41  fof(f6,axiom,(
% 0.18/0.41    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.18/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.18/0.41  fof(f60,plain,(
% 0.18/0.41    spl3_7 | ~spl3_2 | ~spl3_6),
% 0.18/0.41    inference(avatar_split_clause,[],[f55,f52,f34,f57])).
% 0.18/0.41  fof(f34,plain,(
% 0.18/0.41    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.18/0.41  fof(f52,plain,(
% 0.18/0.41    spl3_6 <=> ! [X1,X0] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.18/0.41  fof(f55,plain,(
% 0.18/0.41    sK1 = k1_setfam_1(k2_tarski(sK1,sK2)) | (~spl3_2 | ~spl3_6)),
% 0.18/0.41    inference(resolution,[],[f53,f36])).
% 0.18/0.41  fof(f36,plain,(
% 0.18/0.41    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.18/0.41    inference(avatar_component_clause,[],[f34])).
% 0.18/0.41  fof(f53,plain,(
% 0.18/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) ) | ~spl3_6),
% 0.18/0.41    inference(avatar_component_clause,[],[f52])).
% 0.18/0.41  fof(f54,plain,(
% 0.18/0.41    spl3_6),
% 0.18/0.41    inference(avatar_split_clause,[],[f26,f52])).
% 0.18/0.41  fof(f26,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.18/0.41    inference(definition_unfolding,[],[f24,f21])).
% 0.18/0.41  fof(f24,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f12])).
% 0.18/0.41  fof(f12,plain,(
% 0.18/0.41    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.18/0.41    inference(ennf_transformation,[],[f1])).
% 0.18/0.41  fof(f1,axiom,(
% 0.18/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.18/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.18/0.41  fof(f50,plain,(
% 0.18/0.41    ~spl3_5),
% 0.18/0.41    inference(avatar_split_clause,[],[f19,f47])).
% 0.18/0.41  fof(f19,plain,(
% 0.18/0.41    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)),
% 0.18/0.41    inference(cnf_transformation,[],[f16])).
% 0.18/0.41  fof(f16,plain,(
% 0.18/0.41    (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 0.18/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14])).
% 0.18/0.41  fof(f14,plain,(
% 0.18/0.41    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 0.18/0.41    introduced(choice_axiom,[])).
% 0.18/0.41  fof(f15,plain,(
% 0.18/0.41    ? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) => (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2))),
% 0.18/0.41    introduced(choice_axiom,[])).
% 0.18/0.41  fof(f9,plain,(
% 0.18/0.41    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 0.18/0.41    inference(ennf_transformation,[],[f8])).
% 0.18/0.41  fof(f8,negated_conjecture,(
% 0.18/0.41    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.18/0.41    inference(negated_conjecture,[],[f7])).
% 0.18/0.41  fof(f7,conjecture,(
% 0.18/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.18/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 0.18/0.41  fof(f45,plain,(
% 0.18/0.41    spl3_4),
% 0.18/0.41    inference(avatar_split_clause,[],[f20,f43])).
% 0.18/0.41  fof(f20,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f2])).
% 0.18/0.41  fof(f2,axiom,(
% 0.18/0.41    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.18/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.18/0.41  fof(f41,plain,(
% 0.18/0.41    spl3_3),
% 0.18/0.41    inference(avatar_split_clause,[],[f22,f39])).
% 0.18/0.41  fof(f22,plain,(
% 0.18/0.41    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f10])).
% 0.18/0.41  fof(f10,plain,(
% 0.18/0.41    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.18/0.41    inference(ennf_transformation,[],[f4])).
% 0.18/0.41  fof(f4,axiom,(
% 0.18/0.41    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.18/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.18/0.41  fof(f37,plain,(
% 0.18/0.41    spl3_2),
% 0.18/0.41    inference(avatar_split_clause,[],[f18,f34])).
% 0.18/0.41  fof(f18,plain,(
% 0.18/0.41    r1_tarski(sK1,sK2)),
% 0.18/0.41    inference(cnf_transformation,[],[f16])).
% 0.18/0.41  fof(f32,plain,(
% 0.18/0.41    spl3_1),
% 0.18/0.41    inference(avatar_split_clause,[],[f17,f29])).
% 0.18/0.41  fof(f17,plain,(
% 0.18/0.41    v1_relat_1(sK0)),
% 0.18/0.41    inference(cnf_transformation,[],[f16])).
% 0.18/0.41  % SZS output end Proof for theBenchmark
% 0.18/0.41  % (21844)------------------------------
% 0.18/0.41  % (21844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.41  % (21844)Termination reason: Refutation
% 0.18/0.41  
% 0.18/0.41  % (21844)Memory used [KB]: 6268
% 0.18/0.41  % (21844)Time elapsed: 0.010 s
% 0.18/0.41  % (21844)------------------------------
% 0.18/0.41  % (21844)------------------------------
% 0.18/0.42  % (21836)Success in time 0.075 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:42:33 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 203 expanded)
%              Number of leaves         :   24 (  84 expanded)
%              Depth                    :    7
%              Number of atoms          :  270 ( 542 expanded)
%              Number of equality atoms :   45 ( 127 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f57,f62,f74,f122,f129,f133,f163,f172,f193,f238,f289,f300,f307,f311,f337,f353])).

fof(f353,plain,
    ( spl9_24
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f352,f335,f304])).

fof(f304,plain,
    ( spl9_24
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f335,plain,
    ( spl9_26
  <=> ! [X6] :
        ( ~ r2_hidden(X6,sK3)
        | r2_hidden(X6,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f352,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl9_26 ),
    inference(duplicate_literal_removal,[],[f350])).

fof(f350,plain,
    ( r1_tarski(sK3,sK1)
    | r1_tarski(sK3,sK1)
    | ~ spl9_26 ),
    inference(resolution,[],[f343,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f343,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK6(X4,sK1),sK3)
        | r1_tarski(X4,sK1) )
    | ~ spl9_26 ),
    inference(resolution,[],[f336,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f336,plain,
    ( ! [X6] :
        ( r2_hidden(X6,sK1)
        | ~ r2_hidden(X6,sK3) )
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f335])).

fof(f337,plain,
    ( spl9_26
    | spl9_10
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f331,f59,f54,f93,f335])).

fof(f93,plain,
    ( spl9_10
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f54,plain,
    ( spl9_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f59,plain,
    ( spl9_5
  <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f331,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X7,sK0)
        | ~ r2_hidden(X6,sK3)
        | r2_hidden(X6,sK1) )
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f104,f55])).

fof(f55,plain,
    ( sK0 = sK2
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f104,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X7,sK2)
        | r2_hidden(X6,sK1) )
    | ~ spl9_5 ),
    inference(resolution,[],[f65,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f65,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X5,sK3)
        | ~ r2_hidden(X4,sK2) )
    | ~ spl9_5 ),
    inference(superposition,[],[f34,f61])).

fof(f61,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f311,plain,
    ( spl9_14
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f310,f188,f126])).

fof(f126,plain,
    ( spl9_14
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f188,plain,
    ( spl9_18
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f310,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl9_18 ),
    inference(duplicate_literal_removal,[],[f308])).

fof(f308,plain,
    ( r1_tarski(sK2,sK0)
    | r1_tarski(sK2,sK0)
    | ~ spl9_18 ),
    inference(resolution,[],[f265,f28])).

fof(f265,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK6(X4,sK0),sK2)
        | r1_tarski(X4,sK0) )
    | ~ spl9_18 ),
    inference(resolution,[],[f189,f29])).

fof(f189,plain,
    ( ! [X5] :
        ( r2_hidden(X5,sK0)
        | ~ r2_hidden(X5,sK2) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f188])).

fof(f307,plain,
    ( spl9_3
    | ~ spl9_24
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f302,f297,f304,f50])).

fof(f50,plain,
    ( spl9_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f297,plain,
    ( spl9_23
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f302,plain,
    ( ~ r1_tarski(sK3,sK1)
    | sK1 = sK3
    | ~ spl9_23 ),
    inference(resolution,[],[f299,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f299,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f297])).

fof(f300,plain,
    ( spl9_23
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f295,f131,f297])).

fof(f131,plain,
    ( spl9_15
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f295,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl9_15 ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl9_15 ),
    inference(resolution,[],[f167,f28])).

fof(f167,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(X3,sK3),sK1)
        | r1_tarski(X3,sK3) )
    | ~ spl9_15 ),
    inference(resolution,[],[f132,f29])).

fof(f132,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f289,plain,
    ( spl9_2
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl9_2
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f19,f47,f272])).

fof(f272,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f179,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f179,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0,sK1),X0)
        | sK1 = X0 )
    | ~ spl9_6 ),
    inference(resolution,[],[f70,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f70,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl9_6
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f47,plain,
    ( k1_xboole_0 != sK1
    | spl9_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f238,plain,
    ( spl9_16
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f234,f191,f169])).

fof(f169,plain,
    ( spl9_16
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f191,plain,
    ( spl9_19
  <=> ! [X4] : ~ r2_hidden(X4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f234,plain,
    ( v1_xboole_0(sK3)
    | ~ spl9_19 ),
    inference(resolution,[],[f192,f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f192,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK3)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( spl9_18
    | spl9_19
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f103,f59,f191,f188])).

fof(f103,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK3)
        | ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f65,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f172,plain,
    ( ~ spl9_16
    | spl9_6
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f164,f131,f69,f169])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(sK3) )
    | ~ spl9_15 ),
    inference(resolution,[],[f132,f21])).

fof(f163,plain,
    ( spl9_1
    | ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl9_1
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f19,f42,f145])).

fof(f145,plain,
    ( ! [X1] :
        ( sK0 = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl9_10 ),
    inference(resolution,[],[f135,f21])).

fof(f135,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0,sK0),X0)
        | sK0 = X0 )
    | ~ spl9_10 ),
    inference(resolution,[],[f94,f22])).

fof(f94,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f42,plain,
    ( k1_xboole_0 != sK0
    | spl9_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl9_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f133,plain,
    ( spl9_10
    | spl9_15
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f67,f59,f131,f93])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f64,f34])).

fof(f64,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK3) )
    | ~ spl9_5 ),
    inference(superposition,[],[f33,f61])).

fof(f129,plain,
    ( spl9_4
    | ~ spl9_14
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f124,f119,f126,f54])).

fof(f119,plain,
    ( spl9_13
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f124,plain,
    ( ~ r1_tarski(sK2,sK0)
    | sK0 = sK2
    | ~ spl9_13 ),
    inference(resolution,[],[f121,f26])).

fof(f121,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f122,plain,
    ( spl9_13
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f117,f72,f119])).

fof(f72,plain,
    ( spl9_7
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f117,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl9_7 ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl9_7 ),
    inference(resolution,[],[f87,f28])).

fof(f87,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(X3,sK2),sK0)
        | r1_tarski(X3,sK2) )
    | ~ spl9_7 ),
    inference(resolution,[],[f73,f29])).

fof(f73,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,
    ( spl9_6
    | spl9_7
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f66,f59,f72,f69])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f63,f34])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK2) )
    | ~ spl9_5 ),
    inference(superposition,[],[f32,f61])).

fof(f62,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f16,f59])).

fof(f16,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

% (9084)Refutation not found, incomplete strategy% (9084)------------------------------
% (9084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f10])).

% (9084)Termination reason: Refutation not found, incomplete strategy

% (9084)Memory used [KB]: 1663
fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

% (9084)Time elapsed: 0.125 s
% (9084)------------------------------
% (9084)------------------------------
fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f57,plain,
    ( ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f15,f54,f50])).

fof(f15,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    ~ spl9_2 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:10:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (9100)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.49  % (9085)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.20/0.51  % (9106)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.20/0.51  % (9095)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.20/0.51  % (9096)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.52  % (9098)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.20/0.52  % (9094)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.20/0.52  % (9094)Refutation not found, incomplete strategy% (9094)------------------------------
% 1.20/0.52  % (9094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (9094)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (9094)Memory used [KB]: 10618
% 1.20/0.52  % (9094)Time elapsed: 0.107 s
% 1.20/0.52  % (9094)------------------------------
% 1.20/0.52  % (9094)------------------------------
% 1.20/0.52  % (9090)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.20/0.53  % (9110)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.53  % (9102)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.53  % (9087)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.53  % (9110)Refutation not found, incomplete strategy% (9110)------------------------------
% 1.34/0.53  % (9110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (9095)Refutation not found, incomplete strategy% (9095)------------------------------
% 1.34/0.53  % (9095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (9095)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (9095)Memory used [KB]: 10618
% 1.34/0.53  % (9095)Time elapsed: 0.120 s
% 1.34/0.53  % (9095)------------------------------
% 1.34/0.53  % (9095)------------------------------
% 1.34/0.53  % (9110)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (9110)Memory used [KB]: 10746
% 1.34/0.53  % (9110)Time elapsed: 0.121 s
% 1.34/0.53  % (9110)------------------------------
% 1.34/0.53  % (9110)------------------------------
% 1.34/0.53  % (9084)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.53  % (9106)Refutation found. Thanks to Tanya!
% 1.34/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f354,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(avatar_sat_refutation,[],[f43,f48,f57,f62,f74,f122,f129,f133,f163,f172,f193,f238,f289,f300,f307,f311,f337,f353])).
% 1.34/0.53  fof(f353,plain,(
% 1.34/0.53    spl9_24 | ~spl9_26),
% 1.34/0.53    inference(avatar_split_clause,[],[f352,f335,f304])).
% 1.34/0.53  fof(f304,plain,(
% 1.34/0.53    spl9_24 <=> r1_tarski(sK3,sK1)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 1.34/0.53  fof(f335,plain,(
% 1.34/0.53    spl9_26 <=> ! [X6] : (~r2_hidden(X6,sK3) | r2_hidden(X6,sK1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 1.34/0.53  fof(f352,plain,(
% 1.34/0.53    r1_tarski(sK3,sK1) | ~spl9_26),
% 1.34/0.53    inference(duplicate_literal_removal,[],[f350])).
% 1.34/0.53  fof(f350,plain,(
% 1.34/0.53    r1_tarski(sK3,sK1) | r1_tarski(sK3,sK1) | ~spl9_26),
% 1.34/0.53    inference(resolution,[],[f343,f28])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f13])).
% 1.34/0.53  fof(f13,plain,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.34/0.53    inference(ennf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.34/0.53  fof(f343,plain,(
% 1.34/0.53    ( ! [X4] : (~r2_hidden(sK6(X4,sK1),sK3) | r1_tarski(X4,sK1)) ) | ~spl9_26),
% 1.34/0.53    inference(resolution,[],[f336,f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f13])).
% 1.34/0.53  fof(f336,plain,(
% 1.34/0.53    ( ! [X6] : (r2_hidden(X6,sK1) | ~r2_hidden(X6,sK3)) ) | ~spl9_26),
% 1.34/0.53    inference(avatar_component_clause,[],[f335])).
% 1.34/0.53  fof(f337,plain,(
% 1.34/0.53    spl9_26 | spl9_10 | ~spl9_4 | ~spl9_5),
% 1.34/0.53    inference(avatar_split_clause,[],[f331,f59,f54,f93,f335])).
% 1.34/0.53  fof(f93,plain,(
% 1.34/0.53    spl9_10 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.34/0.53  fof(f54,plain,(
% 1.34/0.53    spl9_4 <=> sK0 = sK2),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.34/0.53  fof(f59,plain,(
% 1.34/0.53    spl9_5 <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.34/0.53  fof(f331,plain,(
% 1.34/0.53    ( ! [X6,X7] : (~r2_hidden(X7,sK0) | ~r2_hidden(X6,sK3) | r2_hidden(X6,sK1)) ) | (~spl9_4 | ~spl9_5)),
% 1.34/0.53    inference(forward_demodulation,[],[f104,f55])).
% 1.34/0.53  fof(f55,plain,(
% 1.34/0.53    sK0 = sK2 | ~spl9_4),
% 1.34/0.53    inference(avatar_component_clause,[],[f54])).
% 1.34/0.53  fof(f104,plain,(
% 1.34/0.53    ( ! [X6,X7] : (~r2_hidden(X6,sK3) | ~r2_hidden(X7,sK2) | r2_hidden(X6,sK1)) ) | ~spl9_5),
% 1.34/0.53    inference(resolution,[],[f65,f33])).
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f6])).
% 1.34/0.53  fof(f6,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.34/0.53  fof(f65,plain,(
% 1.34/0.53    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) ) | ~spl9_5),
% 1.34/0.53    inference(superposition,[],[f34,f61])).
% 1.34/0.53  fof(f61,plain,(
% 1.34/0.53    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) | ~spl9_5),
% 1.34/0.53    inference(avatar_component_clause,[],[f59])).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f6])).
% 1.34/0.53  fof(f311,plain,(
% 1.34/0.53    spl9_14 | ~spl9_18),
% 1.34/0.53    inference(avatar_split_clause,[],[f310,f188,f126])).
% 1.34/0.53  fof(f126,plain,(
% 1.34/0.53    spl9_14 <=> r1_tarski(sK2,sK0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.34/0.53  fof(f188,plain,(
% 1.34/0.53    spl9_18 <=> ! [X5] : (~r2_hidden(X5,sK2) | r2_hidden(X5,sK0))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 1.34/0.53  fof(f310,plain,(
% 1.34/0.53    r1_tarski(sK2,sK0) | ~spl9_18),
% 1.34/0.53    inference(duplicate_literal_removal,[],[f308])).
% 1.34/0.53  fof(f308,plain,(
% 1.34/0.53    r1_tarski(sK2,sK0) | r1_tarski(sK2,sK0) | ~spl9_18),
% 1.34/0.53    inference(resolution,[],[f265,f28])).
% 1.34/0.53  fof(f265,plain,(
% 1.34/0.53    ( ! [X4] : (~r2_hidden(sK6(X4,sK0),sK2) | r1_tarski(X4,sK0)) ) | ~spl9_18),
% 1.34/0.53    inference(resolution,[],[f189,f29])).
% 1.34/0.53  fof(f189,plain,(
% 1.34/0.53    ( ! [X5] : (r2_hidden(X5,sK0) | ~r2_hidden(X5,sK2)) ) | ~spl9_18),
% 1.34/0.53    inference(avatar_component_clause,[],[f188])).
% 1.34/0.53  fof(f307,plain,(
% 1.34/0.53    spl9_3 | ~spl9_24 | ~spl9_23),
% 1.34/0.53    inference(avatar_split_clause,[],[f302,f297,f304,f50])).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    spl9_3 <=> sK1 = sK3),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.34/0.53  fof(f297,plain,(
% 1.34/0.53    spl9_23 <=> r1_tarski(sK1,sK3)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 1.34/0.53  fof(f302,plain,(
% 1.34/0.53    ~r1_tarski(sK3,sK1) | sK1 = sK3 | ~spl9_23),
% 1.34/0.53    inference(resolution,[],[f299,f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.53  fof(f299,plain,(
% 1.34/0.53    r1_tarski(sK1,sK3) | ~spl9_23),
% 1.34/0.53    inference(avatar_component_clause,[],[f297])).
% 1.34/0.53  fof(f300,plain,(
% 1.34/0.53    spl9_23 | ~spl9_15),
% 1.34/0.53    inference(avatar_split_clause,[],[f295,f131,f297])).
% 1.34/0.53  fof(f131,plain,(
% 1.34/0.53    spl9_15 <=> ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.34/0.53  fof(f295,plain,(
% 1.34/0.53    r1_tarski(sK1,sK3) | ~spl9_15),
% 1.34/0.53    inference(duplicate_literal_removal,[],[f294])).
% 1.34/0.53  fof(f294,plain,(
% 1.34/0.53    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl9_15),
% 1.34/0.53    inference(resolution,[],[f167,f28])).
% 1.34/0.53  fof(f167,plain,(
% 1.34/0.53    ( ! [X3] : (~r2_hidden(sK6(X3,sK3),sK1) | r1_tarski(X3,sK3)) ) | ~spl9_15),
% 1.34/0.53    inference(resolution,[],[f132,f29])).
% 1.34/0.53  fof(f132,plain,(
% 1.34/0.53    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) ) | ~spl9_15),
% 1.34/0.53    inference(avatar_component_clause,[],[f131])).
% 1.34/0.53  fof(f289,plain,(
% 1.34/0.53    spl9_2 | ~spl9_6),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f278])).
% 1.34/0.53  fof(f278,plain,(
% 1.34/0.53    $false | (spl9_2 | ~spl9_6)),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f19,f47,f272])).
% 1.34/0.53  fof(f272,plain,(
% 1.34/0.53    ( ! [X0] : (sK1 = X0 | ~v1_xboole_0(X0)) ) | ~spl9_6),
% 1.34/0.53    inference(resolution,[],[f179,f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.34/0.53  fof(f179,plain,(
% 1.34/0.53    ( ! [X0] : (r2_hidden(sK5(X0,sK1),X0) | sK1 = X0) ) | ~spl9_6),
% 1.34/0.53    inference(resolution,[],[f70,f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f12])).
% 1.34/0.53  fof(f12,plain,(
% 1.34/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.34/0.53    inference(ennf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.34/0.53  fof(f70,plain,(
% 1.34/0.53    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl9_6),
% 1.34/0.53    inference(avatar_component_clause,[],[f69])).
% 1.34/0.53  fof(f69,plain,(
% 1.34/0.53    spl9_6 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.34/0.53  fof(f47,plain,(
% 1.34/0.53    k1_xboole_0 != sK1 | spl9_2),
% 1.34/0.53    inference(avatar_component_clause,[],[f45])).
% 1.34/0.53  fof(f45,plain,(
% 1.34/0.53    spl9_2 <=> k1_xboole_0 = sK1),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    v1_xboole_0(k1_xboole_0)),
% 1.34/0.53    inference(cnf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    v1_xboole_0(k1_xboole_0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.34/0.53  fof(f238,plain,(
% 1.34/0.53    spl9_16 | ~spl9_19),
% 1.34/0.53    inference(avatar_split_clause,[],[f234,f191,f169])).
% 1.34/0.53  fof(f169,plain,(
% 1.34/0.53    spl9_16 <=> v1_xboole_0(sK3)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.34/0.53  fof(f191,plain,(
% 1.34/0.53    spl9_19 <=> ! [X4] : ~r2_hidden(X4,sK3)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 1.34/0.53  fof(f234,plain,(
% 1.34/0.53    v1_xboole_0(sK3) | ~spl9_19),
% 1.34/0.53    inference(resolution,[],[f192,f20])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f1])).
% 1.34/0.53  fof(f192,plain,(
% 1.34/0.53    ( ! [X4] : (~r2_hidden(X4,sK3)) ) | ~spl9_19),
% 1.34/0.53    inference(avatar_component_clause,[],[f191])).
% 1.34/0.53  fof(f193,plain,(
% 1.34/0.53    spl9_18 | spl9_19 | ~spl9_5),
% 1.34/0.53    inference(avatar_split_clause,[],[f103,f59,f191,f188])).
% 1.34/0.53  fof(f103,plain,(
% 1.34/0.53    ( ! [X4,X5] : (~r2_hidden(X4,sK3) | ~r2_hidden(X5,sK2) | r2_hidden(X5,sK0)) ) | ~spl9_5),
% 1.34/0.53    inference(resolution,[],[f65,f32])).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f6])).
% 1.34/0.53  fof(f172,plain,(
% 1.34/0.53    ~spl9_16 | spl9_6 | ~spl9_15),
% 1.34/0.53    inference(avatar_split_clause,[],[f164,f131,f69,f169])).
% 1.34/0.53  fof(f164,plain,(
% 1.34/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(sK3)) ) | ~spl9_15),
% 1.34/0.53    inference(resolution,[],[f132,f21])).
% 1.34/0.53  fof(f163,plain,(
% 1.34/0.53    spl9_1 | ~spl9_10),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f149])).
% 1.34/0.53  fof(f149,plain,(
% 1.34/0.53    $false | (spl9_1 | ~spl9_10)),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f19,f42,f145])).
% 1.34/0.53  fof(f145,plain,(
% 1.34/0.53    ( ! [X1] : (sK0 = X1 | ~v1_xboole_0(X1)) ) | ~spl9_10),
% 1.34/0.53    inference(resolution,[],[f135,f21])).
% 1.34/0.53  fof(f135,plain,(
% 1.34/0.53    ( ! [X0] : (r2_hidden(sK5(X0,sK0),X0) | sK0 = X0) ) | ~spl9_10),
% 1.34/0.53    inference(resolution,[],[f94,f22])).
% 1.34/0.53  fof(f94,plain,(
% 1.34/0.53    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl9_10),
% 1.34/0.53    inference(avatar_component_clause,[],[f93])).
% 1.34/0.53  fof(f42,plain,(
% 1.34/0.53    k1_xboole_0 != sK0 | spl9_1),
% 1.34/0.53    inference(avatar_component_clause,[],[f40])).
% 1.34/0.53  fof(f40,plain,(
% 1.34/0.53    spl9_1 <=> k1_xboole_0 = sK0),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.34/0.53  fof(f133,plain,(
% 1.34/0.53    spl9_10 | spl9_15 | ~spl9_5),
% 1.34/0.53    inference(avatar_split_clause,[],[f67,f59,f131,f93])).
% 1.34/0.53  fof(f67,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl9_5),
% 1.34/0.53    inference(resolution,[],[f64,f34])).
% 1.34/0.53  fof(f64,plain,(
% 1.34/0.53    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK3)) ) | ~spl9_5),
% 1.34/0.53    inference(superposition,[],[f33,f61])).
% 1.34/0.53  fof(f129,plain,(
% 1.34/0.53    spl9_4 | ~spl9_14 | ~spl9_13),
% 1.34/0.53    inference(avatar_split_clause,[],[f124,f119,f126,f54])).
% 1.34/0.53  fof(f119,plain,(
% 1.34/0.53    spl9_13 <=> r1_tarski(sK0,sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.34/0.53  fof(f124,plain,(
% 1.34/0.53    ~r1_tarski(sK2,sK0) | sK0 = sK2 | ~spl9_13),
% 1.34/0.53    inference(resolution,[],[f121,f26])).
% 1.34/0.53  fof(f121,plain,(
% 1.34/0.53    r1_tarski(sK0,sK2) | ~spl9_13),
% 1.34/0.53    inference(avatar_component_clause,[],[f119])).
% 1.34/0.53  fof(f122,plain,(
% 1.34/0.53    spl9_13 | ~spl9_7),
% 1.34/0.53    inference(avatar_split_clause,[],[f117,f72,f119])).
% 1.34/0.53  fof(f72,plain,(
% 1.34/0.53    spl9_7 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.34/0.53  fof(f117,plain,(
% 1.34/0.53    r1_tarski(sK0,sK2) | ~spl9_7),
% 1.34/0.53    inference(duplicate_literal_removal,[],[f116])).
% 1.34/0.53  fof(f116,plain,(
% 1.34/0.53    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl9_7),
% 1.34/0.53    inference(resolution,[],[f87,f28])).
% 1.34/0.53  fof(f87,plain,(
% 1.34/0.53    ( ! [X3] : (~r2_hidden(sK6(X3,sK2),sK0) | r1_tarski(X3,sK2)) ) | ~spl9_7),
% 1.34/0.53    inference(resolution,[],[f73,f29])).
% 1.34/0.53  fof(f73,plain,(
% 1.34/0.53    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl9_7),
% 1.34/0.53    inference(avatar_component_clause,[],[f72])).
% 1.34/0.53  fof(f74,plain,(
% 1.34/0.53    spl9_6 | spl9_7 | ~spl9_5),
% 1.34/0.53    inference(avatar_split_clause,[],[f66,f59,f72,f69])).
% 1.34/0.53  fof(f66,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl9_5),
% 1.34/0.53    inference(resolution,[],[f63,f34])).
% 1.34/0.53  fof(f63,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK2)) ) | ~spl9_5),
% 1.34/0.53    inference(superposition,[],[f32,f61])).
% 1.34/0.53  fof(f62,plain,(
% 1.34/0.53    spl9_5),
% 1.34/0.53    inference(avatar_split_clause,[],[f16,f59])).
% 1.34/0.53  fof(f16,plain,(
% 1.34/0.53    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  % (9084)Refutation not found, incomplete strategy% (9084)------------------------------
% 1.34/0.53  % (9084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  fof(f11,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.34/0.53    inference(flattening,[],[f10])).
% 1.34/0.53  % (9084)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (9084)Memory used [KB]: 1663
% 1.34/0.53  fof(f10,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f9])).
% 1.34/0.53  % (9084)Time elapsed: 0.125 s
% 1.34/0.53  % (9084)------------------------------
% 1.34/0.53  % (9084)------------------------------
% 1.34/0.53  fof(f9,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.34/0.53    inference(negated_conjecture,[],[f8])).
% 1.34/0.53  fof(f8,conjecture,(
% 1.34/0.53    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.34/0.53  fof(f57,plain,(
% 1.34/0.53    ~spl9_3 | ~spl9_4),
% 1.34/0.53    inference(avatar_split_clause,[],[f15,f54,f50])).
% 1.34/0.53  fof(f15,plain,(
% 1.34/0.53    sK0 != sK2 | sK1 != sK3),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  fof(f48,plain,(
% 1.34/0.53    ~spl9_2),
% 1.34/0.53    inference(avatar_split_clause,[],[f18,f45])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    k1_xboole_0 != sK1),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  fof(f43,plain,(
% 1.34/0.53    ~spl9_1),
% 1.34/0.53    inference(avatar_split_clause,[],[f17,f40])).
% 1.34/0.53  fof(f17,plain,(
% 1.34/0.53    k1_xboole_0 != sK0),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (9106)------------------------------
% 1.34/0.53  % (9106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (9106)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (9106)Memory used [KB]: 10874
% 1.34/0.53  % (9106)Time elapsed: 0.085 s
% 1.34/0.53  % (9106)------------------------------
% 1.34/0.53  % (9106)------------------------------
% 1.34/0.53  % (9088)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.53  % (9083)Success in time 0.175 s
%------------------------------------------------------------------------------

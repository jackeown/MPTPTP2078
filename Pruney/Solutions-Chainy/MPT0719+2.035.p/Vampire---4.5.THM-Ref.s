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
% DateTime   : Thu Dec  3 12:55:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 117 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :  240 ( 328 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f55,f59,f67,f71,f75,f83,f93,f101,f117,f127,f134])).

fof(f134,plain,
    ( ~ spl6_10
    | ~ spl6_14
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_14
    | spl6_19 ),
    inference(subsumption_resolution,[],[f131,f92])).

fof(f92,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_14
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f131,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl6_10
    | spl6_19 ),
    inference(resolution,[],[f116,f74])).

fof(f74,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | r2_hidden(sK2(X0),X0) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_10
  <=> ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f116,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_19
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f127,plain,
    ( ~ spl6_4
    | ~ spl6_8
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_8
    | spl6_18 ),
    inference(subsumption_resolution,[],[f124,f50])).

fof(f50,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl6_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f124,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_8
    | spl6_18 ),
    inference(resolution,[],[f113,f66])).

fof(f66,plain,
    ( ! [X0] :
        ( v1_funct_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl6_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f113,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_18
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f117,plain,
    ( ~ spl6_18
    | ~ spl6_19
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f106,f99,f91,f57,f45,f41,f37,f115,f112])).

fof(f37,plain,
    ( spl6_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f41,plain,
    ( spl6_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f45,plain,
    ( spl6_3
  <=> v5_funct_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f57,plain,
    ( spl6_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f99,plain,
    ( spl6_16
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
        | v5_funct_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f106,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f105,f92])).

fof(f105,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f104,f58])).

fof(f58,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f104,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f103,f38])).

fof(f38,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f103,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f102,f42])).

fof(f42,plain,
    ( v1_funct_1(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f102,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | spl6_3
    | ~ spl6_16 ),
    inference(resolution,[],[f100,f46])).

fof(f46,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( v5_funct_1(X1,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f29,f99])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | v5_funct_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f93,plain,
    ( spl6_14
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f85,f81,f69,f53,f91])).

fof(f53,plain,
    ( spl6_5
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f69,plain,
    ( spl6_9
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f81,plain,
    ( spl6_12
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f85,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f84,f54])).

fof(f54,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(superposition,[],[f82,f70])).

fof(f70,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f34,f81])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f75,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f71,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f26,f69])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f67,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f59,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f55,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f51,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f47,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

fof(f43,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (23312)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.41  % (23312)Refutation not found, incomplete strategy% (23312)------------------------------
% 0.20/0.41  % (23312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (23312)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (23312)Memory used [KB]: 1663
% 0.20/0.41  % (23312)Time elapsed: 0.003 s
% 0.20/0.41  % (23312)------------------------------
% 0.20/0.41  % (23312)------------------------------
% 0.20/0.44  % (23308)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.44  % (23308)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f135,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f55,f59,f67,f71,f75,f83,f93,f101,f117,f127,f134])).
% 0.20/0.44  fof(f134,plain,(
% 0.20/0.44    ~spl6_10 | ~spl6_14 | spl6_19),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f133])).
% 0.20/0.44  fof(f133,plain,(
% 0.20/0.44    $false | (~spl6_10 | ~spl6_14 | spl6_19)),
% 0.20/0.44    inference(subsumption_resolution,[],[f131,f92])).
% 0.20/0.44  fof(f92,plain,(
% 0.20/0.44    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_14),
% 0.20/0.44    inference(avatar_component_clause,[],[f91])).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    spl6_14 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.44  fof(f131,plain,(
% 0.20/0.44    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | (~spl6_10 | spl6_19)),
% 0.20/0.44    inference(resolution,[],[f116,f74])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK2(X0),X0)) ) | ~spl6_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f73])).
% 0.20/0.44  fof(f73,plain,(
% 0.20/0.44    spl6_10 <=> ! [X0] : (r2_hidden(sK2(X0),X0) | v1_relat_1(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.44  fof(f116,plain,(
% 0.20/0.44    ~v1_relat_1(k1_xboole_0) | spl6_19),
% 0.20/0.44    inference(avatar_component_clause,[],[f115])).
% 0.20/0.44  fof(f115,plain,(
% 0.20/0.44    spl6_19 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.44  fof(f127,plain,(
% 0.20/0.44    ~spl6_4 | ~spl6_8 | spl6_18),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f126])).
% 0.20/0.44  fof(f126,plain,(
% 0.20/0.44    $false | (~spl6_4 | ~spl6_8 | spl6_18)),
% 0.20/0.44    inference(subsumption_resolution,[],[f124,f50])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0) | ~spl6_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f49])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    spl6_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.44  fof(f124,plain,(
% 0.20/0.44    ~v1_xboole_0(k1_xboole_0) | (~spl6_8 | spl6_18)),
% 0.20/0.44    inference(resolution,[],[f113,f66])).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) ) | ~spl6_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f65])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    spl6_8 <=> ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.44  fof(f113,plain,(
% 0.20/0.44    ~v1_funct_1(k1_xboole_0) | spl6_18),
% 0.20/0.44    inference(avatar_component_clause,[],[f112])).
% 0.20/0.44  fof(f112,plain,(
% 0.20/0.44    spl6_18 <=> v1_funct_1(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.44  fof(f117,plain,(
% 0.20/0.44    ~spl6_18 | ~spl6_19 | ~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | ~spl6_14 | ~spl6_16),
% 0.20/0.44    inference(avatar_split_clause,[],[f106,f99,f91,f57,f45,f41,f37,f115,f112])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    spl6_1 <=> v1_relat_1(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    spl6_2 <=> v1_funct_1(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    spl6_3 <=> v5_funct_1(k1_xboole_0,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    spl6_6 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.44  fof(f99,plain,(
% 0.20/0.44    spl6_16 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | v5_funct_1(X1,X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.44  fof(f106,plain,(
% 0.20/0.44    ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | ~spl6_14 | ~spl6_16)),
% 0.20/0.44    inference(subsumption_resolution,[],[f105,f92])).
% 0.20/0.44  fof(f105,plain,(
% 0.20/0.44    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | ~spl6_16)),
% 0.20/0.44    inference(forward_demodulation,[],[f104,f58])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f57])).
% 0.20/0.44  fof(f104,plain,(
% 0.20/0.44    ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_16)),
% 0.20/0.44    inference(subsumption_resolution,[],[f103,f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    v1_relat_1(sK0) | ~spl6_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f37])).
% 0.20/0.44  fof(f103,plain,(
% 0.20/0.44    ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0) | (~spl6_2 | spl6_3 | ~spl6_16)),
% 0.20/0.44    inference(subsumption_resolution,[],[f102,f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    v1_funct_1(sK0) | ~spl6_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f41])).
% 0.20/0.44  fof(f102,plain,(
% 0.20/0.44    ~v1_funct_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0) | (spl6_3 | ~spl6_16)),
% 0.20/0.44    inference(resolution,[],[f100,f46])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    ~v5_funct_1(k1_xboole_0,sK0) | spl6_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f45])).
% 0.20/0.44  fof(f100,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v5_funct_1(X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_relat_1(X0)) ) | ~spl6_16),
% 0.20/0.44    inference(avatar_component_clause,[],[f99])).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    spl6_16),
% 0.20/0.44    inference(avatar_split_clause,[],[f29,f99])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | v5_funct_1(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).
% 0.20/0.44  fof(f93,plain,(
% 0.20/0.44    spl6_14 | ~spl6_5 | ~spl6_9 | ~spl6_12),
% 0.20/0.44    inference(avatar_split_clause,[],[f85,f81,f69,f53,f91])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    spl6_5 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    spl6_9 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.44  fof(f81,plain,(
% 0.20/0.44    spl6_12 <=> ! [X1,X0,X2] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.44  fof(f85,plain,(
% 0.20/0.44    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl6_5 | ~spl6_9 | ~spl6_12)),
% 0.20/0.44    inference(subsumption_resolution,[],[f84,f54])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl6_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f53])).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) ) | (~spl6_9 | ~spl6_12)),
% 0.20/0.44    inference(superposition,[],[f82,f70])).
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl6_9),
% 0.20/0.44    inference(avatar_component_clause,[],[f69])).
% 0.20/0.44  fof(f82,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl6_12),
% 0.20/0.44    inference(avatar_component_clause,[],[f81])).
% 0.20/0.44  fof(f83,plain,(
% 0.20/0.44    spl6_12),
% 0.20/0.44    inference(avatar_split_clause,[],[f34,f81])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(rectify,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    spl6_10),
% 0.20/0.44    inference(avatar_split_clause,[],[f32,f73])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    spl6_9),
% 0.20/0.44    inference(avatar_split_clause,[],[f26,f69])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    spl6_8),
% 0.20/0.44    inference(avatar_split_clause,[],[f27,f65])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    spl6_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f23,f57])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    spl6_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f25,f53])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    spl6_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f22,f49])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    ~spl6_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f21,f45])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,negated_conjecture,(
% 0.20/0.44    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.20/0.44    inference(negated_conjecture,[],[f9])).
% 0.20/0.44  fof(f9,conjecture,(
% 0.20/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    spl6_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f20,f41])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    v1_funct_1(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    spl6_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f19,f37])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    v1_relat_1(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (23308)------------------------------
% 0.20/0.44  % (23308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (23308)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (23308)Memory used [KB]: 10618
% 0.20/0.44  % (23308)Time elapsed: 0.036 s
% 0.20/0.44  % (23308)------------------------------
% 0.20/0.44  % (23308)------------------------------
% 0.20/0.45  % (23298)Success in time 0.091 s
%------------------------------------------------------------------------------

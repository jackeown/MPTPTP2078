%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : compts_1__t27_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:51 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   69 (  98 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  159 ( 263 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f76,f83,f90,f97,f104,f111,f118,f133,f136,f142])).

fof(f142,plain,
    ( ~ spl4_0
    | ~ spl4_2
    | spl4_5
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f140,f75])).

fof(f75,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f140,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_0
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f139,f82])).

fof(f82,plain,
    ( ~ v1_compts_1(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_5
  <=> ~ v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f139,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_0
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f138,f68])).

fof(f68,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f138,plain,
    ( ~ v2_pre_topc(sK0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_16 ),
    inference(resolution,[],[f51,f126])).

fof(f126,plain,
    ( v8_struct_0(sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_16
  <=> v8_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v8_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
        & v2_pre_topc(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
        & v2_pre_topc(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v8_struct_0(X0) )
       => ( v1_compts_1(X0)
          & v2_pre_topc(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t27_compts_1.p',cc3_compts_1)).

fof(f136,plain,
    ( ~ spl4_2
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f134,f75])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_19 ),
    inference(resolution,[],[f132,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t27_compts_1.p',dt_l1_pre_topc)).

fof(f132,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_19
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f133,plain,
    ( spl4_16
    | ~ spl4_19
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f120,f109,f131,f125])).

fof(f109,plain,
    ( spl4_12
  <=> v1_finset_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f120,plain,
    ( ~ l1_struct_0(sK0)
    | v8_struct_0(sK0)
    | ~ spl4_12 ),
    inference(resolution,[],[f53,f110])).

fof(f110,plain,
    ( v1_finset_1(u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v8_struct_0(X0) )
     => ~ v1_finset_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t27_compts_1.p',fc9_struct_0)).

fof(f118,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f48,f116])).

fof(f116,plain,
    ( spl4_14
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f48,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t27_compts_1.p',d2_xboole_0)).

fof(f111,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f45,f109])).

fof(f45,plain,(
    v1_finset_1(u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ v1_compts_1(sK0)
    & v1_finset_1(u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ~ v1_compts_1(X0)
        & v1_finset_1(u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ~ v1_compts_1(sK0)
      & v1_finset_1(u1_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ~ v1_compts_1(X0)
      & v1_finset_1(u1_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ~ v1_compts_1(X0)
      & v1_finset_1(u1_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( v1_finset_1(u1_struct_0(X0))
         => v1_compts_1(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_finset_1(u1_struct_0(X0))
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t27_compts_1.p',t27_compts_1)).

fof(f104,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f62,f102])).

fof(f102,plain,
    ( spl4_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f47,f48])).

fof(f47,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t27_compts_1.p',dt_o_0_0_xboole_0)).

fof(f97,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f61,f95])).

fof(f95,plain,
    ( spl4_8
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f61,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f41])).

fof(f41,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK3) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t27_compts_1.p',existence_l1_pre_topc)).

fof(f90,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f60,f88])).

fof(f88,plain,
    ( spl4_6
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f60,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    l1_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f39])).

fof(f39,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK2) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t27_compts_1.p',existence_l1_struct_0)).

fof(f83,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f46,plain,(
    ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f44,f74])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f43,f67])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------

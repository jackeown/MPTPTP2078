%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t8_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:20 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 360 expanded)
%              Number of leaves         :   47 ( 151 expanded)
%              Depth                    :   10
%              Number of atoms          :  388 ( 823 expanded)
%              Number of equality atoms :   20 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f73,f80,f87,f94,f104,f112,f136,f145,f152,f162,f177,f191,f200,f228,f241,f257,f266,f273,f280,f307,f323,f340,f359,f368,f381,f390,f397])).

fof(f397,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f395,f93])).

fof(f93,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_9
  <=> ~ r1_tarski(k1_setfam_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f395,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK2)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f391,f79])).

fof(f79,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_4
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r1_tarski(k1_setfam_1(sK1),X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f124,f72])).

fof(f72,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f124,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | r1_tarski(k1_setfam_1(X3),X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f57,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t4_setfam_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t1_xboole_1)).

fof(f390,plain,
    ( ~ spl4_61
    | ~ spl4_46
    | spl4_59 ),
    inference(avatar_split_clause,[],[f382,f379,f321,f388])).

fof(f388,plain,
    ( spl4_61
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f321,plain,
    ( spl4_46
  <=> k1_xboole_0 = k1_zfmisc_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f379,plain,
    ( spl4_59
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f382,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),sK2)
    | ~ spl4_46
    | ~ spl4_59 ),
    inference(resolution,[],[f380,f326])).

fof(f326,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k1_xboole_0)
        | ~ r1_tarski(X1,sK2) )
    | ~ spl4_46 ),
    inference(superposition,[],[f53,f322])).

fof(f322,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK2)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f321])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t3_subset)).

fof(f380,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f379])).

fof(f381,plain,
    ( spl4_56
    | ~ spl4_59
    | ~ spl4_30
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f332,f321,f226,f379,f373])).

fof(f373,plain,
    ( spl4_56
  <=> m1_subset_1(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f226,plain,
    ( spl4_30
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f332,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | m1_subset_1(k1_xboole_0,sK2)
    | ~ spl4_30
    | ~ spl4_46 ),
    inference(superposition,[],[f232,f322])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0))
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl4_30 ),
    inference(resolution,[],[f227,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t4_subset)).

fof(f227,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f226])).

fof(f368,plain,
    ( ~ spl4_55
    | ~ spl4_46
    | spl4_53 ),
    inference(avatar_split_clause,[],[f360,f357,f321,f366])).

fof(f366,plain,
    ( spl4_55
  <=> ~ r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f357,plain,
    ( spl4_53
  <=> ~ m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f360,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl4_46
    | ~ spl4_53 ),
    inference(resolution,[],[f358,f326])).

fof(f358,plain,
    ( ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f357])).

fof(f359,plain,
    ( spl4_50
    | ~ spl4_53
    | ~ spl4_2
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f330,f321,f71,f357,f351])).

fof(f351,plain,
    ( spl4_50
  <=> m1_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f330,plain,
    ( ~ m1_subset_1(sK1,k1_xboole_0)
    | m1_subset_1(sK0,sK2)
    | ~ spl4_2
    | ~ spl4_46 ),
    inference(superposition,[],[f204,f322])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(sK0,X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f56,f72])).

fof(f340,plain,
    ( spl4_48
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f327,f321,f338])).

fof(f338,plain,
    ( spl4_48
  <=> r1_tarski(sK3(k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f327,plain,
    ( r1_tarski(sK3(k1_xboole_0),sK2)
    | ~ spl4_46 ),
    inference(superposition,[],[f113,f322])).

fof(f113,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f52,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',existence_m1_subset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f323,plain,
    ( spl4_46
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f313,f299,f175,f160,f321])).

fof(f160,plain,
    ( spl4_20
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f175,plain,
    ( spl4_22
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f299,plain,
    ( spl4_42
  <=> v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f313,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK2)
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f308,f176])).

fof(f176,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f175])).

fof(f308,plain,
    ( k1_zfmisc_1(sK2) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_42 ),
    inference(resolution,[],[f300,f164])).

fof(f164,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl4_20 ),
    inference(resolution,[],[f161,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t8_boole)).

fof(f161,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f300,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f299])).

fof(f307,plain,
    ( spl4_42
    | spl4_44
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f292,f78,f305,f299])).

fof(f305,plain,
    ( spl4_44
  <=> r2_hidden(sK0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f292,plain,
    ( r2_hidden(sK0,k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl4_4 ),
    inference(resolution,[],[f119,f79])).

fof(f119,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,X3)
      | r2_hidden(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f51,f53])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t2_subset)).

fof(f280,plain,
    ( spl4_40
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f247,f239,f175,f160,f278])).

fof(f278,plain,
    ( spl4_40
  <=> k1_setfam_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f239,plain,
    ( spl4_32
  <=> v1_xboole_0(k1_setfam_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f247,plain,
    ( k1_setfam_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | ~ spl4_20
    | ~ spl4_22
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f242,f176])).

fof(f242,plain,
    ( k1_setfam_1(k1_zfmisc_1(k1_xboole_0)) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_32 ),
    inference(resolution,[],[f240,f164])).

fof(f240,plain,
    ( v1_xboole_0(k1_setfam_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f239])).

fof(f273,plain,
    ( ~ spl4_39
    | spl4_35 ),
    inference(avatar_split_clause,[],[f259,f255,f271])).

fof(f271,plain,
    ( spl4_39
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f255,plain,
    ( spl4_35
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f259,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_35 ),
    inference(resolution,[],[f256,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t1_subset)).

fof(f256,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f255])).

fof(f266,plain,
    ( ~ spl4_37
    | spl4_35 ),
    inference(avatar_split_clause,[],[f258,f255,f264])).

fof(f264,plain,
    ( spl4_37
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f258,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_35 ),
    inference(resolution,[],[f256,f53])).

fof(f257,plain,
    ( ~ spl4_35
    | ~ spl4_0
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f233,f226,f64,f255])).

fof(f64,plain,
    ( spl4_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f233,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_30 ),
    inference(resolution,[],[f227,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_0 ),
    inference(resolution,[],[f58,f65])).

fof(f65,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f64])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t5_subset)).

fof(f241,plain,
    ( spl4_32
    | ~ spl4_0
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f229,f226,f64,f239])).

fof(f229,plain,
    ( v1_xboole_0(k1_setfam_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_0
    | ~ spl4_30 ),
    inference(resolution,[],[f227,f167])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | v1_xboole_0(k1_setfam_1(X0)) )
    | ~ spl4_0 ),
    inference(resolution,[],[f154,f50])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl4_0 ),
    inference(resolution,[],[f129,f53])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl4_0 ),
    inference(resolution,[],[f127,f117])).

fof(f117,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f51,f47])).

fof(f228,plain,
    ( spl4_28
    | spl4_30
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f183,f175,f226,f220])).

fof(f220,plain,
    ( spl4_28
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f183,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(superposition,[],[f117,f176])).

fof(f200,plain,
    ( spl4_26
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f184,f175,f198])).

fof(f198,plain,
    ( spl4_26
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f184,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(superposition,[],[f47,f176])).

fof(f191,plain,
    ( spl4_24
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f181,f175,f189])).

fof(f189,plain,
    ( spl4_24
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f181,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_22 ),
    inference(superposition,[],[f113,f176])).

fof(f177,plain,
    ( spl4_22
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f166,f160,f175])).

fof(f166,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(resolution,[],[f161,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t6_boole)).

fof(f162,plain,
    ( spl4_20
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f153,f64,f160])).

fof(f153,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_0 ),
    inference(resolution,[],[f129,f47])).

fof(f152,plain,
    ( ~ spl4_19
    | spl4_15 ),
    inference(avatar_split_clause,[],[f138,f134,f150])).

fof(f150,plain,
    ( spl4_19
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f134,plain,
    ( spl4_15
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f138,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_15 ),
    inference(resolution,[],[f135,f49])).

fof(f135,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f145,plain,
    ( ~ spl4_17
    | spl4_15 ),
    inference(avatar_split_clause,[],[f137,f134,f143])).

fof(f143,plain,
    ( spl4_17
  <=> ~ r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f137,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_15 ),
    inference(resolution,[],[f135,f53])).

fof(f136,plain,
    ( ~ spl4_15
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f128,f71,f64,f134])).

fof(f128,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(resolution,[],[f127,f72])).

fof(f112,plain,
    ( ~ spl4_13
    | spl4_9 ),
    inference(avatar_split_clause,[],[f105,f92,f110])).

fof(f110,plain,
    ( spl4_13
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f105,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl4_9 ),
    inference(resolution,[],[f50,f93])).

fof(f104,plain,
    ( ~ spl4_11
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f97,f71,f102])).

fof(f102,plain,
    ( spl4_11
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f97,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f48,f72])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',antisymmetry_r2_hidden)).

fof(f94,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f43,f92])).

fof(f43,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),sK2)
    & r1_tarski(sK0,sK2)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k1_setfam_1(X1),X2)
        & r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),sK2)
      & r1_tarski(sK0,sK2)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t8_setfam_1)).

fof(f87,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f45,f85])).

fof(f85,plain,
    ( spl4_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f45,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',d2_xboole_0)).

fof(f80,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f42,f78])).

fof(f42,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f71])).

fof(f41,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f59,f64])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f44,f45])).

fof(f44,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------

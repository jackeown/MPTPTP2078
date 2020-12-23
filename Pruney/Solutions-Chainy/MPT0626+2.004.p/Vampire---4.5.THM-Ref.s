%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 230 expanded)
%              Number of leaves         :   30 ( 108 expanded)
%              Depth                    :    8
%              Number of atoms          :  349 ( 730 expanded)
%              Number of equality atoms :   25 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f66,f71,f72,f86,f120,f161,f194,f224,f232,f251,f259,f289,f297,f303,f315,f316,f333,f357,f369,f370,f376])).

% (31999)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f376,plain,
    ( spl4_5
    | ~ spl4_6
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f375,f229,f218,f63,f59])).

% (32000)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f59,plain,
    ( spl4_5
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f63,plain,
    ( spl4_6
  <=> r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f218,plain,
    ( spl4_31
  <=> ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK0),X0)
        | r2_hidden(sK0,k10_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f229,plain,
    ( spl4_33
  <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f375,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl4_6
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f371,f231])).

fof(f231,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f229])).

fof(f371,plain,
    ( r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1)))
    | ~ spl4_6
    | ~ spl4_31 ),
    inference(resolution,[],[f65,f219])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK0),X0)
        | r2_hidden(sK0,k10_relat_1(sK2,X0)) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f218])).

fof(f65,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f370,plain,
    ( k1_funct_1(sK2,sK0) != sK3(sK0,k1_relat_1(sK1),sK2)
    | k1_funct_1(sK2,sK0) != sK3(sK0,k2_relat_1(sK2),sK2)
    | r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ r2_hidden(sK3(sK0,k1_relat_1(sK1),sK2),k1_relat_1(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f369,plain,
    ( ~ spl4_4
    | spl4_54
    | ~ spl4_3
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f359,f354,f49,f366,f54])).

fof(f54,plain,
    ( spl4_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f366,plain,
    ( spl4_54
  <=> k1_funct_1(sK2,sK0) = sK3(sK0,k1_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f49,plain,
    ( spl4_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f354,plain,
    ( spl4_52
  <=> r2_hidden(k4_tarski(sK0,sK3(sK0,k1_relat_1(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f359,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK0) = sK3(sK0,k1_relat_1(sK1),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_52 ),
    inference(resolution,[],[f356,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

% (31988)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f356,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK0,k1_relat_1(sK1),sK2)),sK2)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f354])).

fof(f357,plain,
    ( spl4_52
    | ~ spl4_5
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f352,f249,f59,f354])).

fof(f249,plain,
    ( spl4_36
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,sK1)))
        | r2_hidden(k4_tarski(X1,sK3(X1,k1_relat_1(sK1),sK2)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f352,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK0,k1_relat_1(sK1),sK2)),sK2)
    | ~ spl4_5
    | ~ spl4_36 ),
    inference(resolution,[],[f250,f61])).

fof(f61,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f250,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,sK1)))
        | r2_hidden(k4_tarski(X1,sK3(X1,k1_relat_1(sK1),sK2)),sK2) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f249])).

fof(f333,plain,
    ( spl4_48
    | ~ spl4_5
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f328,f257,f59,f330])).

fof(f330,plain,
    ( spl4_48
  <=> r2_hidden(sK3(sK0,k1_relat_1(sK1),sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f257,plain,
    ( spl4_38
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k5_relat_1(sK2,sK1)))
        | r2_hidden(sK3(X3,k1_relat_1(sK1),sK2),k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f328,plain,
    ( r2_hidden(sK3(sK0,k1_relat_1(sK1),sK2),k1_relat_1(sK1))
    | ~ spl4_5
    | ~ spl4_38 ),
    inference(resolution,[],[f258,f61])).

fof(f258,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k5_relat_1(sK2,sK1)))
        | r2_hidden(sK3(X3,k1_relat_1(sK1),sK2),k1_relat_1(sK1)) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f257])).

fof(f316,plain,
    ( k1_funct_1(sK2,sK0) != sK3(sK0,k2_relat_1(sK2),sK2)
    | r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | ~ r2_hidden(sK3(sK0,k2_relat_1(sK2),sK2),k2_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f315,plain,
    ( ~ spl4_4
    | spl4_46
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f305,f293,f49,f312,f54])).

fof(f312,plain,
    ( spl4_46
  <=> k1_funct_1(sK2,sK0) = sK3(sK0,k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f293,plain,
    ( spl4_44
  <=> r2_hidden(k4_tarski(sK0,sK3(sK0,k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f305,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK0) = sK3(sK0,k2_relat_1(sK2),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_44 ),
    inference(resolution,[],[f295,f35])).

fof(f295,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK0,k2_relat_1(sK2),sK2)),sK2)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f293])).

fof(f303,plain,
    ( spl4_44
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f300,f159,f68,f293])).

fof(f68,plain,
    ( spl4_7
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f159,plain,
    ( spl4_20
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,sK3(X1,k2_relat_1(sK2),sK2)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f300,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK0,k2_relat_1(sK2),sK2)),sK2)
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(resolution,[],[f70,f160])).

fof(f160,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,sK3(X1,k2_relat_1(sK2),sK2)),sK2) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f159])).

fof(f70,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f297,plain,
    ( spl4_7
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f290,f229,f59,f54,f68])).

fof(f290,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_33 ),
    inference(resolution,[],[f238,f61])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK1)))
        | r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl4_4
    | ~ spl4_33 ),
    inference(superposition,[],[f88,f231])).

fof(f88,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k10_relat_1(sK2,X3))
        | r2_hidden(X2,k1_relat_1(sK2)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f29,f74])).

fof(f74,plain,
    ( ! [X1] : r1_tarski(k10_relat_1(sK2,X1),k1_relat_1(sK2))
    | ~ spl4_4 ),
    inference(resolution,[],[f28,f56])).

fof(f56,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f289,plain,
    ( spl4_43
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f284,f111,f68,f286])).

fof(f286,plain,
    ( spl4_43
  <=> r2_hidden(sK3(sK0,k2_relat_1(sK2),sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f111,plain,
    ( spl4_13
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | r2_hidden(sK3(X1,k2_relat_1(sK2),sK2),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f284,plain,
    ( r2_hidden(sK3(sK0,k2_relat_1(sK2),sK2),k2_relat_1(sK2))
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(resolution,[],[f112,f70])).

fof(f112,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | r2_hidden(sK3(X1,k2_relat_1(sK2),sK2),k2_relat_1(sK2)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f111])).

fof(f259,plain,
    ( ~ spl4_4
    | spl4_38
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f242,f229,f257,f54])).

fof(f242,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k5_relat_1(sK2,sK1)))
        | r2_hidden(sK3(X3,k1_relat_1(sK1),sK2),k1_relat_1(sK1))
        | ~ v1_relat_1(sK2) )
    | ~ spl4_33 ),
    inference(superposition,[],[f32,f231])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f251,plain,
    ( ~ spl4_4
    | spl4_36
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f240,f229,f249,f54])).

fof(f240,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,sK1)))
        | r2_hidden(k4_tarski(X1,sK3(X1,k1_relat_1(sK1),sK2)),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_33 ),
    inference(superposition,[],[f31,f231])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f232,plain,
    ( spl4_33
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f226,f54,f44,f229])).

fof(f44,plain,
    ( spl4_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f226,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f96,f46])).

fof(f46,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f96,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(sK2,X1)) = k10_relat_1(sK2,k1_relat_1(X1)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f27,f56])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f224,plain,
    ( spl4_31
    | ~ spl4_4
    | ~ spl4_32
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f216,f191,f221,f54,f218])).

fof(f221,plain,
    ( spl4_32
  <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f191,plain,
    ( spl4_26
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(k1_funct_1(sK2,sK0),X0)
        | r2_hidden(sK0,k10_relat_1(sK2,X0)) )
    | ~ spl4_26 ),
    inference(resolution,[],[f33,f193])).

fof(f193,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f191])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

% (31996)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f194,plain,
    ( spl4_26
    | ~ spl4_4
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f188,f68,f49,f54,f191])).

fof(f188,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl4_7 ),
    inference(resolution,[],[f37,f70])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f161,plain,
    ( ~ spl4_4
    | spl4_20
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f152,f83,f159,f54])).

fof(f83,plain,
    ( spl4_9
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f152,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,sK3(X1,k2_relat_1(sK2),sK2)),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_9 ),
    inference(superposition,[],[f31,f85])).

fof(f85,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f120,plain,
    ( ~ spl4_4
    | spl4_13
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f118,f83,f111,f54])).

fof(f118,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | r2_hidden(sK3(X1,k2_relat_1(sK2),sK2),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl4_9 ),
    inference(superposition,[],[f30,f85])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,
    ( spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f76,f54,f83])).

fof(f76,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl4_4 ),
    inference(resolution,[],[f26,f56])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f72,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f19,f68,f63,f59])).

fof(f19,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
            <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f71,plain,
    ( spl4_5
    | spl4_7 ),
    inference(avatar_split_clause,[],[f20,f68,f59])).

fof(f20,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f21,f63,f59])).

fof(f21,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

% (32007)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:57:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (32001)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (31993)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (32009)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (31991)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (32001)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (31985)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (31986)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (31987)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (31990)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (32008)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f388,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f47,f52,f57,f66,f71,f72,f86,f120,f161,f194,f224,f232,f251,f259,f289,f297,f303,f315,f316,f333,f357,f369,f370,f376])).
% 0.21/0.54  % (31999)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  fof(f376,plain,(
% 0.21/0.54    spl4_5 | ~spl4_6 | ~spl4_31 | ~spl4_33),
% 0.21/0.54    inference(avatar_split_clause,[],[f375,f229,f218,f63,f59])).
% 0.21/0.54  % (32000)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    spl4_5 <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    spl4_6 <=> r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    spl4_31 <=> ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK0),X0) | r2_hidden(sK0,k10_relat_1(sK2,X0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    spl4_33 <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.54  fof(f375,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) | (~spl4_6 | ~spl4_31 | ~spl4_33)),
% 0.21/0.54    inference(forward_demodulation,[],[f371,f231])).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1)) | ~spl4_33),
% 0.21/0.54    inference(avatar_component_clause,[],[f229])).
% 0.21/0.54  fof(f371,plain,(
% 0.21/0.54    r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1))) | (~spl4_6 | ~spl4_31)),
% 0.21/0.54    inference(resolution,[],[f65,f219])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK0),X0) | r2_hidden(sK0,k10_relat_1(sK2,X0))) ) | ~spl4_31),
% 0.21/0.54    inference(avatar_component_clause,[],[f218])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~spl4_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f63])).
% 0.21/0.54  fof(f370,plain,(
% 0.21/0.54    k1_funct_1(sK2,sK0) != sK3(sK0,k1_relat_1(sK1),sK2) | k1_funct_1(sK2,sK0) != sK3(sK0,k2_relat_1(sK2),sK2) | r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK3(sK0,k1_relat_1(sK1),sK2),k1_relat_1(sK1))),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f369,plain,(
% 0.21/0.54    ~spl4_4 | spl4_54 | ~spl4_3 | ~spl4_52),
% 0.21/0.54    inference(avatar_split_clause,[],[f359,f354,f49,f366,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    spl4_4 <=> v1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    spl4_54 <=> k1_funct_1(sK2,sK0) = sK3(sK0,k1_relat_1(sK1),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    spl4_3 <=> v1_funct_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f354,plain,(
% 0.21/0.54    spl4_52 <=> r2_hidden(k4_tarski(sK0,sK3(sK0,k1_relat_1(sK1),sK2)),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.21/0.54  fof(f359,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | k1_funct_1(sK2,sK0) = sK3(sK0,k1_relat_1(sK1),sK2) | ~v1_relat_1(sK2) | ~spl4_52),
% 0.21/0.54    inference(resolution,[],[f356,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  % (31988)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK0,sK3(sK0,k1_relat_1(sK1),sK2)),sK2) | ~spl4_52),
% 0.21/0.54    inference(avatar_component_clause,[],[f354])).
% 0.21/0.54  fof(f357,plain,(
% 0.21/0.54    spl4_52 | ~spl4_5 | ~spl4_36),
% 0.21/0.54    inference(avatar_split_clause,[],[f352,f249,f59,f354])).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    spl4_36 <=> ! [X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,sK1))) | r2_hidden(k4_tarski(X1,sK3(X1,k1_relat_1(sK1),sK2)),sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.54  fof(f352,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK0,sK3(sK0,k1_relat_1(sK1),sK2)),sK2) | (~spl4_5 | ~spl4_36)),
% 0.21/0.54    inference(resolution,[],[f250,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) | ~spl4_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f59])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,sK1))) | r2_hidden(k4_tarski(X1,sK3(X1,k1_relat_1(sK1),sK2)),sK2)) ) | ~spl4_36),
% 0.21/0.54    inference(avatar_component_clause,[],[f249])).
% 0.21/0.54  fof(f333,plain,(
% 0.21/0.54    spl4_48 | ~spl4_5 | ~spl4_38),
% 0.21/0.54    inference(avatar_split_clause,[],[f328,f257,f59,f330])).
% 0.21/0.54  fof(f330,plain,(
% 0.21/0.54    spl4_48 <=> r2_hidden(sK3(sK0,k1_relat_1(sK1),sK2),k1_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    spl4_38 <=> ! [X3] : (~r2_hidden(X3,k1_relat_1(k5_relat_1(sK2,sK1))) | r2_hidden(sK3(X3,k1_relat_1(sK1),sK2),k1_relat_1(sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.54  fof(f328,plain,(
% 0.21/0.54    r2_hidden(sK3(sK0,k1_relat_1(sK1),sK2),k1_relat_1(sK1)) | (~spl4_5 | ~spl4_38)),
% 0.21/0.54    inference(resolution,[],[f258,f61])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(k5_relat_1(sK2,sK1))) | r2_hidden(sK3(X3,k1_relat_1(sK1),sK2),k1_relat_1(sK1))) ) | ~spl4_38),
% 0.21/0.54    inference(avatar_component_clause,[],[f257])).
% 0.21/0.54  fof(f316,plain,(
% 0.21/0.54    k1_funct_1(sK2,sK0) != sK3(sK0,k2_relat_1(sK2),sK2) | r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | ~r2_hidden(sK3(sK0,k2_relat_1(sK2),sK2),k2_relat_1(sK2))),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f315,plain,(
% 0.21/0.54    ~spl4_4 | spl4_46 | ~spl4_3 | ~spl4_44),
% 0.21/0.54    inference(avatar_split_clause,[],[f305,f293,f49,f312,f54])).
% 0.21/0.54  fof(f312,plain,(
% 0.21/0.54    spl4_46 <=> k1_funct_1(sK2,sK0) = sK3(sK0,k2_relat_1(sK2),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.21/0.54  fof(f293,plain,(
% 0.21/0.54    spl4_44 <=> r2_hidden(k4_tarski(sK0,sK3(sK0,k2_relat_1(sK2),sK2)),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | k1_funct_1(sK2,sK0) = sK3(sK0,k2_relat_1(sK2),sK2) | ~v1_relat_1(sK2) | ~spl4_44),
% 0.21/0.54    inference(resolution,[],[f295,f35])).
% 0.21/0.54  fof(f295,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK0,sK3(sK0,k2_relat_1(sK2),sK2)),sK2) | ~spl4_44),
% 0.21/0.54    inference(avatar_component_clause,[],[f293])).
% 0.21/0.54  fof(f303,plain,(
% 0.21/0.54    spl4_44 | ~spl4_7 | ~spl4_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f300,f159,f68,f293])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    spl4_7 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    spl4_20 <=> ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X1,sK3(X1,k2_relat_1(sK2),sK2)),sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.54  fof(f300,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK0,sK3(sK0,k2_relat_1(sK2),sK2)),sK2) | (~spl4_7 | ~spl4_20)),
% 0.21/0.54    inference(resolution,[],[f70,f160])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X1,sK3(X1,k2_relat_1(sK2),sK2)),sK2)) ) | ~spl4_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f159])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl4_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f68])).
% 0.21/0.54  fof(f297,plain,(
% 0.21/0.54    spl4_7 | ~spl4_4 | ~spl4_5 | ~spl4_33),
% 0.21/0.54    inference(avatar_split_clause,[],[f290,f229,f59,f54,f68])).
% 0.21/0.54  fof(f290,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(sK2)) | (~spl4_4 | ~spl4_5 | ~spl4_33)),
% 0.21/0.54    inference(resolution,[],[f238,f61])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK1))) | r2_hidden(X0,k1_relat_1(sK2))) ) | (~spl4_4 | ~spl4_33)),
% 0.21/0.54    inference(superposition,[],[f88,f231])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k10_relat_1(sK2,X3)) | r2_hidden(X2,k1_relat_1(sK2))) ) | ~spl4_4),
% 0.21/0.54    inference(resolution,[],[f29,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(k10_relat_1(sK2,X1),k1_relat_1(sK2))) ) | ~spl4_4),
% 0.21/0.54    inference(resolution,[],[f28,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl4_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f54])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f289,plain,(
% 0.21/0.54    spl4_43 | ~spl4_7 | ~spl4_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f284,f111,f68,f286])).
% 0.21/0.54  fof(f286,plain,(
% 0.21/0.54    spl4_43 <=> r2_hidden(sK3(sK0,k2_relat_1(sK2),sK2),k2_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    spl4_13 <=> ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | r2_hidden(sK3(X1,k2_relat_1(sK2),sK2),k2_relat_1(sK2)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.54  fof(f284,plain,(
% 0.21/0.54    r2_hidden(sK3(sK0,k2_relat_1(sK2),sK2),k2_relat_1(sK2)) | (~spl4_7 | ~spl4_13)),
% 0.21/0.54    inference(resolution,[],[f112,f70])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | r2_hidden(sK3(X1,k2_relat_1(sK2),sK2),k2_relat_1(sK2))) ) | ~spl4_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f111])).
% 0.21/0.54  fof(f259,plain,(
% 0.21/0.54    ~spl4_4 | spl4_38 | ~spl4_33),
% 0.21/0.54    inference(avatar_split_clause,[],[f242,f229,f257,f54])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(k5_relat_1(sK2,sK1))) | r2_hidden(sK3(X3,k1_relat_1(sK1),sK2),k1_relat_1(sK1)) | ~v1_relat_1(sK2)) ) | ~spl4_33),
% 0.21/0.54    inference(superposition,[],[f32,f231])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.54  fof(f251,plain,(
% 0.21/0.54    ~spl4_4 | spl4_36 | ~spl4_33),
% 0.21/0.54    inference(avatar_split_clause,[],[f240,f229,f249,f54])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,sK1))) | r2_hidden(k4_tarski(X1,sK3(X1,k1_relat_1(sK1),sK2)),sK2) | ~v1_relat_1(sK2)) ) | ~spl4_33),
% 0.21/0.54    inference(superposition,[],[f31,f231])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    spl4_33 | ~spl4_2 | ~spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f226,f54,f44,f229])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    spl4_2 <=> v1_relat_1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.55  fof(f226,plain,(
% 0.21/0.55    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1)) | (~spl4_2 | ~spl4_4)),
% 0.21/0.55    inference(resolution,[],[f96,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    v1_relat_1(sK1) | ~spl4_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f44])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(sK2,X1)) = k10_relat_1(sK2,k1_relat_1(X1))) ) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f27,f56])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.55  fof(f224,plain,(
% 0.21/0.55    spl4_31 | ~spl4_4 | ~spl4_32 | ~spl4_26),
% 0.21/0.55    inference(avatar_split_clause,[],[f216,f191,f221,f54,f218])).
% 0.21/0.55  fof(f221,plain,(
% 0.21/0.55    spl4_32 <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    spl4_26 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.55  fof(f216,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(k1_funct_1(sK2,sK0),X0) | r2_hidden(sK0,k10_relat_1(sK2,X0))) ) | ~spl4_26),
% 0.21/0.55    inference(resolution,[],[f33,f193])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~spl4_26),
% 0.21/0.55    inference(avatar_component_clause,[],[f191])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  % (31996)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  fof(f194,plain,(
% 0.21/0.55    spl4_26 | ~spl4_4 | ~spl4_3 | ~spl4_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f188,f68,f49,f54,f191])).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~spl4_7),
% 0.21/0.55    inference(resolution,[],[f37,f70])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.21/0.55    inference(equality_resolution,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    ~spl4_4 | spl4_20 | ~spl4_9),
% 0.21/0.55    inference(avatar_split_clause,[],[f152,f83,f159,f54])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    spl4_9 <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X1,sK3(X1,k2_relat_1(sK2),sK2)),sK2) | ~v1_relat_1(sK2)) ) | ~spl4_9),
% 0.21/0.55    inference(superposition,[],[f31,f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl4_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f83])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    ~spl4_4 | spl4_13 | ~spl4_9),
% 0.21/0.55    inference(avatar_split_clause,[],[f118,f83,f111,f54])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | r2_hidden(sK3(X1,k2_relat_1(sK2),sK2),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl4_9),
% 0.21/0.55    inference(superposition,[],[f30,f85])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    spl4_9 | ~spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f76,f54,f83])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f26,f56])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ~spl4_5 | ~spl4_6 | ~spl4_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f19,f68,f63,f59])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <~> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <~> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.55    inference(negated_conjecture,[],[f7])).
% 0.21/0.55  fof(f7,conjecture,(
% 0.21/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    spl4_5 | spl4_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f20,f68,f59])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    spl4_5 | spl4_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f21,f63,f59])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f22,f54])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    v1_relat_1(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    spl4_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f23,f49])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    v1_funct_1(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    spl4_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f24,f44])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    v1_relat_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  % (32007)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (32001)------------------------------
% 0.21/0.55  % (32001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32001)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (32001)Memory used [KB]: 11001
% 0.21/0.55  % (32001)Time elapsed: 0.113 s
% 0.21/0.55  % (32001)------------------------------
% 0.21/0.55  % (32001)------------------------------
% 0.21/0.55  % (31984)Success in time 0.183 s
%------------------------------------------------------------------------------

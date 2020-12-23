%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 219 expanded)
%              Number of leaves         :   25 (  89 expanded)
%              Depth                    :    9
%              Number of atoms          :  302 ( 760 expanded)
%              Number of equality atoms :   22 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7386)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f1103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f124,f167,f172,f240,f249,f552,f621,f905,f987,f1097])).

fof(f1097,plain,
    ( ~ spl8_5
    | ~ spl8_16
    | spl8_50 ),
    inference(avatar_contradiction_clause,[],[f1096])).

fof(f1096,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_16
    | spl8_50 ),
    inference(subsumption_resolution,[],[f1095,f620])).

fof(f620,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | spl8_50 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl8_50
  <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f1095,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1082,f80])).

fof(f80,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl8_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1082,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | ~ spl8_16 ),
    inference(duplicate_literal_removal,[],[f1075])).

fof(f1075,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl8_16 ),
    inference(resolution,[],[f239,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f239,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),X2)
        | ~ v1_relat_1(X2)
        | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1)) )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl8_16
  <=> ! [X2] :
        ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1))
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(k7_relat_1(sK2,sK0),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f987,plain,
    ( spl8_66
    | ~ spl8_5
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f965,f246,f78,f902])).

fof(f902,plain,
    ( spl8_66
  <=> r2_hidden(sK4(k7_relat_1(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f246,plain,
    ( spl8_17
  <=> r2_hidden(sK4(k7_relat_1(sK2,sK0)),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f965,plain,
    ( r2_hidden(sK4(k7_relat_1(sK2,sK0)),sK2)
    | ~ spl8_5
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f100,f248,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f248,plain,
    ( r2_hidden(sK4(k7_relat_1(sK2,sK0)),k7_relat_1(sK2,sK0))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f246])).

fof(f100,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK2,X0),sK2)
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f80,f44])).

fof(f905,plain,
    ( ~ spl8_66
    | ~ spl8_5
    | spl8_14 ),
    inference(avatar_split_clause,[],[f899,f230,f78,f902])).

fof(f230,plain,
    ( spl8_14
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f899,plain,
    ( ~ r2_hidden(sK4(k7_relat_1(sK2,sK0)),sK2)
    | ~ spl8_5
    | spl8_14 ),
    inference(unit_resulting_resolution,[],[f80,f242,f41])).

fof(f41,plain,(
    ! [X4,X0] :
      ( k4_tarski(sK5(X4),sK6(X4)) = X4
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK4(X0)
          & r2_hidden(sK4(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK5(X4),sK6(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f28,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK4(X0)
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK5(X4),sK6(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f242,plain,
    ( ! [X0,X1] : k4_tarski(X0,X1) != sK4(k7_relat_1(sK2,sK0))
    | spl8_14 ),
    inference(unit_resulting_resolution,[],[f232,f43])).

fof(f43,plain,(
    ! [X2,X0,X3] :
      ( v1_relat_1(X0)
      | k4_tarski(X2,X3) != sK4(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f232,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f230])).

fof(f621,plain,
    ( ~ spl8_50
    | ~ spl8_13
    | spl8_30 ),
    inference(avatar_split_clause,[],[f609,f374,f169,f618])).

fof(f169,plain,
    ( spl8_13
  <=> r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f374,plain,
    ( spl8_30
  <=> r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f609,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | ~ spl8_13
    | spl8_30 ),
    inference(unit_resulting_resolution,[],[f171,f376,f50])).

fof(f376,plain,
    ( ~ r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK2,sK1))
    | spl8_30 ),
    inference(avatar_component_clause,[],[f374])).

fof(f171,plain,
    ( r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK2,sK0))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f169])).

% (7391)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f552,plain,
    ( ~ spl8_30
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_12 ),
    inference(avatar_split_clause,[],[f545,f164,f78,f73,f68,f374])).

fof(f68,plain,
    ( spl8_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f73,plain,
    ( spl8_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f164,plain,
    ( spl8_12
  <=> r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f545,plain,
    ( ~ r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK2,sK1))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_12 ),
    inference(unit_resulting_resolution,[],[f166,f197])).

fof(f197,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k7_relat_1(sK2,X2))
        | r2_hidden(X3,k7_relat_1(sK3,X2)) )
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(resolution,[],[f134,f50])).

fof(f134,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f80,f75,f70,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(f70,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f75,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f166,plain,
    ( ~ r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK3,sK1))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f249,plain,
    ( spl8_17
    | spl8_14 ),
    inference(avatar_split_clause,[],[f241,f230,f246])).

fof(f241,plain,
    ( r2_hidden(sK4(k7_relat_1(sK2,sK0)),k7_relat_1(sK2,sK0))
    | spl8_14 ),
    inference(unit_resulting_resolution,[],[f232,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f240,plain,
    ( ~ spl8_14
    | spl8_16
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f227,f121,f238,f230])).

fof(f121,plain,
    ( spl8_7
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f227,plain,
    ( ! [X2] :
        ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1))
        | ~ r1_tarski(k7_relat_1(sK2,sK0),X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k7_relat_1(sK2,sK0)) )
    | ~ spl8_7 ),
    inference(superposition,[],[f45,f123])).

fof(f123,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f172,plain,
    ( spl8_13
    | spl8_1 ),
    inference(avatar_split_clause,[],[f158,f58,f169])).

fof(f58,plain,
    ( spl8_1
  <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f158,plain,
    ( r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK2,sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f60,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f167,plain,
    ( ~ spl8_12
    | spl8_1 ),
    inference(avatar_split_clause,[],[f159,f58,f164])).

fof(f159,plain,
    ( ~ r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK3,sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f60,f52])).

% (7400)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f124,plain,
    ( spl8_7
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f107,f78,f63,f121])).

fof(f63,plain,
    ( spl8_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f107,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f80,f65,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(f65,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f81,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f36,f78])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

fof(f76,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f37,f73])).

fof(f37,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f38,f68])).

fof(f38,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f39,f63])).

fof(f39,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f40,f58])).

fof(f40,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:24:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (7380)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (7396)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (7388)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (7382)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (7383)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (7390)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (7398)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (7377)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (7395)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (7374)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (7402)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (7390)Refutation not found, incomplete strategy% (7390)------------------------------
% 0.20/0.52  % (7390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7390)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7390)Memory used [KB]: 10618
% 0.20/0.52  % (7390)Time elapsed: 0.127 s
% 0.20/0.52  % (7390)------------------------------
% 0.20/0.52  % (7390)------------------------------
% 0.20/0.52  % (7373)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (7378)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (7394)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (7375)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (7376)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (7375)Refutation not found, incomplete strategy% (7375)------------------------------
% 0.20/0.53  % (7375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7375)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7375)Memory used [KB]: 10746
% 0.20/0.53  % (7375)Time elapsed: 0.129 s
% 0.20/0.53  % (7375)------------------------------
% 0.20/0.53  % (7375)------------------------------
% 0.20/0.53  % (7395)Refutation not found, incomplete strategy% (7395)------------------------------
% 0.20/0.53  % (7395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7395)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7395)Memory used [KB]: 10746
% 0.20/0.53  % (7395)Time elapsed: 0.092 s
% 0.20/0.53  % (7395)------------------------------
% 0.20/0.53  % (7395)------------------------------
% 0.20/0.53  % (7387)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (7384)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (7389)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (7382)Refutation not found, incomplete strategy% (7382)------------------------------
% 0.20/0.53  % (7382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7382)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7382)Memory used [KB]: 10874
% 0.20/0.53  % (7382)Time elapsed: 0.128 s
% 0.20/0.53  % (7382)------------------------------
% 0.20/0.53  % (7382)------------------------------
% 0.20/0.53  % (7383)Refutation not found, incomplete strategy% (7383)------------------------------
% 0.20/0.53  % (7383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7383)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7383)Memory used [KB]: 10746
% 0.20/0.53  % (7383)Time elapsed: 0.138 s
% 0.20/0.53  % (7383)------------------------------
% 0.20/0.53  % (7383)------------------------------
% 0.20/0.53  % (7385)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (7393)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (7399)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (7397)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (7379)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (7401)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (7398)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  % (7386)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  fof(f1103,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f124,f167,f172,f240,f249,f552,f621,f905,f987,f1097])).
% 0.20/0.54  fof(f1097,plain,(
% 0.20/0.54    ~spl8_5 | ~spl8_16 | spl8_50),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1096])).
% 0.20/0.54  fof(f1096,plain,(
% 0.20/0.54    $false | (~spl8_5 | ~spl8_16 | spl8_50)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1095,f620])).
% 0.20/0.54  fof(f620,plain,(
% 0.20/0.54    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) | spl8_50),
% 0.20/0.54    inference(avatar_component_clause,[],[f618])).
% 0.20/0.54  fof(f618,plain,(
% 0.20/0.54    spl8_50 <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 0.20/0.54  fof(f1095,plain,(
% 0.20/0.54    r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) | (~spl8_5 | ~spl8_16)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1082,f80])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    v1_relat_1(sK2) | ~spl8_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f78])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    spl8_5 <=> v1_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.54  fof(f1082,plain,(
% 0.20/0.54    ~v1_relat_1(sK2) | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) | ~spl8_16),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f1075])).
% 0.20/0.54  fof(f1075,plain,(
% 0.20/0.54    ~v1_relat_1(sK2) | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~spl8_16),
% 0.20/0.54    inference(resolution,[],[f239,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.54  fof(f239,plain,(
% 0.20/0.54    ( ! [X2] : (~r1_tarski(k7_relat_1(sK2,sK0),X2) | ~v1_relat_1(X2) | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1))) ) | ~spl8_16),
% 0.20/0.54    inference(avatar_component_clause,[],[f238])).
% 0.20/0.54  fof(f238,plain,(
% 0.20/0.54    spl8_16 <=> ! [X2] : (r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1)) | ~v1_relat_1(X2) | ~r1_tarski(k7_relat_1(sK2,sK0),X2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.54  fof(f987,plain,(
% 0.20/0.54    spl8_66 | ~spl8_5 | ~spl8_17),
% 0.20/0.54    inference(avatar_split_clause,[],[f965,f246,f78,f902])).
% 0.20/0.54  fof(f902,plain,(
% 0.20/0.54    spl8_66 <=> r2_hidden(sK4(k7_relat_1(sK2,sK0)),sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).
% 0.20/0.54  fof(f246,plain,(
% 0.20/0.54    spl8_17 <=> r2_hidden(sK4(k7_relat_1(sK2,sK0)),k7_relat_1(sK2,sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.54  fof(f965,plain,(
% 0.20/0.54    r2_hidden(sK4(k7_relat_1(sK2,sK0)),sK2) | (~spl8_5 | ~spl8_17)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f100,f248,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f33,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(rectify,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f248,plain,(
% 0.20/0.54    r2_hidden(sK4(k7_relat_1(sK2,sK0)),k7_relat_1(sK2,sK0)) | ~spl8_17),
% 0.20/0.54    inference(avatar_component_clause,[],[f246])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),sK2)) ) | ~spl8_5),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f80,f44])).
% 0.20/0.54  fof(f905,plain,(
% 0.20/0.54    ~spl8_66 | ~spl8_5 | spl8_14),
% 0.20/0.54    inference(avatar_split_clause,[],[f899,f230,f78,f902])).
% 0.20/0.54  fof(f230,plain,(
% 0.20/0.54    spl8_14 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.54  fof(f899,plain,(
% 0.20/0.54    ~r2_hidden(sK4(k7_relat_1(sK2,sK0)),sK2) | (~spl8_5 | spl8_14)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f80,f242,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X4,X0] : (k4_tarski(sK5(X4),sK6(X4)) = X4 | ~r2_hidden(X4,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK4(X0) & r2_hidden(sK4(X0),X0))) & (! [X4] : (k4_tarski(sK5(X4),sK6(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f28,f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK4(X0) & r2_hidden(sK4(X0),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK5(X4),sK6(X4)) = X4)),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(rectify,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.54  fof(f242,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_tarski(X0,X1) != sK4(k7_relat_1(sK2,sK0))) ) | spl8_14),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f232,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X2,X0,X3] : (v1_relat_1(X0) | k4_tarski(X2,X3) != sK4(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f232,plain,(
% 0.20/0.54    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl8_14),
% 0.20/0.54    inference(avatar_component_clause,[],[f230])).
% 0.20/0.54  fof(f621,plain,(
% 0.20/0.54    ~spl8_50 | ~spl8_13 | spl8_30),
% 0.20/0.54    inference(avatar_split_clause,[],[f609,f374,f169,f618])).
% 0.20/0.54  fof(f169,plain,(
% 0.20/0.54    spl8_13 <=> r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK2,sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.54  fof(f374,plain,(
% 0.20/0.54    spl8_30 <=> r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK2,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.20/0.54  fof(f609,plain,(
% 0.20/0.54    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) | (~spl8_13 | spl8_30)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f171,f376,f50])).
% 0.20/0.54  fof(f376,plain,(
% 0.20/0.54    ~r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK2,sK1)) | spl8_30),
% 0.20/0.54    inference(avatar_component_clause,[],[f374])).
% 0.20/0.54  fof(f171,plain,(
% 0.20/0.54    r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK2,sK0)) | ~spl8_13),
% 0.20/0.54    inference(avatar_component_clause,[],[f169])).
% 0.20/0.54  % (7391)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  fof(f552,plain,(
% 0.20/0.54    ~spl8_30 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_12),
% 0.20/0.54    inference(avatar_split_clause,[],[f545,f164,f78,f73,f68,f374])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    spl8_3 <=> r1_tarski(sK2,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    spl8_4 <=> v1_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.54  fof(f164,plain,(
% 0.20/0.54    spl8_12 <=> r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK3,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.54  fof(f545,plain,(
% 0.20/0.54    ~r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK2,sK1)) | (~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_12)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f166,f197])).
% 0.20/0.54  fof(f197,plain,(
% 0.20/0.54    ( ! [X2,X3] : (~r2_hidden(X3,k7_relat_1(sK2,X2)) | r2_hidden(X3,k7_relat_1(sK3,X2))) ) | (~spl8_3 | ~spl8_4 | ~spl8_5)),
% 0.20/0.54    inference(resolution,[],[f134,f50])).
% 0.20/0.54  fof(f134,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0))) ) | (~spl8_3 | ~spl8_4 | ~spl8_5)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f80,f75,f70,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    r1_tarski(sK2,sK3) | ~spl8_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f68])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    v1_relat_1(sK3) | ~spl8_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f73])).
% 0.20/0.54  fof(f166,plain,(
% 0.20/0.54    ~r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK3,sK1)) | spl8_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f164])).
% 0.20/0.54  fof(f249,plain,(
% 0.20/0.54    spl8_17 | spl8_14),
% 0.20/0.54    inference(avatar_split_clause,[],[f241,f230,f246])).
% 0.20/0.54  fof(f241,plain,(
% 0.20/0.54    r2_hidden(sK4(k7_relat_1(sK2,sK0)),k7_relat_1(sK2,sK0)) | spl8_14),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f232,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK4(X0),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f240,plain,(
% 0.20/0.54    ~spl8_14 | spl8_16 | ~spl8_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f227,f121,f238,f230])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    spl8_7 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.54  fof(f227,plain,(
% 0.20/0.54    ( ! [X2] : (r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X2,sK1)) | ~r1_tarski(k7_relat_1(sK2,sK0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(k7_relat_1(sK2,sK0))) ) | ~spl8_7),
% 0.20/0.54    inference(superposition,[],[f45,f123])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | ~spl8_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f121])).
% 0.20/0.54  fof(f172,plain,(
% 0.20/0.54    spl8_13 | spl8_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f158,f58,f169])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    spl8_1 <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.54  fof(f158,plain,(
% 0.20/0.54    r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK2,sK0)) | spl8_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f60,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) | spl8_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f58])).
% 0.20/0.54  fof(f167,plain,(
% 0.20/0.54    ~spl8_12 | spl8_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f159,f58,f164])).
% 0.20/0.54  fof(f159,plain,(
% 0.20/0.54    ~r2_hidden(sK7(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),k7_relat_1(sK3,sK1)) | spl8_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f60,f52])).
% 0.20/0.54  % (7400)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK7(X0,X1),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    spl8_7 | ~spl8_2 | ~spl8_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f107,f78,f63,f121])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    spl8_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | (~spl8_2 | ~spl8_5)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f80,f65,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(flattening,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    r1_tarski(sK0,sK1) | ~spl8_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f63])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    spl8_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f36,f78])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    v1_relat_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23,f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.54    inference(flattening,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.20/0.54    inference(negated_conjecture,[],[f9])).
% 0.20/0.54  fof(f9,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    spl8_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f37,f73])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    v1_relat_1(sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    spl8_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f38,f68])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    r1_tarski(sK2,sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    spl8_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f39,f63])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    r1_tarski(sK0,sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ~spl8_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f40,f58])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (7398)------------------------------
% 0.20/0.54  % (7398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7398)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (7398)Memory used [KB]: 6908
% 0.20/0.54  % (7398)Time elapsed: 0.139 s
% 0.20/0.54  % (7398)------------------------------
% 0.20/0.54  % (7398)------------------------------
% 0.20/0.54  % (7381)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (7372)Success in time 0.189 s
%------------------------------------------------------------------------------

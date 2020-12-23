%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:21 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 218 expanded)
%              Number of leaves         :   24 (  90 expanded)
%              Depth                    :    9
%              Number of atoms          :  394 ( 908 expanded)
%              Number of equality atoms :   12 (  34 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f65,f67,f71,f75,f82,f89,f98,f108,f110,f112,f115,f123,f137,f139,f150,f154,f181,f183])).

% (29534)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f183,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)
    | r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f181,plain,
    ( ~ spl3_5
    | ~ spl3_4
    | spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f171,f148,f134,f69,f73])).

fof(f73,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f69,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f134,plain,
    ( spl3_15
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f148,plain,
    ( spl3_16
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f171,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_16 ),
    inference(resolution,[],[f149,f44])).

% (29533)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f149,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f154,plain,
    ( ~ spl3_5
    | spl3_17
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f143,f106,f152,f73])).

fof(f152,plain,
    ( spl3_17
  <=> r2_hidden(k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f106,plain,
    ( spl3_12
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),k5_relat_1(sK2,k6_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f143,plain,
    ( r2_hidden(k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f107,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

fof(f107,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),k5_relat_1(sK2,k6_relat_1(sK1)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f150,plain,
    ( ~ spl3_5
    | spl3_16
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f142,f106,f148,f73])).

fof(f142,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f107,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f139,plain,
    ( ~ spl3_5
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9
    | spl3_10 ),
    inference(avatar_split_clause,[],[f138,f100,f96,f93,f69,f73])).

fof(f93,plain,
    ( spl3_8
  <=> v1_relat_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f96,plain,
    ( spl3_9
  <=> v1_funct_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f100,plain,
    ( spl3_10
  <=> v1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f138,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(resolution,[],[f101,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f101,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f137,plain,
    ( ~ spl3_10
    | ~ spl3_11
    | spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f128,f121,f54,f103,f100])).

fof(f103,plain,
    ( spl3_11
  <=> v1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f54,plain,
    ( spl3_1
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f121,plain,
    ( spl3_13
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(sK2,k6_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f128,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))
    | ~ v1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)))
    | ~ v1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))
    | ~ spl3_13 ),
    inference(resolution,[],[f122,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f122,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(sK2,k6_relat_1(sK1)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f119,f87,f60,f121])).

fof(f60,plain,
    ( spl3_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f87,plain,
    ( spl3_7
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(sK2,k6_relat_1(X0)))
        | ~ r2_hidden(k1_funct_1(sK2,sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f119,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(sK2,k6_relat_1(sK1)))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f88,f64])).

fof(f64,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK0),X0)
        | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(sK2,k6_relat_1(X0))) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f115,plain,
    ( ~ spl3_5
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9
    | spl3_11 ),
    inference(avatar_split_clause,[],[f114,f103,f96,f93,f69,f73])).

fof(f114,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(resolution,[],[f104,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f104,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f112,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f97,f37])).

fof(f37,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f97,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f110,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f94,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f94,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f108,plain,
    ( ~ spl3_10
    | ~ spl3_11
    | spl3_12
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f91,f54,f106,f103,f100])).

fof(f91,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),k5_relat_1(sK2,k6_relat_1(sK1)))
    | ~ v1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)))
    | ~ v1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))
    | ~ spl3_1 ),
    inference(resolution,[],[f63,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f98,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | ~ spl3_5
    | ~ spl3_4
    | spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f90,f54,f57,f69,f73,f96,f93])).

fof(f57,plain,
    ( spl3_2
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f90,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ spl3_1 ),
    inference(resolution,[],[f63,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f89,plain,
    ( ~ spl3_5
    | spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f85,f80,f87,f73])).

fof(f80,plain,
    ( spl3_6
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f85,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(sK2,k6_relat_1(X0)))
        | ~ r2_hidden(k1_funct_1(sK2,sK0),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_6 ),
    inference(resolution,[],[f48,f81])).

fof(f81,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X3)
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,
    ( ~ spl3_5
    | ~ spl3_4
    | spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f76,f57,f80,f69,f73])).

fof(f76,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f52,f66])).

fof(f66,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f75,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
    & ( ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
        & r2_hidden(sK0,k1_relat_1(sK2)) )
      | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
          & r2_hidden(sK0,k1_relat_1(sK2)) )
        | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

% (29526)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (29521)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (29527)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

fof(f71,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f33,f57,f54])).

fof(f33,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f34,f60,f54])).

fof(f34,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f35,f60,f57,f54])).

fof(f35,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:47:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.44  % (29524)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.44  % (29525)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.45  % (29525)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f184,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f62,f65,f67,f71,f75,f82,f89,f98,f108,f110,f112,f115,f123,f137,f139,f150,f154,f181,f183])).
% 0.19/0.45  % (29534)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.45  fof(f183,plain,(
% 0.19/0.45    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0) | r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0),sK1)),
% 0.19/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.45  fof(f181,plain,(
% 0.19/0.45    ~spl3_5 | ~spl3_4 | spl3_15 | ~spl3_16),
% 0.19/0.45    inference(avatar_split_clause,[],[f171,f148,f134,f69,f73])).
% 0.19/0.45  fof(f73,plain,(
% 0.19/0.45    spl3_5 <=> v1_relat_1(sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.45  fof(f69,plain,(
% 0.19/0.45    spl3_4 <=> v1_funct_1(sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.45  fof(f134,plain,(
% 0.19/0.45    spl3_15 <=> k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.45  fof(f148,plain,(
% 0.19/0.45    spl3_16 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.45  fof(f171,plain,(
% 0.19/0.45    k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_16),
% 0.19/0.45    inference(resolution,[],[f149,f44])).
% 0.19/0.46  % (29533)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f26])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(flattening,[],[f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(nnf_transformation,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(flattening,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.19/0.46  fof(f149,plain,(
% 0.19/0.46    r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),sK2) | ~spl3_16),
% 0.19/0.46    inference(avatar_component_clause,[],[f148])).
% 0.19/0.46  fof(f154,plain,(
% 0.19/0.46    ~spl3_5 | spl3_17 | ~spl3_12),
% 0.19/0.46    inference(avatar_split_clause,[],[f143,f106,f152,f73])).
% 0.19/0.46  fof(f152,plain,(
% 0.19/0.46    spl3_17 <=> r2_hidden(k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0),sK1)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.19/0.46  fof(f106,plain,(
% 0.19/0.46    spl3_12 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),k5_relat_1(sK2,k6_relat_1(sK1)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.46  fof(f143,plain,(
% 0.19/0.46    r2_hidden(k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0),sK1) | ~v1_relat_1(sK2) | ~spl3_12),
% 0.19/0.46    inference(resolution,[],[f107,f46])).
% 0.19/0.46  fof(f46,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | r2_hidden(X1,X2) | ~v1_relat_1(X3)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 0.19/0.46    inference(flattening,[],[f27])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 0.19/0.46    inference(nnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))) | ~v1_relat_1(X3))),
% 0.19/0.46    inference(ennf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).
% 0.19/0.46  fof(f107,plain,(
% 0.19/0.46    r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),k5_relat_1(sK2,k6_relat_1(sK1))) | ~spl3_12),
% 0.19/0.46    inference(avatar_component_clause,[],[f106])).
% 0.19/0.46  fof(f150,plain,(
% 0.19/0.46    ~spl3_5 | spl3_16 | ~spl3_12),
% 0.19/0.46    inference(avatar_split_clause,[],[f142,f106,f148,f73])).
% 0.19/0.46  fof(f142,plain,(
% 0.19/0.46    r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),sK2) | ~v1_relat_1(sK2) | ~spl3_12),
% 0.19/0.46    inference(resolution,[],[f107,f47])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | r2_hidden(k4_tarski(X0,X1),X3) | ~v1_relat_1(X3)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f28])).
% 0.19/0.46  fof(f139,plain,(
% 0.19/0.46    ~spl3_5 | ~spl3_4 | ~spl3_8 | ~spl3_9 | spl3_10),
% 0.19/0.46    inference(avatar_split_clause,[],[f138,f100,f96,f93,f69,f73])).
% 0.19/0.46  fof(f93,plain,(
% 0.19/0.46    spl3_8 <=> v1_relat_1(k6_relat_1(sK1))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.46  fof(f96,plain,(
% 0.19/0.46    spl3_9 <=> v1_funct_1(k6_relat_1(sK1))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.46  fof(f100,plain,(
% 0.19/0.46    spl3_10 <=> v1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.46  fof(f138,plain,(
% 0.19/0.46    ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_10),
% 0.19/0.46    inference(resolution,[],[f101,f38])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(flattening,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.19/0.46  fof(f101,plain,(
% 0.19/0.46    ~v1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))) | spl3_10),
% 0.19/0.46    inference(avatar_component_clause,[],[f100])).
% 0.19/0.46  fof(f137,plain,(
% 0.19/0.46    ~spl3_10 | ~spl3_11 | spl3_1 | ~spl3_13),
% 0.19/0.46    inference(avatar_split_clause,[],[f128,f121,f54,f103,f100])).
% 0.19/0.46  fof(f103,plain,(
% 0.19/0.46    spl3_11 <=> v1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.46  fof(f54,plain,(
% 0.19/0.46    spl3_1 <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.46  fof(f121,plain,(
% 0.19/0.46    spl3_13 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(sK2,k6_relat_1(sK1)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.19/0.46  fof(f128,plain,(
% 0.19/0.46    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) | ~v1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1))) | ~v1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))) | ~spl3_13),
% 0.19/0.46    inference(resolution,[],[f122,f43])).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f26])).
% 0.19/0.46  fof(f122,plain,(
% 0.19/0.46    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(sK2,k6_relat_1(sK1))) | ~spl3_13),
% 0.19/0.46    inference(avatar_component_clause,[],[f121])).
% 0.19/0.46  fof(f123,plain,(
% 0.19/0.46    spl3_13 | ~spl3_3 | ~spl3_7),
% 0.19/0.46    inference(avatar_split_clause,[],[f119,f87,f60,f121])).
% 0.19/0.46  fof(f60,plain,(
% 0.19/0.46    spl3_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.46  fof(f87,plain,(
% 0.19/0.46    spl3_7 <=> ! [X0] : (r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(sK2,k6_relat_1(X0))) | ~r2_hidden(k1_funct_1(sK2,sK0),X0))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.46  fof(f119,plain,(
% 0.19/0.46    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(sK2,k6_relat_1(sK1))) | (~spl3_3 | ~spl3_7)),
% 0.19/0.46    inference(resolution,[],[f88,f64])).
% 0.19/0.46  fof(f64,plain,(
% 0.19/0.46    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~spl3_3),
% 0.19/0.46    inference(avatar_component_clause,[],[f60])).
% 0.19/0.46  fof(f88,plain,(
% 0.19/0.46    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK0),X0) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(sK2,k6_relat_1(X0)))) ) | ~spl3_7),
% 0.19/0.46    inference(avatar_component_clause,[],[f87])).
% 0.19/0.46  fof(f115,plain,(
% 0.19/0.46    ~spl3_5 | ~spl3_4 | ~spl3_8 | ~spl3_9 | spl3_11),
% 0.19/0.46    inference(avatar_split_clause,[],[f114,f103,f96,f93,f69,f73])).
% 0.19/0.46  fof(f114,plain,(
% 0.19/0.46    ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_11),
% 0.19/0.46    inference(resolution,[],[f104,f39])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f12])).
% 0.19/0.46  fof(f104,plain,(
% 0.19/0.46    ~v1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1))) | spl3_11),
% 0.19/0.46    inference(avatar_component_clause,[],[f103])).
% 0.19/0.46  fof(f112,plain,(
% 0.19/0.46    spl3_9),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f111])).
% 0.19/0.46  fof(f111,plain,(
% 0.19/0.46    $false | spl3_9),
% 0.19/0.46    inference(resolution,[],[f97,f37])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.46  fof(f97,plain,(
% 0.19/0.46    ~v1_funct_1(k6_relat_1(sK1)) | spl3_9),
% 0.19/0.46    inference(avatar_component_clause,[],[f96])).
% 0.19/0.46  fof(f110,plain,(
% 0.19/0.46    spl3_8),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f109])).
% 0.19/0.46  fof(f109,plain,(
% 0.19/0.46    $false | spl3_8),
% 0.19/0.46    inference(resolution,[],[f94,f36])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f4])).
% 0.19/0.46  fof(f94,plain,(
% 0.19/0.46    ~v1_relat_1(k6_relat_1(sK1)) | spl3_8),
% 0.19/0.46    inference(avatar_component_clause,[],[f93])).
% 0.19/0.46  fof(f108,plain,(
% 0.19/0.46    ~spl3_10 | ~spl3_11 | spl3_12 | ~spl3_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f91,f54,f106,f103,f100])).
% 0.19/0.46  fof(f91,plain,(
% 0.19/0.46    r2_hidden(k4_tarski(sK0,k1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1)),sK0)),k5_relat_1(sK2,k6_relat_1(sK1))) | ~v1_funct_1(k5_relat_1(sK2,k6_relat_1(sK1))) | ~v1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))) | ~spl3_1),
% 0.19/0.46    inference(resolution,[],[f63,f52])).
% 0.19/0.46  fof(f52,plain,(
% 0.19/0.46    ( ! [X2,X0] : (~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.19/0.46    inference(equality_resolution,[],[f45])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f26])).
% 0.19/0.46  fof(f63,plain,(
% 0.19/0.46    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) | ~spl3_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f54])).
% 0.19/0.46  fof(f98,plain,(
% 0.19/0.46    ~spl3_8 | ~spl3_9 | ~spl3_5 | ~spl3_4 | spl3_2 | ~spl3_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f90,f54,f57,f69,f73,f96,f93])).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    spl3_2 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.46  fof(f90,plain,(
% 0.19/0.46    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~spl3_1),
% 0.19/0.46    inference(resolution,[],[f63,f40])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.46    inference(flattening,[],[f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.46    inference(nnf_transformation,[],[f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.46    inference(flattening,[],[f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).
% 0.19/0.46  fof(f89,plain,(
% 0.19/0.46    ~spl3_5 | spl3_7 | ~spl3_6),
% 0.19/0.46    inference(avatar_split_clause,[],[f85,f80,f87,f73])).
% 0.19/0.46  fof(f80,plain,(
% 0.19/0.46    spl3_6 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    ( ! [X0] : (r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(sK2,k6_relat_1(X0))) | ~r2_hidden(k1_funct_1(sK2,sK0),X0) | ~v1_relat_1(sK2)) ) | ~spl3_6),
% 0.19/0.46    inference(resolution,[],[f48,f81])).
% 0.19/0.46  fof(f81,plain,(
% 0.19/0.46    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~spl3_6),
% 0.19/0.46    inference(avatar_component_clause,[],[f80])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),X3) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(X1,X2) | ~v1_relat_1(X3)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f28])).
% 0.19/0.46  fof(f82,plain,(
% 0.19/0.46    ~spl3_5 | ~spl3_4 | spl3_6 | ~spl3_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f76,f57,f80,f69,f73])).
% 0.19/0.46  fof(f76,plain,(
% 0.19/0.46    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_2),
% 0.19/0.46    inference(resolution,[],[f52,f66])).
% 0.19/0.46  fof(f66,plain,(
% 0.19/0.46    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl3_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f57])).
% 0.19/0.46  fof(f75,plain,(
% 0.19/0.46    spl3_5),
% 0.19/0.46    inference(avatar_split_clause,[],[f31,f73])).
% 0.19/0.46  fof(f31,plain,(
% 0.19/0.46    v1_relat_1(sK2)),
% 0.19/0.46    inference(cnf_transformation,[],[f22])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    (~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  % (29526)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.46  % (29521)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.46  % (29527)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.19/0.47    inference(flattening,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ? [X0,X1,X2] : ((((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.19/0.47    inference(nnf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,plain,(
% 0.19/0.47    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.19/0.47    inference(flattening,[],[f9])).
% 0.19/0.47  fof(f9,plain,(
% 0.19/0.47    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,negated_conjecture,(
% 0.19/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.19/0.47    inference(negated_conjecture,[],[f7])).
% 0.19/0.47  fof(f7,conjecture,(
% 0.19/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).
% 0.19/0.47  fof(f71,plain,(
% 0.19/0.47    spl3_4),
% 0.19/0.47    inference(avatar_split_clause,[],[f32,f69])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    v1_funct_1(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  fof(f67,plain,(
% 0.19/0.47    spl3_1 | spl3_2),
% 0.19/0.47    inference(avatar_split_clause,[],[f33,f57,f54])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  fof(f65,plain,(
% 0.19/0.47    spl3_1 | spl3_3),
% 0.19/0.47    inference(avatar_split_clause,[],[f34,f60,f54])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    r2_hidden(k1_funct_1(sK2,sK0),sK1) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.19/0.47    inference(avatar_split_clause,[],[f35,f60,f57,f54])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (29525)------------------------------
% 0.19/0.47  % (29525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (29525)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (29525)Memory used [KB]: 10746
% 0.19/0.47  % (29525)Time elapsed: 0.060 s
% 0.19/0.47  % (29525)------------------------------
% 0.19/0.47  % (29525)------------------------------
% 0.19/0.47  % (29518)Success in time 0.125 s
%------------------------------------------------------------------------------

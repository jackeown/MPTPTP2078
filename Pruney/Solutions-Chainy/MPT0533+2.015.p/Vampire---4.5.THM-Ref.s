%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 176 expanded)
%              Number of leaves         :   26 (  83 expanded)
%              Depth                    :    7
%              Number of atoms          :  341 ( 731 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32337)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% (32317)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% (32336)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% (32328)WARNING: option uwaf not known.
% (32328)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% (32329)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% (32326)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% (32327)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% (32338)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
fof(f144,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f56,f61,f65,f69,f73,f77,f81,f92,f101,f103,f110,f117,f126,f138,f143])).

fof(f143,plain,
    ( ~ spl6_1
    | ~ spl6_5
    | spl6_20 ),
    inference(avatar_split_clause,[],[f139,f135,f54,f34])).

fof(f34,plain,
    ( spl6_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f54,plain,
    ( spl6_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f135,plain,
    ( spl6_20
  <=> v1_relat_1(k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f139,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_5
    | spl6_20 ),
    inference(resolution,[],[f137,f55])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f137,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f135])).

fof(f138,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_20
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f127,f124,f75,f49,f135,f44,f39,f34])).

fof(f39,plain,
    ( spl6_2
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f44,plain,
    ( spl6_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f49,plain,
    ( spl6_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f75,plain,
    ( spl6_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f124,plain,
    ( spl6_18
  <=> ! [X0] :
        ( ~ v1_relat_1(k8_relat_1(X0,sK2))
        | ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f127,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(resolution,[],[f125,f76])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(sK1,sK3))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(k8_relat_1(X0,sK2)) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f124])).

fof(f126,plain,
    ( ~ spl6_1
    | spl6_18
    | ~ spl6_7
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f118,f115,f63,f124,f34])).

fof(f63,plain,
    ( spl6_7
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f115,plain,
    ( spl6_17
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k8_relat_1(sK0,sK2),X0)
        | ~ r1_tarski(X0,k8_relat_1(sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k8_relat_1(X0,sK2))
        | ~ r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(sK1,sK3))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_7
    | ~ spl6_17 ),
    inference(resolution,[],[f116,f64])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK2),X0)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k8_relat_1(sK1,sK3)) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,
    ( spl6_6
    | ~ spl6_14
    | spl6_17
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f113,f108,f67,f115,f95,f58])).

fof(f58,plain,
    ( spl6_6
  <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f95,plain,
    ( spl6_14
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f67,plain,
    ( spl6_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f108,plain,
    ( spl6_16
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k8_relat_1(sK1,sK3))
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1)
        | ~ r1_tarski(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k8_relat_1(sK1,sK3))
        | ~ r1_tarski(k8_relat_1(sK0,sK2),X0)
        | ~ v1_relat_1(k8_relat_1(sK0,sK2))
        | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) )
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k8_relat_1(sK1,sK3))
        | ~ r1_tarski(k8_relat_1(sK0,sK2),X0)
        | ~ v1_relat_1(k8_relat_1(sK0,sK2))
        | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
        | ~ v1_relat_1(k8_relat_1(sK0,sK2)) )
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(resolution,[],[f109,f68])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
        | r1_tarski(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,k8_relat_1(sK1,sK3))
        | ~ r1_tarski(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,
    ( spl6_16
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f105,f99,f79,f108])).

fof(f79,plain,
    ( spl6_11
  <=> ! [X1,X5,X0,X4] :
        ( r2_hidden(k4_tarski(X4,X5),X1)
        | ~ r2_hidden(k4_tarski(X4,X5),X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f99,plain,
    ( spl6_15
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k8_relat_1(sK1,sK3))
        | ~ r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

% (32333)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k8_relat_1(sK1,sK3))
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1)
        | ~ r1_tarski(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(resolution,[],[f100,f80])).

fof(f80,plain,
    ( ! [X4,X0,X5,X1] :
        ( r2_hidden(k4_tarski(X4,X5),X1)
        | ~ r2_hidden(k4_tarski(X4,X5),X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X0)
        | ~ r1_tarski(X0,k8_relat_1(sK1,sK3))
        | ~ v1_relat_1(X0) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f99])).

fof(f103,plain,
    ( ~ spl6_1
    | ~ spl6_5
    | spl6_14 ),
    inference(avatar_split_clause,[],[f102,f95,f54,f34])).

fof(f102,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_5
    | spl6_14 ),
    inference(resolution,[],[f97,f55])).

fof(f97,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f95])).

fof(f101,plain,
    ( ~ spl6_14
    | spl6_15
    | spl6_6
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f93,f90,f58,f99,f95])).

fof(f90,plain,
    ( spl6_13
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2)
        | ~ r1_tarski(X2,X1)
        | ~ v1_relat_1(X2)
        | r1_tarski(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k8_relat_1(sK1,sK3))
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X0)
        | ~ v1_relat_1(k8_relat_1(sK0,sK2)) )
    | spl6_6
    | ~ spl6_13 ),
    inference(resolution,[],[f91,f60])).

fof(f60,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f91,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X2,X1)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2)
        | ~ v1_relat_1(X0) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,
    ( spl6_13
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f88,f79,f71,f90])).

fof(f71,plain,
    ( spl6_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2)
        | ~ r1_tarski(X2,X1)
        | ~ v1_relat_1(X2)
        | r1_tarski(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(resolution,[],[f80,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        | r1_tarski(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f81,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f27,f79])).

fof(f27,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f77,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

fof(f73,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

fof(f61,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

fof(f56,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f52,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f22,f34])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:52:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (32321)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.47  % (32322)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.48  % (32330)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % (32332)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.49  % (32324)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.50  % (32331)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.50  % (32320)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.50  % (32325)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.50  % (32335)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.22/0.50  % (32319)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.50  % (32334)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.50  % (32318)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.51  % (32334)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  % (32337)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.22/0.51  % (32317)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (32336)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (32328)WARNING: option uwaf not known.
% 0.22/0.51  % (32328)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.51  % (32329)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.51  % (32326)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (32327)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.52  % (32338)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f56,f61,f65,f69,f73,f77,f81,f92,f101,f103,f110,f117,f126,f138,f143])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ~spl6_1 | ~spl6_5 | spl6_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f139,f135,f54,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    spl6_1 <=> v1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    spl6_5 <=> ! [X1,X0] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    spl6_20 <=> v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | (~spl6_5 | spl6_20)),
% 0.22/0.52    inference(resolution,[],[f137,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | ~spl6_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f54])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ~v1_relat_1(k8_relat_1(sK1,sK2)) | spl6_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f135])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_20 | ~spl6_4 | ~spl6_10 | ~spl6_18),
% 0.22/0.52    inference(avatar_split_clause,[],[f127,f124,f75,f49,f135,f44,f39,f34])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    spl6_2 <=> v1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    spl6_3 <=> r1_tarski(sK2,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    spl6_4 <=> r1_tarski(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl6_10 <=> ! [X1,X0,X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    spl6_18 <=> ! [X0] : (~v1_relat_1(k8_relat_1(X0,sK2)) | ~r1_tarski(sK0,X0) | ~r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(sK1,sK3)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ~r1_tarski(sK0,sK1) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~r1_tarski(sK2,sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | (~spl6_10 | ~spl6_18)),
% 0.22/0.52    inference(resolution,[],[f125,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl6_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f75])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(sK1,sK3)) | ~r1_tarski(sK0,X0) | ~v1_relat_1(k8_relat_1(X0,sK2))) ) | ~spl6_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f124])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ~spl6_1 | spl6_18 | ~spl6_7 | ~spl6_17),
% 0.22/0.52    inference(avatar_split_clause,[],[f118,f115,f63,f124,f34])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    spl6_7 <=> ! [X1,X0,X2] : (r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    spl6_17 <=> ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k8_relat_1(sK0,sK2),X0) | ~r1_tarski(X0,k8_relat_1(sK1,sK3)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(k8_relat_1(X0,sK2)) | ~r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(sK1,sK3)) | ~r1_tarski(sK0,X0) | ~v1_relat_1(sK2)) ) | (~spl6_7 | ~spl6_17)),
% 0.22/0.52    inference(resolution,[],[f116,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) ) | ~spl6_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f63])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k8_relat_1(sK0,sK2),X0) | ~v1_relat_1(X0) | ~r1_tarski(X0,k8_relat_1(sK1,sK3))) ) | ~spl6_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f115])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    spl6_6 | ~spl6_14 | spl6_17 | ~spl6_8 | ~spl6_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f113,f108,f67,f115,f95,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl6_6 <=> r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl6_14 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    spl6_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    spl6_16 <=> ! [X1,X0] : (~r1_tarski(X0,k8_relat_1(sK1,sK3)) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1) | ~r1_tarski(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(X0,k8_relat_1(sK1,sK3)) | ~r1_tarski(k8_relat_1(sK0,sK2),X0) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))) ) | (~spl6_8 | ~spl6_16)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(X0,k8_relat_1(sK1,sK3)) | ~r1_tarski(k8_relat_1(sK0,sK2),X0) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) | ~v1_relat_1(k8_relat_1(sK0,sK2))) ) | (~spl6_8 | ~spl6_16)),
% 0.22/0.52    inference(resolution,[],[f109,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) ) | ~spl6_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f67])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1) | ~v1_relat_1(X0) | ~r1_tarski(X0,k8_relat_1(sK1,sK3)) | ~r1_tarski(X1,X0) | ~v1_relat_1(X1)) ) | ~spl6_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f108])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    spl6_16 | ~spl6_11 | ~spl6_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f105,f99,f79,f108])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl6_11 <=> ! [X1,X5,X0,X4] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    spl6_15 <=> ! [X0] : (~r1_tarski(X0,k8_relat_1(sK1,sK3)) | ~r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X0) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.52  % (32333)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k8_relat_1(sK1,sK3)) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X1) | ~r1_tarski(X1,X0) | ~v1_relat_1(X1)) ) | (~spl6_11 | ~spl6_15)),
% 0.22/0.52    inference(resolution,[],[f100,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) ) | ~spl6_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f79])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X0) | ~r1_tarski(X0,k8_relat_1(sK1,sK3)) | ~v1_relat_1(X0)) ) | ~spl6_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f99])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ~spl6_1 | ~spl6_5 | spl6_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f102,f95,f54,f34])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | (~spl6_5 | spl6_14)),
% 0.22/0.52    inference(resolution,[],[f97,f55])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl6_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f95])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ~spl6_14 | spl6_15 | spl6_6 | ~spl6_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f93,f90,f58,f99,f95])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    spl6_13 <=> ! [X1,X0,X2] : (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2) | ~r1_tarski(X2,X1) | ~v1_relat_1(X2) | r1_tarski(X0,X1) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k8_relat_1(sK1,sK3)) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),X0) | ~v1_relat_1(k8_relat_1(sK0,sK2))) ) | (spl6_6 | ~spl6_13)),
% 0.22/0.52    inference(resolution,[],[f91,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) | spl6_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f58])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2) | ~v1_relat_1(X0)) ) | ~spl6_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f90])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl6_13 | ~spl6_9 | ~spl6_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f88,f79,f71,f90])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    spl6_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2) | ~r1_tarski(X2,X1) | ~v1_relat_1(X2) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) ) | (~spl6_9 | ~spl6_11)),
% 0.22/0.52    inference(resolution,[],[f80,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) ) | ~spl6_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f71])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl6_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f27,f79])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(rectify,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl6_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f31,f75])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl6_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f29,f71])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl6_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f28,f67])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    spl6_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f32,f63])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ~spl6_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f26,f58])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    spl6_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f30,f54])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    spl6_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f25,f49])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    spl6_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f24,f44])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    r1_tarski(sK2,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    spl6_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f23,f39])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    v1_relat_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    spl6_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f22,f34])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (32334)------------------------------
% 0.22/0.52  % (32334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32334)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (32334)Memory used [KB]: 5373
% 0.22/0.52  % (32334)Time elapsed: 0.101 s
% 0.22/0.52  % (32334)------------------------------
% 0.22/0.52  % (32334)------------------------------
% 0.22/0.52  % (32314)Success in time 0.158 s
%------------------------------------------------------------------------------

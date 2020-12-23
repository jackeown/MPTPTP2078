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
% DateTime   : Thu Dec  3 12:55:21 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 168 expanded)
%              Number of leaves         :   19 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  294 ( 744 expanded)
%              Number of equality atoms :   15 (  56 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f48,f122,f135,f143,f147,f157,f167,f171])).

fof(f171,plain,
    ( ~ spl5_18
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f168,f117,f46,f141])).

fof(f141,plain,
    ( spl5_18
  <=> r2_hidden(sK4(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f46,plain,
    ( spl5_3
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f117,plain,
    ( spl5_14
  <=> ! [X3] :
        ( ~ r2_hidden(sK4(sK0),X3)
        | ~ v3_ordinal1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f168,plain,
    ( ~ r2_hidden(sK4(sK0),sK1)
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(resolution,[],[f118,f47])).

fof(f47,plain,
    ( v3_ordinal1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f118,plain,
    ( ! [X3] :
        ( ~ v3_ordinal1(X3)
        | ~ r2_hidden(sK4(sK0),X3) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f167,plain,
    ( spl5_1
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f165,f114,f38])).

fof(f38,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f114,plain,
    ( spl5_13
  <=> ! [X4] : ~ r2_hidden(X4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f165,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_13 ),
    inference(resolution,[],[f115,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f115,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f157,plain,
    ( spl5_1
    | spl5_17 ),
    inference(avatar_split_clause,[],[f154,f133,f38])).

fof(f133,plain,
    ( spl5_17
  <=> r2_hidden(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f154,plain,
    ( k1_xboole_0 = sK0
    | spl5_17 ),
    inference(resolution,[],[f148,f32])).

fof(f148,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl5_17 ),
    inference(resolution,[],[f134,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK4(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f23])).

fof(f23,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK4(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f134,plain,
    ( ~ r2_hidden(sK4(sK0),sK0)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f147,plain,
    ( ~ spl5_17
    | ~ spl5_2
    | spl5_18 ),
    inference(avatar_split_clause,[],[f146,f141,f42,f133])).

fof(f42,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f146,plain,
    ( ~ r2_hidden(sK4(sK0),sK0)
    | ~ spl5_2
    | spl5_18 ),
    inference(resolution,[],[f145,f43])).

fof(f43,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r2_hidden(sK4(sK0),X0) )
    | spl5_18 ),
    inference(resolution,[],[f142,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

% (8143)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

% (8148)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f8,plain,(
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

fof(f142,plain,
    ( ~ r2_hidden(sK4(sK0),sK1)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( ~ spl5_18
    | ~ spl5_3
    | spl5_16 ),
    inference(avatar_split_clause,[],[f137,f130,f46,f141])).

fof(f130,plain,
    ( spl5_16
  <=> v3_ordinal1(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f137,plain,
    ( ~ r2_hidden(sK4(sK0),sK1)
    | ~ spl5_3
    | spl5_16 ),
    inference(resolution,[],[f136,f47])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | ~ r2_hidden(sK4(sK0),X0) )
    | spl5_16 ),
    inference(resolution,[],[f131,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f131,plain,
    ( ~ v3_ordinal1(sK4(sK0))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f130])).

fof(f135,plain,
    ( ~ spl5_16
    | ~ spl5_17
    | spl5_15 ),
    inference(avatar_split_clause,[],[f126,f120,f133,f130])).

fof(f120,plain,
    ( spl5_15
  <=> r2_hidden(sK2(sK4(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f126,plain,
    ( ~ r2_hidden(sK4(sK0),sK0)
    | ~ v3_ordinal1(sK4(sK0))
    | spl5_15 ),
    inference(resolution,[],[f121,f29])).

fof(f29,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ! [X2] :
        ( ( ~ r1_ordinal1(X2,sK2(X2))
          & r2_hidden(sK2(X2),sK0)
          & v3_ordinal1(sK2(X2)) )
        | ~ r2_hidden(X2,sK0)
        | ~ v3_ordinal1(X2) )
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_ordinal1(X2,X3)
                & r2_hidden(X3,X0)
                & v3_ordinal1(X3) )
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,sK0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,sK0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r1_ordinal1(X2,X3)
          & r2_hidden(X3,sK0)
          & v3_ordinal1(X3) )
     => ( ~ r1_ordinal1(X2,sK2(X2))
        & r2_hidden(sK2(X2),sK0)
        & v3_ordinal1(sK2(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ~ ( ! [X2] :
                ( v3_ordinal1(X2)
               => ~ ( ! [X3] :
                        ( v3_ordinal1(X3)
                       => ( r2_hidden(X3,X0)
                         => r1_ordinal1(X2,X3) ) )
                    & r2_hidden(X2,X0) ) )
            & k1_xboole_0 != X0
            & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

% (8153)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f6,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ~ ( ! [X2] :
              ( v3_ordinal1(X2)
             => ~ ( ! [X3] :
                      ( v3_ordinal1(X3)
                     => ( r2_hidden(X3,X0)
                       => r1_ordinal1(X2,X3) ) )
                  & r2_hidden(X2,X0) ) )
          & k1_xboole_0 != X0
          & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_ordinal1)).

fof(f121,plain,
    ( ~ r2_hidden(sK2(sK4(sK0)),sK0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f120])).

% (8158)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f122,plain,
    ( spl5_13
    | spl5_14
    | ~ spl5_15
    | spl5_14
    | spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f110,f117,f114,f117,f120,f117,f114])).

fof(f110,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ r2_hidden(sK4(sK0),X0)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK4(sK0),X2)
      | ~ v3_ordinal1(X2)
      | ~ r2_hidden(sK2(sK4(sK0)),sK0)
      | ~ r2_hidden(sK4(sK0),X3)
      | ~ v3_ordinal1(X3)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(resolution,[],[f109,f35])).

% (8133)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f109,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(X0),sK0)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(sK4(X0),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(sK4(X0),X3)
      | ~ v3_ordinal1(X3)
      | ~ r2_hidden(sK2(sK4(X0)),X0)
      | ~ r2_hidden(sK4(X0),X4)
      | ~ v3_ordinal1(X4) ) ),
    inference(resolution,[],[f108,f33])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_ordinal1(sK4(X0))
      | ~ r2_hidden(sK4(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(sK4(X0),sK0)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(sK4(X0),X3)
      | ~ v3_ordinal1(X3)
      | ~ r2_hidden(sK2(sK4(X0)),X0) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK2(sK4(X0)),X0)
      | ~ r2_hidden(sK4(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(sK4(X0),sK0)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(sK4(X0),X3)
      | ~ v3_ordinal1(X3)
      | ~ r2_hidden(sK4(X0),sK0)
      | ~ v3_ordinal1(sK4(X0)) ) ),
    inference(resolution,[],[f105,f28])).

fof(f28,plain,(
    ! [X2] :
      ( v3_ordinal1(sK2(X2))
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_ordinal1(sK2(sK4(X0)))
      | ~ r2_hidden(sK2(sK4(X0)),X0)
      | ~ r2_hidden(sK4(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(sK4(X0),sK0)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(sK4(X0),X3)
      | ~ v3_ordinal1(X3) ) ),
    inference(resolution,[],[f104,f33])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_ordinal1(sK4(X1))
      | ~ v3_ordinal1(sK2(sK4(X1)))
      | ~ r2_hidden(sK2(sK4(X1)),X1)
      | ~ r2_hidden(sK4(X1),X2)
      | ~ v3_ordinal1(X2)
      | ~ r2_hidden(sK4(X1),sK0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f57,f30])).

fof(f30,plain,(
    ! [X2] :
      ( ~ r1_ordinal1(X2,sK2(X2))
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_ordinal1(sK4(X1),X2)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(sK4(X1),X3)
      | ~ v3_ordinal1(X3) ) ),
    inference(resolution,[],[f49,f33])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_ordinal1(sK4(X1))
      | ~ r2_hidden(X2,X1)
      | r1_ordinal1(sK4(X1),X0)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f36,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK4(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f26,f42])).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f27,f38])).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (8137)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (8144)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (8152)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (8134)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (8139)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.54  % (8152)Refutation found. Thanks to Tanya!
% 1.29/0.54  % SZS status Theorem for theBenchmark
% 1.29/0.54  % (8146)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.54  % (8136)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.54  % (8135)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.55  % (8157)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.55  % (8138)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.55  % (8161)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.55  % (8155)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.55  % (8150)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.55  % (8147)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.55  % (8151)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.55  % (8156)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.55  % (8162)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.55  % (8149)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.55  % SZS output start Proof for theBenchmark
% 1.29/0.55  fof(f172,plain,(
% 1.29/0.55    $false),
% 1.29/0.55    inference(avatar_sat_refutation,[],[f40,f44,f48,f122,f135,f143,f147,f157,f167,f171])).
% 1.29/0.55  fof(f171,plain,(
% 1.29/0.55    ~spl5_18 | ~spl5_3 | ~spl5_14),
% 1.29/0.55    inference(avatar_split_clause,[],[f168,f117,f46,f141])).
% 1.29/0.55  fof(f141,plain,(
% 1.29/0.55    spl5_18 <=> r2_hidden(sK4(sK0),sK1)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.29/0.55  fof(f46,plain,(
% 1.29/0.55    spl5_3 <=> v3_ordinal1(sK1)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.29/0.55  fof(f117,plain,(
% 1.29/0.55    spl5_14 <=> ! [X3] : (~r2_hidden(sK4(sK0),X3) | ~v3_ordinal1(X3))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.29/0.55  fof(f168,plain,(
% 1.29/0.55    ~r2_hidden(sK4(sK0),sK1) | (~spl5_3 | ~spl5_14)),
% 1.29/0.55    inference(resolution,[],[f118,f47])).
% 1.29/0.55  fof(f47,plain,(
% 1.29/0.55    v3_ordinal1(sK1) | ~spl5_3),
% 1.29/0.55    inference(avatar_component_clause,[],[f46])).
% 1.29/0.55  fof(f118,plain,(
% 1.29/0.55    ( ! [X3] : (~v3_ordinal1(X3) | ~r2_hidden(sK4(sK0),X3)) ) | ~spl5_14),
% 1.29/0.55    inference(avatar_component_clause,[],[f117])).
% 1.29/0.55  fof(f167,plain,(
% 1.29/0.55    spl5_1 | ~spl5_13),
% 1.29/0.55    inference(avatar_split_clause,[],[f165,f114,f38])).
% 1.29/0.55  fof(f38,plain,(
% 1.29/0.55    spl5_1 <=> k1_xboole_0 = sK0),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.29/0.55  fof(f114,plain,(
% 1.29/0.55    spl5_13 <=> ! [X4] : ~r2_hidden(X4,sK0)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.29/0.55  fof(f165,plain,(
% 1.29/0.55    k1_xboole_0 = sK0 | ~spl5_13),
% 1.29/0.55    inference(resolution,[],[f115,f32])).
% 1.29/0.55  fof(f32,plain,(
% 1.29/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.29/0.55    inference(cnf_transformation,[],[f22])).
% 1.29/0.55  fof(f22,plain,(
% 1.29/0.55    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.29/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).
% 1.29/0.55  fof(f21,plain,(
% 1.29/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.29/0.55    introduced(choice_axiom,[])).
% 1.29/0.55  fof(f13,plain,(
% 1.29/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.29/0.55    inference(ennf_transformation,[],[f2])).
% 1.29/0.55  fof(f2,axiom,(
% 1.29/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.29/0.55  fof(f115,plain,(
% 1.29/0.55    ( ! [X4] : (~r2_hidden(X4,sK0)) ) | ~spl5_13),
% 1.29/0.55    inference(avatar_component_clause,[],[f114])).
% 1.29/0.55  fof(f157,plain,(
% 1.29/0.55    spl5_1 | spl5_17),
% 1.29/0.55    inference(avatar_split_clause,[],[f154,f133,f38])).
% 1.29/0.55  fof(f133,plain,(
% 1.29/0.55    spl5_17 <=> r2_hidden(sK4(sK0),sK0)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.29/0.55  fof(f154,plain,(
% 1.29/0.55    k1_xboole_0 = sK0 | spl5_17),
% 1.29/0.55    inference(resolution,[],[f148,f32])).
% 1.29/0.55  fof(f148,plain,(
% 1.29/0.55    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl5_17),
% 1.29/0.55    inference(resolution,[],[f134,f35])).
% 1.29/0.55  fof(f35,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X1),X1) | ~r2_hidden(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f24])).
% 1.29/0.55  fof(f24,plain,(
% 1.29/0.55    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK4(X1),X1)) | ~r2_hidden(X0,X1))),
% 1.29/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f23])).
% 1.29/0.55  fof(f23,plain,(
% 1.29/0.55    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK4(X1),X1)))),
% 1.29/0.55    introduced(choice_axiom,[])).
% 1.29/0.55  fof(f17,plain,(
% 1.29/0.55    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f3])).
% 1.29/0.55  fof(f3,axiom,(
% 1.29/0.55    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 1.29/0.55  fof(f134,plain,(
% 1.29/0.55    ~r2_hidden(sK4(sK0),sK0) | spl5_17),
% 1.29/0.55    inference(avatar_component_clause,[],[f133])).
% 1.29/0.55  fof(f147,plain,(
% 1.29/0.55    ~spl5_17 | ~spl5_2 | spl5_18),
% 1.29/0.55    inference(avatar_split_clause,[],[f146,f141,f42,f133])).
% 1.29/0.55  fof(f42,plain,(
% 1.29/0.55    spl5_2 <=> r1_tarski(sK0,sK1)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.29/0.55  fof(f146,plain,(
% 1.29/0.55    ~r2_hidden(sK4(sK0),sK0) | (~spl5_2 | spl5_18)),
% 1.29/0.55    inference(resolution,[],[f145,f43])).
% 1.29/0.55  fof(f43,plain,(
% 1.29/0.55    r1_tarski(sK0,sK1) | ~spl5_2),
% 1.29/0.55    inference(avatar_component_clause,[],[f42])).
% 1.29/0.55  fof(f145,plain,(
% 1.29/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r2_hidden(sK4(sK0),X0)) ) | spl5_18),
% 1.29/0.55    inference(resolution,[],[f142,f34])).
% 1.29/0.55  fof(f34,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f16])).
% 1.29/0.55  % (8143)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.55  fof(f16,plain,(
% 1.29/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f8])).
% 1.29/0.55  % (8148)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.55  fof(f8,plain,(
% 1.29/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.29/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 1.29/0.55  fof(f1,axiom,(
% 1.29/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.29/0.55  fof(f142,plain,(
% 1.29/0.55    ~r2_hidden(sK4(sK0),sK1) | spl5_18),
% 1.29/0.55    inference(avatar_component_clause,[],[f141])).
% 1.29/0.55  fof(f143,plain,(
% 1.29/0.55    ~spl5_18 | ~spl5_3 | spl5_16),
% 1.29/0.55    inference(avatar_split_clause,[],[f137,f130,f46,f141])).
% 1.29/0.55  fof(f130,plain,(
% 1.29/0.55    spl5_16 <=> v3_ordinal1(sK4(sK0))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.29/0.55  fof(f137,plain,(
% 1.29/0.55    ~r2_hidden(sK4(sK0),sK1) | (~spl5_3 | spl5_16)),
% 1.29/0.55    inference(resolution,[],[f136,f47])).
% 1.29/0.55  fof(f136,plain,(
% 1.29/0.55    ( ! [X0] : (~v3_ordinal1(X0) | ~r2_hidden(sK4(sK0),X0)) ) | spl5_16),
% 1.29/0.55    inference(resolution,[],[f131,f33])).
% 1.29/0.55  fof(f33,plain,(
% 1.29/0.55    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f15])).
% 1.29/0.55  fof(f15,plain,(
% 1.29/0.55    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 1.29/0.55    inference(flattening,[],[f14])).
% 1.29/0.55  fof(f14,plain,(
% 1.29/0.55    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f4])).
% 1.29/0.55  fof(f4,axiom,(
% 1.29/0.55    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 1.29/0.55  fof(f131,plain,(
% 1.29/0.55    ~v3_ordinal1(sK4(sK0)) | spl5_16),
% 1.29/0.55    inference(avatar_component_clause,[],[f130])).
% 1.29/0.55  fof(f135,plain,(
% 1.29/0.55    ~spl5_16 | ~spl5_17 | spl5_15),
% 1.29/0.55    inference(avatar_split_clause,[],[f126,f120,f133,f130])).
% 1.29/0.55  fof(f120,plain,(
% 1.29/0.55    spl5_15 <=> r2_hidden(sK2(sK4(sK0)),sK0)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.29/0.55  fof(f126,plain,(
% 1.29/0.55    ~r2_hidden(sK4(sK0),sK0) | ~v3_ordinal1(sK4(sK0)) | spl5_15),
% 1.29/0.55    inference(resolution,[],[f121,f29])).
% 1.29/0.55  fof(f29,plain,(
% 1.29/0.55    ( ! [X2] : (r2_hidden(sK2(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f20])).
% 1.29/0.55  fof(f20,plain,(
% 1.29/0.55    ! [X2] : ((~r1_ordinal1(X2,sK2(X2)) & r2_hidden(sK2(X2),sK0) & v3_ordinal1(sK2(X2))) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1) & v3_ordinal1(sK1)),
% 1.29/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19,f18])).
% 1.29/0.55  fof(f18,plain,(
% 1.29/0.55    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1)) => (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,sK0) & v3_ordinal1(X3)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1) & v3_ordinal1(sK1))),
% 1.29/0.55    introduced(choice_axiom,[])).
% 1.29/0.55  fof(f19,plain,(
% 1.29/0.55    ! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,sK0) & v3_ordinal1(X3)) => (~r1_ordinal1(X2,sK2(X2)) & r2_hidden(sK2(X2),sK0) & v3_ordinal1(sK2(X2))))),
% 1.29/0.55    introduced(choice_axiom,[])).
% 1.29/0.55  fof(f10,plain,(
% 1.29/0.55    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1))),
% 1.29/0.55    inference(flattening,[],[f9])).
% 1.29/0.55  fof(f9,plain,(
% 1.29/0.55    ? [X0,X1] : ((! [X2] : ((? [X3] : ((~r1_ordinal1(X2,X3) & r2_hidden(X3,X0)) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0)) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) & v3_ordinal1(X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f7])).
% 1.29/0.55  fof(f7,negated_conjecture,(
% 1.29/0.55    ~! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 1.29/0.55    inference(negated_conjecture,[],[f6])).
% 1.29/0.55  % (8153)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.55  fof(f6,conjecture,(
% 1.29/0.55    ! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_ordinal1)).
% 1.29/0.56  fof(f121,plain,(
% 1.29/0.56    ~r2_hidden(sK2(sK4(sK0)),sK0) | spl5_15),
% 1.29/0.56    inference(avatar_component_clause,[],[f120])).
% 1.29/0.56  % (8158)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.56  fof(f122,plain,(
% 1.29/0.56    spl5_13 | spl5_14 | ~spl5_15 | spl5_14 | spl5_13 | spl5_14),
% 1.29/0.56    inference(avatar_split_clause,[],[f110,f117,f114,f117,f120,f117,f114])).
% 1.29/0.56  fof(f110,plain,(
% 1.29/0.56    ( ! [X4,X2,X0,X3,X1] : (~v3_ordinal1(X0) | ~r2_hidden(sK4(sK0),X0) | ~r2_hidden(X1,sK0) | ~r2_hidden(sK4(sK0),X2) | ~v3_ordinal1(X2) | ~r2_hidden(sK2(sK4(sK0)),sK0) | ~r2_hidden(sK4(sK0),X3) | ~v3_ordinal1(X3) | ~r2_hidden(X4,sK0)) )),
% 1.29/0.56    inference(resolution,[],[f109,f35])).
% 1.29/0.56  % (8133)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.56  fof(f109,plain,(
% 1.29/0.56    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(sK4(X0),sK0) | ~v3_ordinal1(X1) | ~r2_hidden(sK4(X0),X1) | ~r2_hidden(X2,X0) | ~r2_hidden(sK4(X0),X3) | ~v3_ordinal1(X3) | ~r2_hidden(sK2(sK4(X0)),X0) | ~r2_hidden(sK4(X0),X4) | ~v3_ordinal1(X4)) )),
% 1.29/0.56    inference(resolution,[],[f108,f33])).
% 1.29/0.56  fof(f108,plain,(
% 1.29/0.56    ( ! [X2,X0,X3,X1] : (~v3_ordinal1(sK4(X0)) | ~r2_hidden(sK4(X0),X1) | ~v3_ordinal1(X1) | ~r2_hidden(sK4(X0),sK0) | ~r2_hidden(X2,X0) | ~r2_hidden(sK4(X0),X3) | ~v3_ordinal1(X3) | ~r2_hidden(sK2(sK4(X0)),X0)) )),
% 1.29/0.56    inference(duplicate_literal_removal,[],[f106])).
% 1.29/0.56  fof(f106,plain,(
% 1.29/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK2(sK4(X0)),X0) | ~r2_hidden(sK4(X0),X1) | ~v3_ordinal1(X1) | ~r2_hidden(sK4(X0),sK0) | ~r2_hidden(X2,X0) | ~r2_hidden(sK4(X0),X3) | ~v3_ordinal1(X3) | ~r2_hidden(sK4(X0),sK0) | ~v3_ordinal1(sK4(X0))) )),
% 1.29/0.56    inference(resolution,[],[f105,f28])).
% 1.29/0.56  fof(f28,plain,(
% 1.29/0.56    ( ! [X2] : (v3_ordinal1(sK2(X2)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f20])).
% 1.29/0.56  fof(f105,plain,(
% 1.29/0.56    ( ! [X2,X0,X3,X1] : (~v3_ordinal1(sK2(sK4(X0))) | ~r2_hidden(sK2(sK4(X0)),X0) | ~r2_hidden(sK4(X0),X1) | ~v3_ordinal1(X1) | ~r2_hidden(sK4(X0),sK0) | ~r2_hidden(X2,X0) | ~r2_hidden(sK4(X0),X3) | ~v3_ordinal1(X3)) )),
% 1.29/0.56    inference(resolution,[],[f104,f33])).
% 1.29/0.56  fof(f104,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~v3_ordinal1(sK4(X1)) | ~v3_ordinal1(sK2(sK4(X1))) | ~r2_hidden(sK2(sK4(X1)),X1) | ~r2_hidden(sK4(X1),X2) | ~v3_ordinal1(X2) | ~r2_hidden(sK4(X1),sK0) | ~r2_hidden(X0,X1)) )),
% 1.29/0.56    inference(resolution,[],[f57,f30])).
% 1.29/0.56  fof(f30,plain,(
% 1.29/0.56    ( ! [X2] : (~r1_ordinal1(X2,sK2(X2)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f20])).
% 1.29/0.56  fof(f57,plain,(
% 1.29/0.56    ( ! [X2,X0,X3,X1] : (r1_ordinal1(sK4(X1),X2) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X1) | ~r2_hidden(sK4(X1),X3) | ~v3_ordinal1(X3)) )),
% 1.29/0.56    inference(resolution,[],[f49,f33])).
% 1.29/0.56  fof(f49,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~v3_ordinal1(sK4(X1)) | ~r2_hidden(X2,X1) | r1_ordinal1(sK4(X1),X0) | ~v3_ordinal1(X0) | ~r2_hidden(X0,X1)) )),
% 1.29/0.56    inference(resolution,[],[f36,f31])).
% 1.29/0.56  fof(f31,plain,(
% 1.29/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f12])).
% 1.29/0.56  fof(f12,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.29/0.56    inference(flattening,[],[f11])).
% 1.29/0.56  fof(f11,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f5])).
% 1.29/0.56  fof(f5,axiom,(
% 1.29/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.29/0.56  fof(f36,plain,(
% 1.29/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f24])).
% 1.29/0.56  fof(f48,plain,(
% 1.29/0.56    spl5_3),
% 1.29/0.56    inference(avatar_split_clause,[],[f25,f46])).
% 1.29/0.56  fof(f25,plain,(
% 1.29/0.56    v3_ordinal1(sK1)),
% 1.29/0.56    inference(cnf_transformation,[],[f20])).
% 1.29/0.56  fof(f44,plain,(
% 1.29/0.56    spl5_2),
% 1.29/0.56    inference(avatar_split_clause,[],[f26,f42])).
% 1.29/0.56  fof(f26,plain,(
% 1.29/0.56    r1_tarski(sK0,sK1)),
% 1.29/0.56    inference(cnf_transformation,[],[f20])).
% 1.29/0.56  fof(f40,plain,(
% 1.29/0.56    ~spl5_1),
% 1.29/0.56    inference(avatar_split_clause,[],[f27,f38])).
% 1.29/0.56  fof(f27,plain,(
% 1.29/0.56    k1_xboole_0 != sK0),
% 1.29/0.56    inference(cnf_transformation,[],[f20])).
% 1.29/0.56  % SZS output end Proof for theBenchmark
% 1.29/0.56  % (8152)------------------------------
% 1.29/0.56  % (8152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (8152)Termination reason: Refutation
% 1.29/0.56  
% 1.29/0.56  % (8152)Memory used [KB]: 10874
% 1.29/0.56  % (8152)Time elapsed: 0.136 s
% 1.29/0.56  % (8152)------------------------------
% 1.29/0.56  % (8152)------------------------------
% 1.29/0.56  % (8124)Success in time 0.19 s
%------------------------------------------------------------------------------

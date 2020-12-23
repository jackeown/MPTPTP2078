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
% DateTime   : Thu Dec  3 12:52:40 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 171 expanded)
%              Number of leaves         :   21 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  375 ( 844 expanded)
%              Number of equality atoms :   92 ( 272 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f367,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f100,f105,f163,f177,f189,f301,f334,f354])).

fof(f354,plain,
    ( ~ spl10_19
    | spl10_22
    | ~ spl10_34 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl10_19
    | spl10_22
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f162,f176,f333])).

fof(f333,plain,
    ( ! [X3] :
        ( k1_funct_1(sK2,X3) = X3
        | ~ r2_hidden(X3,sK0) )
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl10_34
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | k1_funct_1(sK2,X3) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f176,plain,
    ( sK8(sK0,sK2) != k1_funct_1(sK2,sK8(sK0,sK2))
    | spl10_22 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl10_22
  <=> sK8(sK0,sK2) = k1_funct_1(sK2,sK8(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f162,plain,
    ( r2_hidden(sK8(sK0,sK2),sK0)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl10_19
  <=> r2_hidden(sK8(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f334,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_8
    | spl10_34
    | ~ spl10_7
    | ~ spl10_33 ),
    inference(avatar_split_clause,[],[f330,f299,f87,f332,f92,f62,f57])).

fof(f57,plain,
    ( spl10_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f62,plain,
    ( spl10_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f92,plain,
    ( spl10_8
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f87,plain,
    ( spl10_7
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f299,plain,
    ( spl10_33
  <=> ! [X3,X4] :
        ( ~ r2_hidden(k1_funct_1(sK2,X3),sK0)
        | ~ r2_hidden(X3,sK0)
        | k1_funct_1(sK2,X3) = X4
        | k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4)
        | ~ r2_hidden(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f330,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | k1_funct_1(sK2,X3) = X3
        | ~ r1_tarski(k2_relat_1(sK2),sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_7
    | ~ spl10_33 ),
    inference(duplicate_literal_removal,[],[f329])).

fof(f329,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | ~ r2_hidden(X3,sK0)
        | k1_funct_1(sK2,X3) = X3
        | ~ r1_tarski(k2_relat_1(sK2),sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_7
    | ~ spl10_33 ),
    inference(forward_demodulation,[],[f325,f89])).

fof(f89,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f325,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | k1_funct_1(sK2,X3) = X3
        | ~ r1_tarski(k2_relat_1(sK2),sK0)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl10_33 ),
    inference(resolution,[],[f320,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f320,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(sK2,X0),X1)
        | ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) = X0
        | ~ r1_tarski(X1,sK0) )
    | ~ spl10_33 ),
    inference(resolution,[],[f315,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f315,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK2,X0),sK0)
        | k1_funct_1(sK2,X0) = X0
        | ~ r2_hidden(X0,sK0) )
    | ~ spl10_33 ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) = X0
        | ~ r2_hidden(k1_funct_1(sK2,X0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl10_33 ),
    inference(equality_resolution,[],[f300])).

fof(f300,plain,
    ( ! [X4,X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4)
        | ~ r2_hidden(X3,sK0)
        | k1_funct_1(sK2,X3) = X4
        | ~ r2_hidden(k1_funct_1(sK2,X3),sK0)
        | ~ r2_hidden(X4,sK0) )
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f299])).

% (14018)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (14017)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (14029)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (14022)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (14016)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (14021)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (14021)Refutation not found, incomplete strategy% (14021)------------------------------
% (14021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14021)Termination reason: Refutation not found, incomplete strategy

% (14021)Memory used [KB]: 10746
% (14021)Time elapsed: 0.150 s
% (14021)------------------------------
% (14021)------------------------------
% (14014)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (14019)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f301,plain,
    ( ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_33
    | ~ spl10_6
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f200,f187,f82,f299,f77,f72,f67])).

fof(f67,plain,
    ( spl10_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f72,plain,
    ( spl10_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f77,plain,
    ( spl10_5
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f82,plain,
    ( spl10_6
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f187,plain,
    ( spl10_25
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f200,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k1_funct_1(sK2,X3),sK0)
        | ~ r2_hidden(X4,sK0)
        | k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | k1_funct_1(sK2,X3) = X4
        | ~ v2_funct_1(sK1)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl10_6
    | ~ spl10_25 ),
    inference(forward_demodulation,[],[f199,f84])).

fof(f84,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f199,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,sK0)
        | k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4)
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(k1_funct_1(sK2,X3),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | k1_funct_1(sK2,X3) = X4
        | ~ v2_funct_1(sK1)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl10_6
    | ~ spl10_25 ),
    inference(forward_demodulation,[],[f195,f84])).

% (14027)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (14011)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f195,plain,
    ( ! [X4,X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4)
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(X4,k1_relat_1(sK1))
        | ~ r2_hidden(k1_funct_1(sK2,X3),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | k1_funct_1(sK2,X3) = X4
        | ~ v2_funct_1(sK1)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl10_25 ),
    inference(superposition,[],[f29,f188])).

fof(f188,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f187])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f189,plain,
    ( ~ spl10_4
    | ~ spl10_2
    | ~ spl10_1
    | ~ spl10_5
    | spl10_25
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f119,f102,f82,f187,f77,f57,f62,f72])).

fof(f102,plain,
    ( spl10_10
  <=> sK1 = k5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK1) )
    | ~ spl10_6
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f118,f84])).

fof(f118,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl10_10 ),
    inference(superposition,[],[f44,f104])).

fof(f104,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(f177,plain,
    ( spl10_9
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_22
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f113,f87,f174,f62,f57,f97])).

fof(f97,plain,
    ( spl10_9
  <=> sK2 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f113,plain,
    ( sK8(sK0,sK2) != k1_funct_1(sK2,sK8(sK0,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k6_relat_1(sK0)
    | ~ spl10_7 ),
    inference(superposition,[],[f54,f89])).

fof(f54,plain,(
    ! [X1] :
      ( sK8(k1_relat_1(X1),X1) != k1_funct_1(X1,sK8(k1_relat_1(X1),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK8(X0,X1) != k1_funct_1(X1,sK8(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f163,plain,
    ( spl10_9
    | ~ spl10_1
    | ~ spl10_2
    | spl10_19
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f112,f87,f160,f62,f57,f97])).

fof(f112,plain,
    ( r2_hidden(sK8(sK0,sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k6_relat_1(sK0)
    | ~ spl10_7 ),
    inference(superposition,[],[f55,f89])).

fof(f55,plain,(
    ! [X1] :
      ( r2_hidden(sK8(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK8(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f105,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f25,f102])).

fof(f25,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

fof(f100,plain,(
    ~ spl10_9 ),
    inference(avatar_split_clause,[],[f26,f97])).

fof(f26,plain,(
    sK2 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f23,f92])).

fof(f23,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f90,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f22,f87])).

fof(f22,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f85,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f21,f82])).

fof(f21,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f28,f77])).

fof(f28,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f27,f72])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f24,f67])).

fof(f24,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f20,f62])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f19,f57])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:19:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (14013)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (14028)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (14009)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (14012)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (14010)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (14020)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (14004)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (14008)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (14031)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (14006)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (14007)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (14033)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (14032)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (14005)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (14023)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (14026)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (14025)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.55  % (14024)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.55  % (14015)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.55  % (14030)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.55  % (14026)Refutation found. Thanks to Tanya!
% 1.45/0.55  % SZS status Theorem for theBenchmark
% 1.45/0.55  % SZS output start Proof for theBenchmark
% 1.45/0.55  fof(f367,plain,(
% 1.45/0.55    $false),
% 1.45/0.55    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f100,f105,f163,f177,f189,f301,f334,f354])).
% 1.45/0.55  fof(f354,plain,(
% 1.45/0.55    ~spl10_19 | spl10_22 | ~spl10_34),
% 1.45/0.55    inference(avatar_contradiction_clause,[],[f335])).
% 1.45/0.55  fof(f335,plain,(
% 1.45/0.55    $false | (~spl10_19 | spl10_22 | ~spl10_34)),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f162,f176,f333])).
% 1.45/0.55  fof(f333,plain,(
% 1.45/0.55    ( ! [X3] : (k1_funct_1(sK2,X3) = X3 | ~r2_hidden(X3,sK0)) ) | ~spl10_34),
% 1.45/0.55    inference(avatar_component_clause,[],[f332])).
% 1.45/0.55  fof(f332,plain,(
% 1.45/0.55    spl10_34 <=> ! [X3] : (~r2_hidden(X3,sK0) | k1_funct_1(sK2,X3) = X3)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 1.45/0.55  fof(f176,plain,(
% 1.45/0.55    sK8(sK0,sK2) != k1_funct_1(sK2,sK8(sK0,sK2)) | spl10_22),
% 1.45/0.55    inference(avatar_component_clause,[],[f174])).
% 1.45/0.55  fof(f174,plain,(
% 1.45/0.55    spl10_22 <=> sK8(sK0,sK2) = k1_funct_1(sK2,sK8(sK0,sK2))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 1.45/0.55  fof(f162,plain,(
% 1.45/0.55    r2_hidden(sK8(sK0,sK2),sK0) | ~spl10_19),
% 1.45/0.55    inference(avatar_component_clause,[],[f160])).
% 1.45/0.55  fof(f160,plain,(
% 1.45/0.55    spl10_19 <=> r2_hidden(sK8(sK0,sK2),sK0)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 1.45/0.55  fof(f334,plain,(
% 1.45/0.55    ~spl10_1 | ~spl10_2 | ~spl10_8 | spl10_34 | ~spl10_7 | ~spl10_33),
% 1.45/0.55    inference(avatar_split_clause,[],[f330,f299,f87,f332,f92,f62,f57])).
% 1.45/0.55  fof(f57,plain,(
% 1.45/0.55    spl10_1 <=> v1_relat_1(sK2)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.45/0.55  fof(f62,plain,(
% 1.45/0.55    spl10_2 <=> v1_funct_1(sK2)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.45/0.55  fof(f92,plain,(
% 1.45/0.55    spl10_8 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.45/0.55  fof(f87,plain,(
% 1.45/0.55    spl10_7 <=> sK0 = k1_relat_1(sK2)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.45/0.55  fof(f299,plain,(
% 1.45/0.55    spl10_33 <=> ! [X3,X4] : (~r2_hidden(k1_funct_1(sK2,X3),sK0) | ~r2_hidden(X3,sK0) | k1_funct_1(sK2,X3) = X4 | k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4) | ~r2_hidden(X4,sK0))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 1.45/0.55  fof(f330,plain,(
% 1.45/0.55    ( ! [X3] : (~r2_hidden(X3,sK0) | k1_funct_1(sK2,X3) = X3 | ~r1_tarski(k2_relat_1(sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl10_7 | ~spl10_33)),
% 1.45/0.55    inference(duplicate_literal_removal,[],[f329])).
% 1.45/0.55  fof(f329,plain,(
% 1.45/0.55    ( ! [X3] : (~r2_hidden(X3,sK0) | ~r2_hidden(X3,sK0) | k1_funct_1(sK2,X3) = X3 | ~r1_tarski(k2_relat_1(sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl10_7 | ~spl10_33)),
% 1.45/0.55    inference(forward_demodulation,[],[f325,f89])).
% 1.45/0.55  fof(f89,plain,(
% 1.45/0.55    sK0 = k1_relat_1(sK2) | ~spl10_7),
% 1.45/0.55    inference(avatar_component_clause,[],[f87])).
% 1.45/0.55  fof(f325,plain,(
% 1.45/0.55    ( ! [X3] : (~r2_hidden(X3,sK0) | k1_funct_1(sK2,X3) = X3 | ~r1_tarski(k2_relat_1(sK2),sK0) | ~v1_funct_1(sK2) | ~r2_hidden(X3,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl10_33),
% 1.45/0.55    inference(resolution,[],[f320,f49])).
% 1.45/0.55  fof(f49,plain,(
% 1.45/0.55    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.45/0.55    inference(equality_resolution,[],[f48])).
% 1.45/0.55  fof(f48,plain,(
% 1.45/0.55    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 1.45/0.55    inference(equality_resolution,[],[f39])).
% 1.45/0.55  fof(f39,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.45/0.55    inference(cnf_transformation,[],[f13])).
% 1.45/0.55  fof(f13,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.45/0.55    inference(flattening,[],[f12])).
% 1.45/0.55  fof(f12,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f2])).
% 1.45/0.55  fof(f2,axiom,(
% 1.45/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.45/0.55  fof(f320,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r2_hidden(k1_funct_1(sK2,X0),X1) | ~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) = X0 | ~r1_tarski(X1,sK0)) ) | ~spl10_33),
% 1.45/0.55    inference(resolution,[],[f315,f45])).
% 1.45/0.55  fof(f45,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f18])).
% 1.45/0.55  fof(f18,plain,(
% 1.45/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f1])).
% 1.45/0.55  fof(f1,axiom,(
% 1.45/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.45/0.55  fof(f315,plain,(
% 1.45/0.55    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,X0),sK0) | k1_funct_1(sK2,X0) = X0 | ~r2_hidden(X0,sK0)) ) | ~spl10_33),
% 1.45/0.55    inference(duplicate_literal_removal,[],[f314])).
% 1.45/0.55  fof(f314,plain,(
% 1.45/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) = X0 | ~r2_hidden(k1_funct_1(sK2,X0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl10_33),
% 1.45/0.55    inference(equality_resolution,[],[f300])).
% 1.45/0.55  fof(f300,plain,(
% 1.45/0.55    ( ! [X4,X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4) | ~r2_hidden(X3,sK0) | k1_funct_1(sK2,X3) = X4 | ~r2_hidden(k1_funct_1(sK2,X3),sK0) | ~r2_hidden(X4,sK0)) ) | ~spl10_33),
% 1.45/0.55    inference(avatar_component_clause,[],[f299])).
% 1.45/0.55  % (14018)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.45/0.56  % (14017)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.56  % (14029)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.56  % (14022)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.56  % (14016)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.56  % (14021)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.56  % (14021)Refutation not found, incomplete strategy% (14021)------------------------------
% 1.45/0.56  % (14021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (14021)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (14021)Memory used [KB]: 10746
% 1.45/0.56  % (14021)Time elapsed: 0.150 s
% 1.45/0.56  % (14021)------------------------------
% 1.45/0.56  % (14021)------------------------------
% 1.45/0.57  % (14014)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.57  % (14019)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.62/0.57  fof(f301,plain,(
% 1.62/0.57    ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_33 | ~spl10_6 | ~spl10_25),
% 1.62/0.57    inference(avatar_split_clause,[],[f200,f187,f82,f299,f77,f72,f67])).
% 1.62/0.57  fof(f67,plain,(
% 1.62/0.57    spl10_3 <=> v2_funct_1(sK1)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.62/0.57  fof(f72,plain,(
% 1.62/0.57    spl10_4 <=> v1_relat_1(sK1)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.62/0.57  fof(f77,plain,(
% 1.62/0.57    spl10_5 <=> v1_funct_1(sK1)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.62/0.57  fof(f82,plain,(
% 1.62/0.57    spl10_6 <=> sK0 = k1_relat_1(sK1)),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.62/0.57  fof(f187,plain,(
% 1.62/0.57    spl10_25 <=> ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)))),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 1.62/0.57  fof(f200,plain,(
% 1.62/0.57    ( ! [X4,X3] : (~r2_hidden(k1_funct_1(sK2,X3),sK0) | ~r2_hidden(X4,sK0) | k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_funct_1(sK2,X3) = X4 | ~v2_funct_1(sK1) | ~r2_hidden(X3,sK0)) ) | (~spl10_6 | ~spl10_25)),
% 1.62/0.57    inference(forward_demodulation,[],[f199,f84])).
% 1.62/0.57  fof(f84,plain,(
% 1.62/0.57    sK0 = k1_relat_1(sK1) | ~spl10_6),
% 1.62/0.57    inference(avatar_component_clause,[],[f82])).
% 1.62/0.57  fof(f199,plain,(
% 1.62/0.57    ( ! [X4,X3] : (~r2_hidden(X4,sK0) | k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4) | ~v1_funct_1(sK1) | ~r2_hidden(k1_funct_1(sK2,X3),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | k1_funct_1(sK2,X3) = X4 | ~v2_funct_1(sK1) | ~r2_hidden(X3,sK0)) ) | (~spl10_6 | ~spl10_25)),
% 1.62/0.57    inference(forward_demodulation,[],[f195,f84])).
% 1.62/0.57  % (14027)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.62/0.58  % (14011)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.62/0.58  fof(f195,plain,(
% 1.62/0.58    ( ! [X4,X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4) | ~v1_funct_1(sK1) | ~r2_hidden(X4,k1_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK2,X3),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | k1_funct_1(sK2,X3) = X4 | ~v2_funct_1(sK1) | ~r2_hidden(X3,sK0)) ) | ~spl10_25),
% 1.62/0.58    inference(superposition,[],[f29,f188])).
% 1.62/0.58  fof(f188,plain,(
% 1.62/0.58    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) | ~r2_hidden(X0,sK0)) ) | ~spl10_25),
% 1.62/0.58    inference(avatar_component_clause,[],[f187])).
% 1.62/0.58  fof(f29,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X2,k1_relat_1(X0)) | ~v1_relat_1(X0) | X1 = X2 | ~v2_funct_1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f11])).
% 1.62/0.58  fof(f11,plain,(
% 1.62/0.58    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.58    inference(flattening,[],[f10])).
% 1.62/0.58  fof(f10,plain,(
% 1.62/0.58    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f3])).
% 1.62/0.58  fof(f3,axiom,(
% 1.62/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 1.62/0.58  fof(f189,plain,(
% 1.62/0.58    ~spl10_4 | ~spl10_2 | ~spl10_1 | ~spl10_5 | spl10_25 | ~spl10_6 | ~spl10_10),
% 1.62/0.58    inference(avatar_split_clause,[],[f119,f102,f82,f187,f77,f57,f62,f72])).
% 1.62/0.58  fof(f102,plain,(
% 1.62/0.58    spl10_10 <=> sK1 = k5_relat_1(sK2,sK1)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 1.62/0.58  fof(f119,plain,(
% 1.62/0.58    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1)) ) | (~spl10_6 | ~spl10_10)),
% 1.62/0.58    inference(forward_demodulation,[],[f118,f84])).
% 1.62/0.58  fof(f118,plain,(
% 1.62/0.58    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl10_10),
% 1.62/0.58    inference(superposition,[],[f44,f104])).
% 1.62/0.58  fof(f104,plain,(
% 1.62/0.58    sK1 = k5_relat_1(sK2,sK1) | ~spl10_10),
% 1.62/0.58    inference(avatar_component_clause,[],[f102])).
% 1.62/0.58  fof(f44,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_relat_1(X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f17,plain,(
% 1.62/0.58    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.62/0.58    inference(flattening,[],[f16])).
% 1.62/0.58  fof(f16,plain,(
% 1.62/0.58    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.62/0.58    inference(ennf_transformation,[],[f4])).
% 1.62/0.58  fof(f4,axiom,(
% 1.62/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
% 1.62/0.58  fof(f177,plain,(
% 1.62/0.58    spl10_9 | ~spl10_1 | ~spl10_2 | ~spl10_22 | ~spl10_7),
% 1.62/0.58    inference(avatar_split_clause,[],[f113,f87,f174,f62,f57,f97])).
% 1.62/0.58  fof(f97,plain,(
% 1.62/0.58    spl10_9 <=> sK2 = k6_relat_1(sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 1.62/0.58  fof(f113,plain,(
% 1.62/0.58    sK8(sK0,sK2) != k1_funct_1(sK2,sK8(sK0,sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k6_relat_1(sK0) | ~spl10_7),
% 1.62/0.58    inference(superposition,[],[f54,f89])).
% 1.62/0.58  fof(f54,plain,(
% 1.62/0.58    ( ! [X1] : (sK8(k1_relat_1(X1),X1) != k1_funct_1(X1,sK8(k1_relat_1(X1),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 1.62/0.58    inference(equality_resolution,[],[f41])).
% 1.62/0.58  fof(f41,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK8(X0,X1) != k1_funct_1(X1,sK8(X0,X1)) | k6_relat_1(X0) = X1) )),
% 1.62/0.58    inference(cnf_transformation,[],[f15])).
% 1.62/0.58  fof(f15,plain,(
% 1.62/0.58    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.62/0.58    inference(flattening,[],[f14])).
% 1.62/0.58  fof(f14,plain,(
% 1.62/0.58    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.62/0.58    inference(ennf_transformation,[],[f5])).
% 1.62/0.58  fof(f5,axiom,(
% 1.62/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 1.62/0.58  fof(f163,plain,(
% 1.62/0.58    spl10_9 | ~spl10_1 | ~spl10_2 | spl10_19 | ~spl10_7),
% 1.62/0.58    inference(avatar_split_clause,[],[f112,f87,f160,f62,f57,f97])).
% 1.62/0.58  fof(f112,plain,(
% 1.62/0.58    r2_hidden(sK8(sK0,sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k6_relat_1(sK0) | ~spl10_7),
% 1.62/0.58    inference(superposition,[],[f55,f89])).
% 1.62/0.58  fof(f55,plain,(
% 1.62/0.58    ( ! [X1] : (r2_hidden(sK8(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 1.62/0.58    inference(equality_resolution,[],[f40])).
% 1.62/0.58  fof(f40,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK8(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 1.62/0.58    inference(cnf_transformation,[],[f15])).
% 1.62/0.58  fof(f105,plain,(
% 1.62/0.58    spl10_10),
% 1.62/0.58    inference(avatar_split_clause,[],[f25,f102])).
% 1.62/0.58  fof(f25,plain,(
% 1.62/0.58    sK1 = k5_relat_1(sK2,sK1)),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  fof(f9,plain,(
% 1.62/0.58    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.62/0.58    inference(flattening,[],[f8])).
% 1.62/0.58  fof(f8,plain,(
% 1.62/0.58    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.62/0.58    inference(ennf_transformation,[],[f7])).
% 1.62/0.58  fof(f7,negated_conjecture,(
% 1.62/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 1.62/0.58    inference(negated_conjecture,[],[f6])).
% 1.62/0.58  fof(f6,conjecture,(
% 1.62/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).
% 1.62/0.58  fof(f100,plain,(
% 1.62/0.58    ~spl10_9),
% 1.62/0.58    inference(avatar_split_clause,[],[f26,f97])).
% 1.62/0.58  fof(f26,plain,(
% 1.62/0.58    sK2 != k6_relat_1(sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  fof(f95,plain,(
% 1.62/0.58    spl10_8),
% 1.62/0.58    inference(avatar_split_clause,[],[f23,f92])).
% 1.62/0.58  fof(f23,plain,(
% 1.62/0.58    r1_tarski(k2_relat_1(sK2),sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  fof(f90,plain,(
% 1.62/0.58    spl10_7),
% 1.62/0.58    inference(avatar_split_clause,[],[f22,f87])).
% 1.62/0.58  fof(f22,plain,(
% 1.62/0.58    sK0 = k1_relat_1(sK2)),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  fof(f85,plain,(
% 1.62/0.58    spl10_6),
% 1.62/0.58    inference(avatar_split_clause,[],[f21,f82])).
% 1.62/0.58  fof(f21,plain,(
% 1.62/0.58    sK0 = k1_relat_1(sK1)),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  fof(f80,plain,(
% 1.62/0.58    spl10_5),
% 1.62/0.58    inference(avatar_split_clause,[],[f28,f77])).
% 1.62/0.58  fof(f28,plain,(
% 1.62/0.58    v1_funct_1(sK1)),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  fof(f75,plain,(
% 1.62/0.58    spl10_4),
% 1.62/0.58    inference(avatar_split_clause,[],[f27,f72])).
% 1.62/0.58  fof(f27,plain,(
% 1.62/0.58    v1_relat_1(sK1)),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  fof(f70,plain,(
% 1.62/0.58    spl10_3),
% 1.62/0.58    inference(avatar_split_clause,[],[f24,f67])).
% 1.62/0.58  fof(f24,plain,(
% 1.62/0.58    v2_funct_1(sK1)),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  fof(f65,plain,(
% 1.62/0.58    spl10_2),
% 1.62/0.58    inference(avatar_split_clause,[],[f20,f62])).
% 1.62/0.58  fof(f20,plain,(
% 1.62/0.58    v1_funct_1(sK2)),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  fof(f60,plain,(
% 1.62/0.58    spl10_1),
% 1.62/0.58    inference(avatar_split_clause,[],[f19,f57])).
% 1.62/0.58  fof(f19,plain,(
% 1.62/0.58    v1_relat_1(sK2)),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  % SZS output end Proof for theBenchmark
% 1.62/0.58  % (14026)------------------------------
% 1.62/0.58  % (14026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (14026)Termination reason: Refutation
% 1.62/0.58  
% 1.62/0.58  % (14026)Memory used [KB]: 11001
% 1.62/0.58  % (14026)Time elapsed: 0.147 s
% 1.62/0.58  % (14026)------------------------------
% 1.62/0.58  % (14026)------------------------------
% 1.62/0.58  % (14003)Success in time 0.217 s
%------------------------------------------------------------------------------

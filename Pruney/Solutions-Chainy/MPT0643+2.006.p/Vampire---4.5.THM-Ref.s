%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:40 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 187 expanded)
%              Number of leaves         :   15 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  328 (1115 expanded)
%              Number of equality atoms :   81 ( 388 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f507,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f106,f130,f177,f195,f271,f440,f449,f480,f506])).

fof(f506,plain,(
    ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | ~ spl10_16 ),
    inference(unit_resulting_resolution,[],[f26,f176])).

fof(f176,plain,
    ( sK2 = k6_relat_1(sK0)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl10_16
  <=> sK2 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f26,plain,(
    sK2 != k6_relat_1(sK0) ),
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

% (26889)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

fof(f480,plain,
    ( ~ spl10_13
    | spl10_18
    | ~ spl10_25
    | ~ spl10_31 ),
    inference(avatar_contradiction_clause,[],[f474])).

% (26906)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f474,plain,
    ( $false
    | ~ spl10_13
    | spl10_18
    | ~ spl10_25
    | ~ spl10_31 ),
    inference(unit_resulting_resolution,[],[f163,f472])).

fof(f472,plain,
    ( ~ r2_hidden(sK3(sK0,sK2),sK0)
    | ~ spl10_13
    | spl10_18
    | ~ spl10_25
    | ~ spl10_31 ),
    inference(forward_demodulation,[],[f469,f22])).

fof(f22,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f469,plain,
    ( ~ r2_hidden(sK3(sK0,sK2),k1_relat_1(sK2))
    | ~ spl10_13
    | spl10_18
    | ~ spl10_25
    | ~ spl10_31 ),
    inference(unit_resulting_resolution,[],[f19,f20,f467,f53])).

fof(f53,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f467,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k2_relat_1(sK2))
    | ~ spl10_13
    | spl10_18
    | ~ spl10_25
    | ~ spl10_31 ),
    inference(unit_resulting_resolution,[],[f23,f453,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f453,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0)
    | ~ spl10_13
    | spl10_18
    | ~ spl10_25
    | ~ spl10_31 ),
    inference(unit_resulting_resolution,[],[f163,f194,f352,f439])).

fof(f439,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,sK0)
        | X2 = X3
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) )
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl10_31
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X3,sK0)
        | X2 = X3
        | ~ r2_hidden(X2,sK0)
        | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f352,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2)))
    | ~ spl10_13
    | ~ spl10_25 ),
    inference(forward_demodulation,[],[f346,f25])).

fof(f25,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f346,plain,
    ( k1_funct_1(k5_relat_1(sK2,sK1),sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2)))
    | ~ spl10_13
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f28,f27,f163,f270])).

fof(f270,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_1(X4)
        | k1_funct_1(k5_relat_1(sK2,X4),X5) = k1_funct_1(X4,k1_funct_1(sK2,X5))
        | ~ v1_relat_1(X4)
        | ~ r2_hidden(X5,sK0) )
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl10_25
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X5,sK0)
        | k1_funct_1(k5_relat_1(sK2,X4),X5) = k1_funct_1(X4,k1_funct_1(sK2,X5))
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f194,plain,
    ( sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))
    | spl10_18 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl10_18
  <=> sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

% (26894)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f23,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f163,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl10_13
  <=> r2_hidden(sK3(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f449,plain,(
    spl10_30 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | spl10_30 ),
    inference(unit_resulting_resolution,[],[f24,f436])).

fof(f436,plain,
    ( ~ v2_funct_1(sK1)
    | spl10_30 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl10_30
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f24,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f440,plain,
    ( ~ spl10_30
    | ~ spl10_8
    | spl10_31 ),
    inference(avatar_split_clause,[],[f68,f438,f123,f434])).

fof(f123,plain,
    ( spl10_8
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f68,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | X2 = X3
      | ~ v2_funct_1(sK1) ) ),
    inference(forward_demodulation,[],[f67,f21])).

fof(f21,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | X2 = X3
      | ~ v2_funct_1(sK1) ) ),
    inference(forward_demodulation,[],[f65,f21])).

fof(f65,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | X2 = X3
      | ~ v2_funct_1(sK1) ) ),
    inference(resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f271,plain,
    ( ~ spl10_2
    | spl10_25 ),
    inference(avatar_split_clause,[],[f62,f269,f87])).

fof(f87,plain,
    ( spl10_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f62,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | k1_funct_1(k5_relat_1(sK2,X4),X5) = k1_funct_1(X4,k1_funct_1(sK2,X5)) ) ),
    inference(forward_demodulation,[],[f59,f22])).

fof(f59,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ r2_hidden(X5,k1_relat_1(sK2))
      | k1_funct_1(k5_relat_1(sK2,X4),X5) = k1_funct_1(X4,k1_funct_1(sK2,X5)) ) ),
    inference(resolution,[],[f20,f33])).

% (26898)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
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
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f195,plain,
    ( spl10_16
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f81,f192,f91,f87,f174])).

fof(f91,plain,
    ( spl10_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f81,plain,
    ( sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k6_relat_1(sK0) ),
    inference(superposition,[],[f50,f22])).

fof(f50,plain,(
    ! [X1] :
      ( sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

% (26905)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f177,plain,
    ( spl10_16
    | ~ spl10_2
    | ~ spl10_3
    | spl10_13 ),
    inference(avatar_split_clause,[],[f80,f161,f91,f87,f174])).

fof(f80,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k6_relat_1(sK0) ),
    inference(superposition,[],[f51,f22])).

fof(f51,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK3(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f130,plain,(
    spl10_8 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl10_8 ),
    inference(unit_resulting_resolution,[],[f27,f125])).

fof(f125,plain,
    ( ~ v1_relat_1(sK1)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f106,plain,(
    spl10_3 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl10_3 ),
    inference(unit_resulting_resolution,[],[f20,f93])).

fof(f93,plain,
    ( ~ v1_funct_1(sK2)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f102,plain,(
    spl10_2 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f19,f89])).

fof(f89,plain,
    ( ~ v1_relat_1(sK2)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (26887)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (26903)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.54  % (26895)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.55  % (26885)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.55  % (26884)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.56  % (26883)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.56/0.56  % (26900)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.56/0.56  % (26893)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.56/0.57  % (26907)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.56/0.57  % (26890)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.56/0.57  % (26892)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.57  % (26899)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.56/0.57  % (26891)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.56/0.58  % (26901)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.56/0.58  % (26909)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.56/0.59  % (26881)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.56/0.60  % (26882)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.56/0.60  % (26897)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.56/0.60  % (26884)Refutation found. Thanks to Tanya!
% 1.56/0.60  % SZS status Theorem for theBenchmark
% 1.56/0.61  % (26902)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.56/0.61  % (26910)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.56/0.61  % SZS output start Proof for theBenchmark
% 1.56/0.61  fof(f507,plain,(
% 1.56/0.61    $false),
% 1.56/0.61    inference(avatar_sat_refutation,[],[f102,f106,f130,f177,f195,f271,f440,f449,f480,f506])).
% 1.56/0.61  fof(f506,plain,(
% 1.56/0.61    ~spl10_16),
% 1.56/0.61    inference(avatar_contradiction_clause,[],[f499])).
% 1.56/0.61  fof(f499,plain,(
% 1.56/0.61    $false | ~spl10_16),
% 1.56/0.61    inference(unit_resulting_resolution,[],[f26,f176])).
% 1.56/0.61  fof(f176,plain,(
% 1.56/0.61    sK2 = k6_relat_1(sK0) | ~spl10_16),
% 1.56/0.61    inference(avatar_component_clause,[],[f174])).
% 1.56/0.61  fof(f174,plain,(
% 1.56/0.61    spl10_16 <=> sK2 = k6_relat_1(sK0)),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.56/0.61  fof(f26,plain,(
% 1.56/0.61    sK2 != k6_relat_1(sK0)),
% 1.56/0.61    inference(cnf_transformation,[],[f9])).
% 1.56/0.61  fof(f9,plain,(
% 1.56/0.61    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.56/0.61    inference(flattening,[],[f8])).
% 1.56/0.61  fof(f8,plain,(
% 1.56/0.61    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.56/0.61    inference(ennf_transformation,[],[f7])).
% 1.56/0.61  % (26889)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.56/0.61  fof(f7,negated_conjecture,(
% 1.56/0.61    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 1.56/0.61    inference(negated_conjecture,[],[f6])).
% 1.56/0.61  fof(f6,conjecture,(
% 1.56/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).
% 1.56/0.61  fof(f480,plain,(
% 1.56/0.61    ~spl10_13 | spl10_18 | ~spl10_25 | ~spl10_31),
% 1.56/0.61    inference(avatar_contradiction_clause,[],[f474])).
% 1.56/0.61  % (26906)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.56/0.61  fof(f474,plain,(
% 1.56/0.61    $false | (~spl10_13 | spl10_18 | ~spl10_25 | ~spl10_31)),
% 1.56/0.61    inference(unit_resulting_resolution,[],[f163,f472])).
% 1.56/0.61  fof(f472,plain,(
% 1.56/0.61    ~r2_hidden(sK3(sK0,sK2),sK0) | (~spl10_13 | spl10_18 | ~spl10_25 | ~spl10_31)),
% 1.56/0.61    inference(forward_demodulation,[],[f469,f22])).
% 1.56/0.61  fof(f22,plain,(
% 1.56/0.61    sK0 = k1_relat_1(sK2)),
% 1.56/0.61    inference(cnf_transformation,[],[f9])).
% 1.56/0.61  fof(f469,plain,(
% 1.56/0.61    ~r2_hidden(sK3(sK0,sK2),k1_relat_1(sK2)) | (~spl10_13 | spl10_18 | ~spl10_25 | ~spl10_31)),
% 1.56/0.61    inference(unit_resulting_resolution,[],[f19,f20,f467,f53])).
% 1.56/0.61  fof(f53,plain,(
% 1.56/0.61    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.56/0.61    inference(equality_resolution,[],[f52])).
% 1.56/0.61  fof(f52,plain,(
% 1.56/0.61    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 1.56/0.61    inference(equality_resolution,[],[f47])).
% 1.56/0.61  fof(f47,plain,(
% 1.56/0.61    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.56/0.61    inference(cnf_transformation,[],[f18])).
% 1.56/0.61  fof(f18,plain,(
% 1.56/0.61    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.56/0.61    inference(flattening,[],[f17])).
% 1.56/0.61  fof(f17,plain,(
% 1.56/0.61    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.56/0.61    inference(ennf_transformation,[],[f2])).
% 1.56/0.61  fof(f2,axiom,(
% 1.56/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.56/0.61  fof(f467,plain,(
% 1.56/0.61    ~r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k2_relat_1(sK2)) | (~spl10_13 | spl10_18 | ~spl10_25 | ~spl10_31)),
% 1.56/0.61    inference(unit_resulting_resolution,[],[f23,f453,f39])).
% 1.56/0.61  fof(f39,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f16])).
% 1.56/0.61  fof(f16,plain,(
% 1.56/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.56/0.61    inference(ennf_transformation,[],[f1])).
% 1.56/0.61  fof(f1,axiom,(
% 1.56/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.61  fof(f453,plain,(
% 1.56/0.61    ~r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0) | (~spl10_13 | spl10_18 | ~spl10_25 | ~spl10_31)),
% 1.56/0.61    inference(unit_resulting_resolution,[],[f163,f194,f352,f439])).
% 1.56/0.61  fof(f439,plain,(
% 1.56/0.61    ( ! [X2,X3] : (~r2_hidden(X3,sK0) | X2 = X3 | ~r2_hidden(X2,sK0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)) ) | ~spl10_31),
% 1.56/0.61    inference(avatar_component_clause,[],[f438])).
% 1.56/0.61  fof(f438,plain,(
% 1.56/0.61    spl10_31 <=> ! [X3,X2] : (~r2_hidden(X3,sK0) | X2 = X3 | ~r2_hidden(X2,sK0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 1.56/0.61  fof(f352,plain,(
% 1.56/0.61    k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) | (~spl10_13 | ~spl10_25)),
% 1.56/0.61    inference(forward_demodulation,[],[f346,f25])).
% 1.56/0.61  fof(f25,plain,(
% 1.56/0.61    sK1 = k5_relat_1(sK2,sK1)),
% 1.56/0.61    inference(cnf_transformation,[],[f9])).
% 1.56/0.61  fof(f346,plain,(
% 1.56/0.61    k1_funct_1(k5_relat_1(sK2,sK1),sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) | (~spl10_13 | ~spl10_25)),
% 1.56/0.61    inference(unit_resulting_resolution,[],[f28,f27,f163,f270])).
% 1.56/0.61  fof(f270,plain,(
% 1.56/0.61    ( ! [X4,X5] : (~v1_funct_1(X4) | k1_funct_1(k5_relat_1(sK2,X4),X5) = k1_funct_1(X4,k1_funct_1(sK2,X5)) | ~v1_relat_1(X4) | ~r2_hidden(X5,sK0)) ) | ~spl10_25),
% 1.56/0.61    inference(avatar_component_clause,[],[f269])).
% 1.56/0.61  fof(f269,plain,(
% 1.56/0.61    spl10_25 <=> ! [X5,X4] : (~r2_hidden(X5,sK0) | k1_funct_1(k5_relat_1(sK2,X4),X5) = k1_funct_1(X4,k1_funct_1(sK2,X5)) | ~v1_relat_1(X4) | ~v1_funct_1(X4))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 1.56/0.61  fof(f27,plain,(
% 1.56/0.61    v1_relat_1(sK1)),
% 1.56/0.61    inference(cnf_transformation,[],[f9])).
% 1.56/0.61  fof(f28,plain,(
% 1.56/0.61    v1_funct_1(sK1)),
% 1.56/0.61    inference(cnf_transformation,[],[f9])).
% 1.56/0.61  fof(f194,plain,(
% 1.56/0.61    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | spl10_18),
% 1.56/0.61    inference(avatar_component_clause,[],[f192])).
% 1.56/0.61  fof(f192,plain,(
% 1.56/0.61    spl10_18 <=> sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2))),
% 1.56/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 1.56/0.62  % (26894)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.56/0.62  fof(f23,plain,(
% 1.56/0.62    r1_tarski(k2_relat_1(sK2),sK0)),
% 1.56/0.62    inference(cnf_transformation,[],[f9])).
% 1.56/0.62  fof(f20,plain,(
% 1.56/0.62    v1_funct_1(sK2)),
% 1.56/0.62    inference(cnf_transformation,[],[f9])).
% 1.56/0.62  fof(f19,plain,(
% 1.56/0.62    v1_relat_1(sK2)),
% 1.56/0.62    inference(cnf_transformation,[],[f9])).
% 1.56/0.62  fof(f163,plain,(
% 1.56/0.62    r2_hidden(sK3(sK0,sK2),sK0) | ~spl10_13),
% 1.56/0.62    inference(avatar_component_clause,[],[f161])).
% 1.56/0.62  fof(f161,plain,(
% 1.56/0.62    spl10_13 <=> r2_hidden(sK3(sK0,sK2),sK0)),
% 1.56/0.62    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 1.56/0.62  fof(f449,plain,(
% 1.56/0.62    spl10_30),
% 1.56/0.62    inference(avatar_contradiction_clause,[],[f441])).
% 1.56/0.62  fof(f441,plain,(
% 1.56/0.62    $false | spl10_30),
% 1.56/0.62    inference(unit_resulting_resolution,[],[f24,f436])).
% 1.56/0.62  fof(f436,plain,(
% 1.56/0.62    ~v2_funct_1(sK1) | spl10_30),
% 1.56/0.62    inference(avatar_component_clause,[],[f434])).
% 1.56/0.62  fof(f434,plain,(
% 1.56/0.62    spl10_30 <=> v2_funct_1(sK1)),
% 1.56/0.62    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 1.56/0.62  fof(f24,plain,(
% 1.56/0.62    v2_funct_1(sK1)),
% 1.56/0.62    inference(cnf_transformation,[],[f9])).
% 1.56/0.62  fof(f440,plain,(
% 1.56/0.62    ~spl10_30 | ~spl10_8 | spl10_31),
% 1.56/0.62    inference(avatar_split_clause,[],[f68,f438,f123,f434])).
% 1.56/0.62  fof(f123,plain,(
% 1.56/0.62    spl10_8 <=> v1_relat_1(sK1)),
% 1.56/0.62    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.56/0.62  fof(f68,plain,(
% 1.56/0.62    ( ! [X2,X3] : (~r2_hidden(X3,sK0) | ~r2_hidden(X2,sK0) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | ~v2_funct_1(sK1)) )),
% 1.56/0.62    inference(forward_demodulation,[],[f67,f21])).
% 1.56/0.62  fof(f21,plain,(
% 1.56/0.62    sK0 = k1_relat_1(sK1)),
% 1.56/0.62    inference(cnf_transformation,[],[f9])).
% 1.56/0.62  fof(f67,plain,(
% 1.56/0.62    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | ~v2_funct_1(sK1)) )),
% 1.56/0.62    inference(forward_demodulation,[],[f65,f21])).
% 1.56/0.62  fof(f65,plain,(
% 1.56/0.62    ( ! [X2,X3] : (~v1_relat_1(sK1) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | ~v2_funct_1(sK1)) )),
% 1.56/0.62    inference(resolution,[],[f28,f34])).
% 1.56/0.62  fof(f34,plain,(
% 1.56/0.62    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 1.56/0.62    inference(cnf_transformation,[],[f15])).
% 1.56/0.62  fof(f15,plain,(
% 1.56/0.62    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.56/0.62    inference(flattening,[],[f14])).
% 1.56/0.62  fof(f14,plain,(
% 1.56/0.62    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.56/0.62    inference(ennf_transformation,[],[f3])).
% 1.56/0.62  fof(f3,axiom,(
% 1.56/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.56/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 1.56/0.62  fof(f271,plain,(
% 1.56/0.62    ~spl10_2 | spl10_25),
% 1.56/0.62    inference(avatar_split_clause,[],[f62,f269,f87])).
% 1.56/0.62  fof(f87,plain,(
% 1.56/0.62    spl10_2 <=> v1_relat_1(sK2)),
% 1.56/0.62    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.56/0.62  fof(f62,plain,(
% 1.56/0.62    ( ! [X4,X5] : (~r2_hidden(X5,sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | k1_funct_1(k5_relat_1(sK2,X4),X5) = k1_funct_1(X4,k1_funct_1(sK2,X5))) )),
% 1.56/0.62    inference(forward_demodulation,[],[f59,f22])).
% 1.56/0.62  fof(f59,plain,(
% 1.56/0.62    ( ! [X4,X5] : (~v1_relat_1(sK2) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | ~r2_hidden(X5,k1_relat_1(sK2)) | k1_funct_1(k5_relat_1(sK2,X4),X5) = k1_funct_1(X4,k1_funct_1(sK2,X5))) )),
% 1.56/0.62    inference(resolution,[],[f20,f33])).
% 1.56/0.62  % (26898)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.56/0.62  fof(f33,plain,(
% 1.56/0.62    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 1.56/0.62    inference(cnf_transformation,[],[f13])).
% 1.56/0.62  fof(f13,plain,(
% 1.56/0.62    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.56/0.62    inference(flattening,[],[f12])).
% 1.56/0.62  fof(f12,plain,(
% 1.56/0.62    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.56/0.62    inference(ennf_transformation,[],[f4])).
% 1.56/0.62  fof(f4,axiom,(
% 1.56/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 1.56/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 1.56/0.62  fof(f195,plain,(
% 1.56/0.62    spl10_16 | ~spl10_2 | ~spl10_3 | ~spl10_18),
% 1.56/0.62    inference(avatar_split_clause,[],[f81,f192,f91,f87,f174])).
% 1.56/0.62  fof(f91,plain,(
% 1.56/0.62    spl10_3 <=> v1_funct_1(sK2)),
% 1.56/0.62    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.56/0.62  fof(f81,plain,(
% 1.56/0.62    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k6_relat_1(sK0)),
% 1.56/0.62    inference(superposition,[],[f50,f22])).
% 1.56/0.62  fof(f50,plain,(
% 1.56/0.62    ( ! [X1] : (sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 1.56/0.62    inference(equality_resolution,[],[f30])).
% 1.56/0.62  fof(f30,plain,(
% 1.56/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) | k6_relat_1(X0) = X1) )),
% 1.56/0.62    inference(cnf_transformation,[],[f11])).
% 1.56/0.62  % (26905)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.56/0.62  fof(f11,plain,(
% 1.56/0.62    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.56/0.62    inference(flattening,[],[f10])).
% 1.56/0.62  fof(f10,plain,(
% 1.56/0.62    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.56/0.62    inference(ennf_transformation,[],[f5])).
% 1.56/0.62  fof(f5,axiom,(
% 1.56/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.56/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 1.56/0.62  fof(f177,plain,(
% 1.56/0.62    spl10_16 | ~spl10_2 | ~spl10_3 | spl10_13),
% 1.56/0.62    inference(avatar_split_clause,[],[f80,f161,f91,f87,f174])).
% 1.56/0.62  fof(f80,plain,(
% 1.56/0.62    r2_hidden(sK3(sK0,sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k6_relat_1(sK0)),
% 1.56/0.62    inference(superposition,[],[f51,f22])).
% 1.56/0.62  fof(f51,plain,(
% 1.56/0.62    ( ! [X1] : (r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 1.56/0.62    inference(equality_resolution,[],[f29])).
% 1.56/0.62  fof(f29,plain,(
% 1.56/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK3(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 1.56/0.62    inference(cnf_transformation,[],[f11])).
% 1.56/0.62  fof(f130,plain,(
% 1.56/0.62    spl10_8),
% 1.56/0.62    inference(avatar_contradiction_clause,[],[f127])).
% 1.56/0.62  fof(f127,plain,(
% 1.56/0.62    $false | spl10_8),
% 1.56/0.62    inference(unit_resulting_resolution,[],[f27,f125])).
% 1.56/0.62  fof(f125,plain,(
% 1.56/0.62    ~v1_relat_1(sK1) | spl10_8),
% 1.56/0.62    inference(avatar_component_clause,[],[f123])).
% 1.56/0.62  fof(f106,plain,(
% 1.56/0.62    spl10_3),
% 1.56/0.62    inference(avatar_contradiction_clause,[],[f103])).
% 1.56/0.62  fof(f103,plain,(
% 1.56/0.62    $false | spl10_3),
% 1.56/0.62    inference(unit_resulting_resolution,[],[f20,f93])).
% 1.56/0.62  fof(f93,plain,(
% 1.56/0.62    ~v1_funct_1(sK2) | spl10_3),
% 1.56/0.62    inference(avatar_component_clause,[],[f91])).
% 1.56/0.62  fof(f102,plain,(
% 1.56/0.62    spl10_2),
% 1.56/0.62    inference(avatar_contradiction_clause,[],[f99])).
% 1.56/0.62  fof(f99,plain,(
% 1.56/0.62    $false | spl10_2),
% 1.56/0.62    inference(unit_resulting_resolution,[],[f19,f89])).
% 1.56/0.62  fof(f89,plain,(
% 1.56/0.62    ~v1_relat_1(sK2) | spl10_2),
% 1.56/0.62    inference(avatar_component_clause,[],[f87])).
% 1.56/0.62  % SZS output end Proof for theBenchmark
% 1.56/0.62  % (26884)------------------------------
% 1.56/0.62  % (26884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.62  % (26884)Termination reason: Refutation
% 1.56/0.62  
% 1.56/0.62  % (26884)Memory used [KB]: 6652
% 1.56/0.62  % (26884)Time elapsed: 0.176 s
% 1.56/0.62  % (26884)------------------------------
% 1.56/0.62  % (26884)------------------------------
% 1.56/0.62  % (26879)Success in time 0.261 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 144 expanded)
%              Number of leaves         :   20 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  301 ( 746 expanded)
%              Number of equality atoms :   37 (  95 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7155)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f67,f71,f75,f85,f93,f116,f146])).

fof(f146,plain,
    ( ~ spl4_8
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f143,f114,f69,f73,f57,f83])).

fof(f83,plain,
    ( spl4_8
  <=> r2_hidden(sK2(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f57,plain,
    ( spl4_3
  <=> v5_funct_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f73,plain,
    ( spl4_7
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f69,plain,
    ( spl4_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

% (7143)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f114,plain,
    ( spl4_12
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(X0,sK2(sK1)),k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_funct_1(X0,sK1)
        | ~ r2_hidden(sK2(sK1),k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f143,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v5_funct_1(sK0,sK1)
    | ~ r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(resolution,[],[f140,f70])).

fof(f70,plain,
    ( v1_funct_1(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v5_funct_1(X0,sK1)
        | ~ r2_hidden(sK2(sK1),k1_relat_1(X0)) )
    | ~ spl4_12 ),
    inference(resolution,[],[f115,f76])).

fof(f76,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f42,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f115,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(X0,sK2(sK1)),k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_funct_1(X0,sK1)
        | ~ r2_hidden(sK2(sK1),k1_relat_1(X0)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( ~ spl4_5
    | ~ spl4_4
    | spl4_12
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f106,f91,f114,f61,f65])).

fof(f65,plain,
    ( spl4_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f61,plain,
    ( spl4_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f91,plain,
    ( spl4_9
  <=> k1_xboole_0 = k1_funct_1(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f106,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(X0,sK2(sK1)),k1_xboole_0)
        | ~ r2_hidden(sK2(sK1),k1_relat_1(X0))
        | ~ v5_funct_1(X0,sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_9 ),
    inference(superposition,[],[f39,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK2(sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | ~ v5_funct_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1)))
                & r2_hidden(sK3(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1)))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

% (7150)Refutation not found, incomplete strategy% (7150)------------------------------
% (7150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

fof(f93,plain,
    ( spl4_9
    | ~ spl4_5
    | ~ spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f89,f49,f61,f65,f91])).

fof(f49,plain,
    ( spl4_1
  <=> v2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f89,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK2(sK1))
    | spl4_1 ),
    inference(resolution,[],[f86,f50])).

fof(f50,plain,
    ( ~ v2_relat_1(sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f86,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_funct_1(X0,sK2(X0)) ) ),
    inference(resolution,[],[f38,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f38,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
      | v2_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
            & r2_hidden(sK2(X0),k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(k1_funct_1(X0,X1))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
        & r2_hidden(sK2(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X1))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_relat_1(X0)
      <=> ! [X1] :
            ~ ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).

fof(f85,plain,
    ( ~ spl4_5
    | ~ spl4_4
    | spl4_1
    | spl4_8
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f78,f53,f83,f49,f61,f65])).

fof(f53,plain,
    ( spl4_2
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f78,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | v2_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f37,f54])).

fof(f54,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f28,f73])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ v2_relat_1(sK1)
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v5_funct_1(sK0,sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_relat_1(X1)
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v5_funct_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(sK0)
          & v5_funct_1(sK0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ~ v2_relat_1(X1)
        & k1_relat_1(X1) = k1_relat_1(sK0)
        & v5_funct_1(sK0,X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_relat_1(sK1)
      & k1_relat_1(sK0) = k1_relat_1(sK1)
      & v5_funct_1(sK0,sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X0) = k1_relat_1(X1)
                & v5_funct_1(X0,X1) )
             => v2_relat_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k1_relat_1(X1)
              & v5_funct_1(X0,X1) )
           => v2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).

fof(f71,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f30,f65])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f32,f57])).

fof(f32,plain,(
    v5_funct_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f33,f53])).

fof(f33,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f34,f49])).

fof(f34,plain,(
    ~ v2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (7139)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (7139)Refutation not found, incomplete strategy% (7139)------------------------------
% 0.20/0.47  % (7139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (7154)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (7139)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (7139)Memory used [KB]: 6268
% 0.20/0.48  % (7139)Time elapsed: 0.057 s
% 0.20/0.48  % (7139)------------------------------
% 0.20/0.48  % (7139)------------------------------
% 0.20/0.49  % (7142)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (7145)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (7142)Refutation not found, incomplete strategy% (7142)------------------------------
% 0.20/0.49  % (7142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (7142)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (7142)Memory used [KB]: 10618
% 0.20/0.49  % (7142)Time elapsed: 0.070 s
% 0.20/0.49  % (7142)------------------------------
% 0.20/0.49  % (7142)------------------------------
% 0.20/0.49  % (7140)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (7150)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (7140)Refutation not found, incomplete strategy% (7140)------------------------------
% 0.20/0.49  % (7140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (7140)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (7140)Memory used [KB]: 10618
% 0.20/0.49  % (7140)Time elapsed: 0.068 s
% 0.20/0.49  % (7140)------------------------------
% 0.20/0.49  % (7140)------------------------------
% 0.20/0.49  % (7145)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (7151)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (7151)Refutation not found, incomplete strategy% (7151)------------------------------
% 0.20/0.49  % (7151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (7151)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (7151)Memory used [KB]: 6012
% 0.20/0.49  % (7151)Time elapsed: 0.002 s
% 0.20/0.49  % (7151)------------------------------
% 0.20/0.49  % (7151)------------------------------
% 0.20/0.49  % (7149)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (7144)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (7160)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (7160)Refutation not found, incomplete strategy% (7160)------------------------------
% 0.20/0.50  % (7160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7160)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7160)Memory used [KB]: 10618
% 0.20/0.50  % (7160)Time elapsed: 0.085 s
% 0.20/0.50  % (7160)------------------------------
% 0.20/0.50  % (7160)------------------------------
% 0.20/0.50  % (7146)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (7141)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (7158)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (7152)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (7152)Refutation not found, incomplete strategy% (7152)------------------------------
% 0.20/0.50  % (7152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7147)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  % (7155)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f67,f71,f75,f85,f93,f116,f146])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    ~spl4_8 | ~spl4_3 | ~spl4_7 | ~spl4_6 | ~spl4_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f143,f114,f69,f73,f57,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    spl4_8 <=> r2_hidden(sK2(sK1),k1_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    spl4_3 <=> v5_funct_1(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    spl4_7 <=> v1_relat_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl4_6 <=> v1_funct_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  % (7143)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    spl4_12 <=> ! [X0] : (r2_hidden(k1_funct_1(X0,sK2(sK1)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v5_funct_1(X0,sK1) | ~r2_hidden(sK2(sK1),k1_relat_1(X0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.51  fof(f143,plain,(
% 0.20/0.51    ~v1_relat_1(sK0) | ~v5_funct_1(sK0,sK1) | ~r2_hidden(sK2(sK1),k1_relat_1(sK0)) | (~spl4_6 | ~spl4_12)),
% 0.20/0.51    inference(resolution,[],[f140,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    v1_funct_1(sK0) | ~spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f69])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v5_funct_1(X0,sK1) | ~r2_hidden(sK2(sK1),k1_relat_1(X0))) ) | ~spl4_12),
% 0.20/0.51    inference(resolution,[],[f115,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(superposition,[],[f42,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(X0,sK2(sK1)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v5_funct_1(X0,sK1) | ~r2_hidden(sK2(sK1),k1_relat_1(X0))) ) | ~spl4_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f114])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ~spl4_5 | ~spl4_4 | spl4_12 | ~spl4_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f106,f91,f114,f61,f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    spl4_5 <=> v1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    spl4_4 <=> v1_funct_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl4_9 <=> k1_xboole_0 = k1_funct_1(sK1,sK2(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(X0,sK2(sK1)),k1_xboole_0) | ~r2_hidden(sK2(sK1),k1_relat_1(X0)) | ~v5_funct_1(X0,sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl4_9),
% 0.20/0.51    inference(superposition,[],[f39,f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    k1_xboole_0 = k1_funct_1(sK1,sK2(sK1)) | ~spl4_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f91])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1))) & r2_hidden(sK3(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1))) & r2_hidden(sK3(X0,X1),k1_relat_1(X1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(rectify,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  % (7150)Refutation not found, incomplete strategy% (7150)------------------------------
% 0.20/0.51  % (7150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    spl4_9 | ~spl4_5 | ~spl4_4 | spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f89,f49,f61,f65,f91])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    spl4_1 <=> v2_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_xboole_0 = k1_funct_1(sK1,sK2(sK1)) | spl4_1),
% 0.20/0.51    inference(resolution,[],[f86,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ~v2_relat_1(sK1) | spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f49])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ( ! [X0] : (v2_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_funct_1(X0,sK2(X0))) )),
% 0.20/0.51    inference(resolution,[],[f38,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0] : (v1_xboole_0(k1_funct_1(X0,sK2(X0))) | v2_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (((v2_relat_1(X0) | (v1_xboole_0(k1_funct_1(X0,sK2(X0))) & r2_hidden(sK2(X0),k1_relat_1(X0)))) & (! [X2] : (~v1_xboole_0(k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X0))) | ~v2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0))) => (v1_xboole_0(k1_funct_1(X0,sK2(X0))) & r2_hidden(sK2(X0),k1_relat_1(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (((v2_relat_1(X0) | ? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X2] : (~v1_xboole_0(k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X0))) | ~v2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(rectify,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (((v2_relat_1(X0) | ? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_relat_1(X0) <=> ! [X1] : ~(v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ~spl4_5 | ~spl4_4 | spl4_1 | spl4_8 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f78,f53,f83,f49,f61,f65])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    spl4_2 <=> k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | v2_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_2),
% 0.20/0.51    inference(superposition,[],[f37,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k1_relat_1(sK1) | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f53])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK2(X0),k1_relat_1(X0)) | v2_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    spl4_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f28,f73])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    (~v2_relat_1(sK1) & k1_relat_1(sK0) = k1_relat_1(sK1) & v5_funct_1(sK0,sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16,f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(sK0) & v5_funct_1(sK0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X1] : (~v2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(sK0) & v5_funct_1(sK0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~v2_relat_1(sK1) & k1_relat_1(sK0) = k1_relat_1(sK1) & v5_funct_1(sK0,sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((~v2_relat_1(X1) & (k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 0.20/0.51    inference(negated_conjecture,[],[f6])).
% 0.20/0.51  fof(f6,conjecture,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f29,f69])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    v1_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f30,f65])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    v1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f31,f61])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    v1_funct_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f32,f57])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    v5_funct_1(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f33,f53])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f34,f49])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ~v2_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (7145)------------------------------
% 0.20/0.51  % (7145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7145)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (7145)Memory used [KB]: 10618
% 0.20/0.51  % (7145)Time elapsed: 0.072 s
% 0.20/0.51  % (7145)------------------------------
% 0.20/0.51  % (7145)------------------------------
% 0.20/0.51  % (7148)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (7150)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7150)Memory used [KB]: 10618
% 0.20/0.51  % (7150)Time elapsed: 0.086 s
% 0.20/0.51  % (7155)Refutation not found, incomplete strategy% (7155)------------------------------
% 0.20/0.51  % (7155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7155)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7155)Memory used [KB]: 6140
% 0.20/0.51  % (7155)Time elapsed: 0.053 s
% 0.20/0.51  % (7155)------------------------------
% 0.20/0.51  % (7155)------------------------------
% 0.20/0.51  % (7150)------------------------------
% 0.20/0.51  % (7150)------------------------------
% 0.20/0.51  % (7152)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7152)Memory used [KB]: 1663
% 0.20/0.51  % (7152)Time elapsed: 0.062 s
% 0.20/0.51  % (7152)------------------------------
% 0.20/0.51  % (7152)------------------------------
% 0.20/0.51  % (7136)Success in time 0.15 s
%------------------------------------------------------------------------------

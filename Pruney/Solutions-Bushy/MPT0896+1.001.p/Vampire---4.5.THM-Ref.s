%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0896+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:51 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 152 expanded)
%              Number of leaves         :   17 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  278 ( 728 expanded)
%              Number of equality atoms :  188 ( 600 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f73,f78,f95,f110,f132,f159,f196,f210])).

fof(f210,plain,
    ( spl8_4
    | spl8_8
    | ~ spl8_9
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl8_4
    | spl8_8
    | ~ spl8_9
    | spl8_11 ),
    inference(unit_resulting_resolution,[],[f55,f93,f77,f72,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f72,plain,
    ( sK3 != sK7
    | spl8_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl8_8
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f77,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_9
  <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f93,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl8_11
  <=> k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f55,plain,
    ( k1_xboole_0 != sK3
    | spl8_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f196,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | spl8_7
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl8_1
    | spl8_2
    | spl8_3
    | spl8_7
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f68,f40,f45,f50,f90,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

% (21376)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f90,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl8_10
  <=> k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f50,plain,
    ( k1_xboole_0 != sK2
    | spl8_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f45,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f40,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f68,plain,
    ( sK2 != sK6
    | spl8_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl8_7
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f159,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | spl8_6
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl8_1
    | spl8_2
    | spl8_3
    | spl8_6
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f64,f40,f45,f50,f90,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,
    ( sK1 != sK5
    | spl8_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl8_6
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f132,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | spl8_5
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl8_1
    | spl8_2
    | spl8_3
    | spl8_5
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f60,f40,f45,f50,f90,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,
    ( sK0 != sK4
    | spl8_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl8_5
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f110,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f40,f45,f50,f94,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f94,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f95,plain,
    ( spl8_10
    | spl8_11
    | spl8_4
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f86,f75,f53,f92,f88])).

fof(f86,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl8_9 ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k3_zfmisc_1(sK4,sK5,sK6) = X0 )
    | ~ spl8_9 ),
    inference(superposition,[],[f26,f77])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f33,f75])).

fof(f33,plain,(
    k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7) ),
    inference(definition_unfolding,[],[f17,f32,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f17,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f73,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f22,f70,f66,f62,f58])).

fof(f22,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------

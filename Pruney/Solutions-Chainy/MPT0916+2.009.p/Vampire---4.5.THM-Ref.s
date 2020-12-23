%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 285 expanded)
%              Number of leaves         :   36 ( 130 expanded)
%              Depth                    :    8
%              Number of atoms          :  412 (1114 expanded)
%              Number of equality atoms :   56 ( 106 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f481,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f122,f128,f163,f224,f230,f238,f243,f351,f360,f363,f393,f428,f444,f451,f456,f475,f480])).

fof(f480,plain,
    ( ~ spl9_17
    | ~ spl9_32 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | ~ spl9_17
    | ~ spl9_32 ),
    inference(unit_resulting_resolution,[],[f242,f68,f474,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f56,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f474,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl9_32
  <=> r1_tarski(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f68,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f242,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl9_17
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f475,plain,
    ( spl9_32
    | ~ spl9_7
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f459,f344,f119,f472])).

fof(f119,plain,
    ( spl9_7
  <=> r1_tarski(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f344,plain,
    ( spl9_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f459,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl9_7
    | ~ spl9_25 ),
    inference(superposition,[],[f121,f346])).

fof(f346,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f344])).

fof(f121,plain,
    ( r1_tarski(sK4,sK1)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f456,plain,
    ( ~ spl9_16
    | ~ spl9_31 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | ~ spl9_16
    | ~ spl9_31 ),
    inference(unit_resulting_resolution,[],[f237,f68,f450,f133])).

fof(f450,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f448])).

% (18349)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f448,plain,
    ( spl9_31
  <=> r1_tarski(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f237,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl9_16
  <=> r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f451,plain,
    ( spl9_31
    | ~ spl9_8
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f432,f348,f125,f448])).

fof(f125,plain,
    ( spl9_8
  <=> r1_tarski(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f348,plain,
    ( spl9_26
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f432,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl9_8
    | ~ spl9_26 ),
    inference(superposition,[],[f127,f350])).

fof(f350,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f348])).

fof(f127,plain,
    ( r1_tarski(sK5,sK2)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f444,plain,
    ( spl9_27
    | ~ spl9_29 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | spl9_27
    | ~ spl9_29 ),
    inference(unit_resulting_resolution,[],[f392,f378,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f378,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl9_27 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl9_27
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f392,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl9_29
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f428,plain,
    ( ~ spl9_15
    | ~ spl9_27 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl9_15
    | ~ spl9_27 ),
    inference(unit_resulting_resolution,[],[f229,f395,f379,f133])).

fof(f379,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f377])).

fof(f395,plain,
    ( ! [X0] : r1_xboole_0(sK3,X0)
    | ~ spl9_27 ),
    inference(resolution,[],[f381,f106])).

fof(f106,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f72,f68])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f381,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | r1_xboole_0(sK3,X0) )
    | ~ spl9_27 ),
    inference(resolution,[],[f379,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f229,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl9_15
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f393,plain,
    ( spl9_29
    | ~ spl9_1
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f364,f340,f82,f390])).

% (18343)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f82,plain,
    ( spl9_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f340,plain,
    ( spl9_24
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f364,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_1
    | ~ spl9_24 ),
    inference(superposition,[],[f84,f342])).

fof(f342,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f340])).

fof(f84,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f363,plain,
    ( spl9_24
    | spl9_25
    | spl9_26
    | ~ spl9_5
    | ~ spl9_17
    | spl9_10 ),
    inference(avatar_split_clause,[],[f361,f156,f240,f102,f348,f344,f340])).

fof(f102,plain,
    ( spl9_5
  <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f156,plain,
    ( spl9_10
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f361,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_10 ),
    inference(superposition,[],[f158,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f158,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f360,plain,
    ( spl9_24
    | spl9_25
    | spl9_26
    | ~ spl9_5
    | ~ spl9_16
    | spl9_11 ),
    inference(avatar_split_clause,[],[f353,f160,f235,f102,f348,f344,f340])).

fof(f160,plain,
    ( spl9_11
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f353,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_11 ),
    inference(superposition,[],[f162,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f162,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f160])).

fof(f351,plain,
    ( spl9_24
    | spl9_25
    | spl9_26
    | ~ spl9_5
    | ~ spl9_15
    | spl9_9 ),
    inference(avatar_split_clause,[],[f335,f152,f227,f102,f348,f344,f340])).

fof(f152,plain,
    ( spl9_9
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f335,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_9 ),
    inference(superposition,[],[f154,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f59])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f154,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f243,plain,
    ( spl9_17
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f233,f221,f240])).

fof(f221,plain,
    ( spl9_14
  <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f233,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl9_14 ),
    inference(resolution,[],[f54,f223])).

fof(f223,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f221])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f238,plain,
    ( spl9_16
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f231,f97,f235])).

fof(f97,plain,
    ( spl9_4
  <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f231,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl9_4 ),
    inference(resolution,[],[f54,f99])).

fof(f99,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f230,plain,
    ( spl9_15
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f225,f221,f227])).

fof(f225,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl9_14 ),
    inference(resolution,[],[f223,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f224,plain,
    ( spl9_14
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f218,f97,f221])).

fof(f218,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl9_4 ),
    inference(resolution,[],[f53,f99])).

fof(f163,plain,
    ( ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f49,f160,f156,f152])).

fof(f49,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
      | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
    & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f20,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                    & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                    & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                  & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                  | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
            & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
                | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
              & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
              | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
              | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
            & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
            & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
   => ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
            | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
            | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
          & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
          & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X6] :
        ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
          | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
          | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
        & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
        & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
        | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
        | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
      & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
      & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f128,plain,
    ( spl9_8
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f112,f92,f125])).

fof(f92,plain,
    ( spl9_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f112,plain,
    ( r1_tarski(sK5,sK2)
    | ~ spl9_3 ),
    inference(resolution,[],[f60,f94])).

fof(f94,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f122,plain,
    ( spl9_7
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f111,f87,f119])).

fof(f87,plain,
    ( spl9_2
  <=> m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f111,plain,
    ( r1_tarski(sK4,sK1)
    | ~ spl9_2 ),
    inference(resolution,[],[f60,f89])).

fof(f89,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f105,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f75,f102])).

fof(f75,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f47,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f74,f97])).

fof(f74,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f48,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f46,f92])).

fof(f46,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f45,f87])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f44,f82])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:51:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (18338)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (18351)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (18333)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (18342)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (18356)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (18335)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (18361)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (18344)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (18334)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (18356)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (18332)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (18336)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (18339)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (18347)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (18361)Refutation not found, incomplete strategy% (18361)------------------------------
% 0.22/0.54  % (18361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18358)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (18333)Refutation not found, incomplete strategy% (18333)------------------------------
% 0.22/0.54  % (18333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18333)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18333)Memory used [KB]: 1791
% 0.22/0.54  % (18333)Time elapsed: 0.109 s
% 0.22/0.54  % (18333)------------------------------
% 0.22/0.54  % (18333)------------------------------
% 0.22/0.54  % (18352)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (18346)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (18342)Refutation not found, incomplete strategy% (18342)------------------------------
% 0.22/0.54  % (18342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18342)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18342)Memory used [KB]: 10874
% 0.22/0.54  % (18342)Time elapsed: 0.135 s
% 0.22/0.54  % (18342)------------------------------
% 0.22/0.54  % (18342)------------------------------
% 0.22/0.54  % (18348)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (18348)Refutation not found, incomplete strategy% (18348)------------------------------
% 0.22/0.54  % (18348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18348)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18348)Memory used [KB]: 10746
% 0.22/0.54  % (18348)Time elapsed: 0.127 s
% 0.22/0.54  % (18348)------------------------------
% 0.22/0.54  % (18348)------------------------------
% 0.22/0.54  % (18337)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (18346)Refutation not found, incomplete strategy% (18346)------------------------------
% 0.22/0.55  % (18346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18362)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (18361)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18361)Memory used [KB]: 10874
% 0.22/0.55  % (18361)Time elapsed: 0.087 s
% 0.22/0.55  % (18361)------------------------------
% 0.22/0.55  % (18361)------------------------------
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f481,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f122,f128,f163,f224,f230,f238,f243,f351,f360,f363,f393,f428,f444,f451,f456,f475,f480])).
% 0.22/0.55  fof(f480,plain,(
% 0.22/0.55    ~spl9_17 | ~spl9_32),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f476])).
% 0.22/0.55  fof(f476,plain,(
% 0.22/0.55    $false | (~spl9_17 | ~spl9_32)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f242,f68,f474,f133])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.55    inference(superposition,[],[f56,f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.55  fof(f474,plain,(
% 0.22/0.55    r1_tarski(sK4,k1_xboole_0) | ~spl9_32),
% 0.22/0.55    inference(avatar_component_clause,[],[f472])).
% 0.22/0.55  fof(f472,plain,(
% 0.22/0.55    spl9_32 <=> r1_tarski(sK4,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.55  fof(f242,plain,(
% 0.22/0.55    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl9_17),
% 0.22/0.55    inference(avatar_component_clause,[],[f240])).
% 0.22/0.55  fof(f240,plain,(
% 0.22/0.55    spl9_17 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.22/0.55  fof(f475,plain,(
% 0.22/0.55    spl9_32 | ~spl9_7 | ~spl9_25),
% 0.22/0.55    inference(avatar_split_clause,[],[f459,f344,f119,f472])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    spl9_7 <=> r1_tarski(sK4,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.55  fof(f344,plain,(
% 0.22/0.55    spl9_25 <=> k1_xboole_0 = sK1),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.22/0.55  fof(f459,plain,(
% 0.22/0.55    r1_tarski(sK4,k1_xboole_0) | (~spl9_7 | ~spl9_25)),
% 0.22/0.55    inference(superposition,[],[f121,f346])).
% 0.22/0.55  fof(f346,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | ~spl9_25),
% 0.22/0.55    inference(avatar_component_clause,[],[f344])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    r1_tarski(sK4,sK1) | ~spl9_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f119])).
% 0.22/0.55  fof(f456,plain,(
% 0.22/0.55    ~spl9_16 | ~spl9_31),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f452])).
% 0.22/0.55  fof(f452,plain,(
% 0.22/0.55    $false | (~spl9_16 | ~spl9_31)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f237,f68,f450,f133])).
% 0.22/0.55  fof(f450,plain,(
% 0.22/0.55    r1_tarski(sK5,k1_xboole_0) | ~spl9_31),
% 0.22/0.55    inference(avatar_component_clause,[],[f448])).
% 0.22/0.55  % (18349)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  fof(f448,plain,(
% 0.22/0.55    spl9_31 <=> r1_tarski(sK5,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 0.22/0.55  fof(f237,plain,(
% 0.22/0.55    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl9_16),
% 0.22/0.55    inference(avatar_component_clause,[],[f235])).
% 0.22/0.55  fof(f235,plain,(
% 0.22/0.55    spl9_16 <=> r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.22/0.55  fof(f451,plain,(
% 0.22/0.55    spl9_31 | ~spl9_8 | ~spl9_26),
% 0.22/0.55    inference(avatar_split_clause,[],[f432,f348,f125,f448])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    spl9_8 <=> r1_tarski(sK5,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.55  fof(f348,plain,(
% 0.22/0.55    spl9_26 <=> k1_xboole_0 = sK2),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.22/0.55  fof(f432,plain,(
% 0.22/0.55    r1_tarski(sK5,k1_xboole_0) | (~spl9_8 | ~spl9_26)),
% 0.22/0.55    inference(superposition,[],[f127,f350])).
% 0.22/0.55  fof(f350,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | ~spl9_26),
% 0.22/0.55    inference(avatar_component_clause,[],[f348])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    r1_tarski(sK5,sK2) | ~spl9_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f125])).
% 0.22/0.55  fof(f444,plain,(
% 0.22/0.55    spl9_27 | ~spl9_29),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f443])).
% 0.22/0.55  fof(f443,plain,(
% 0.22/0.55    $false | (spl9_27 | ~spl9_29)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f392,f378,f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.55    inference(nnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.55  fof(f378,plain,(
% 0.22/0.55    ~r1_tarski(sK3,k1_xboole_0) | spl9_27),
% 0.22/0.55    inference(avatar_component_clause,[],[f377])).
% 0.22/0.55  fof(f377,plain,(
% 0.22/0.55    spl9_27 <=> r1_tarski(sK3,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.22/0.55  fof(f392,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl9_29),
% 0.22/0.55    inference(avatar_component_clause,[],[f390])).
% 0.22/0.55  fof(f390,plain,(
% 0.22/0.55    spl9_29 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.22/0.55  fof(f428,plain,(
% 0.22/0.55    ~spl9_15 | ~spl9_27),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f417])).
% 0.22/0.55  fof(f417,plain,(
% 0.22/0.55    $false | (~spl9_15 | ~spl9_27)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f229,f395,f379,f133])).
% 0.22/0.55  fof(f379,plain,(
% 0.22/0.55    r1_tarski(sK3,k1_xboole_0) | ~spl9_27),
% 0.22/0.55    inference(avatar_component_clause,[],[f377])).
% 0.22/0.55  fof(f395,plain,(
% 0.22/0.55    ( ! [X0] : (r1_xboole_0(sK3,X0)) ) | ~spl9_27),
% 0.22/0.55    inference(resolution,[],[f381,f106])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f72,f68])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.55  fof(f381,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | r1_xboole_0(sK3,X0)) ) | ~spl9_27),
% 0.22/0.55    inference(resolution,[],[f379,f69])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.55  fof(f229,plain,(
% 0.22/0.55    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl9_15),
% 0.22/0.55    inference(avatar_component_clause,[],[f227])).
% 0.22/0.55  fof(f227,plain,(
% 0.22/0.55    spl9_15 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.55  fof(f393,plain,(
% 0.22/0.55    spl9_29 | ~spl9_1 | ~spl9_24),
% 0.22/0.55    inference(avatar_split_clause,[],[f364,f340,f82,f390])).
% 0.22/0.55  % (18343)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    spl9_1 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.55  fof(f340,plain,(
% 0.22/0.55    spl9_24 <=> k1_xboole_0 = sK0),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.22/0.55  fof(f364,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl9_1 | ~spl9_24)),
% 0.22/0.55    inference(superposition,[],[f84,f342])).
% 0.22/0.55  fof(f342,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | ~spl9_24),
% 0.22/0.55    inference(avatar_component_clause,[],[f340])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl9_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f82])).
% 0.22/0.55  fof(f363,plain,(
% 0.22/0.55    spl9_24 | spl9_25 | spl9_26 | ~spl9_5 | ~spl9_17 | spl9_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f361,f156,f240,f102,f348,f344,f340])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    spl9_5 <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    spl9_10 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.55  fof(f361,plain,(
% 0.22/0.55    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl9_10),
% 0.22/0.55    inference(superposition,[],[f158,f77])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(definition_unfolding,[],[f51,f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl9_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f156])).
% 0.22/0.55  fof(f360,plain,(
% 0.22/0.55    spl9_24 | spl9_25 | spl9_26 | ~spl9_5 | ~spl9_16 | spl9_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f353,f160,f235,f102,f348,f344,f340])).
% 0.22/0.55  fof(f160,plain,(
% 0.22/0.55    spl9_11 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.55  fof(f353,plain,(
% 0.22/0.55    ~r2_hidden(k2_mcart_1(sK6),sK5) | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl9_11),
% 0.22/0.55    inference(superposition,[],[f162,f76])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(definition_unfolding,[],[f52,f59])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl9_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f160])).
% 0.22/0.55  fof(f351,plain,(
% 0.22/0.55    spl9_24 | spl9_25 | spl9_26 | ~spl9_5 | ~spl9_15 | spl9_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f335,f152,f227,f102,f348,f344,f340])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    spl9_9 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.55  fof(f335,plain,(
% 0.22/0.55    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl9_9),
% 0.22/0.55    inference(superposition,[],[f154,f78])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(definition_unfolding,[],[f50,f59])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl9_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f152])).
% 0.22/0.55  fof(f243,plain,(
% 0.22/0.55    spl9_17 | ~spl9_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f233,f221,f240])).
% 0.22/0.55  fof(f221,plain,(
% 0.22/0.55    spl9_14 <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.22/0.55  fof(f233,plain,(
% 0.22/0.55    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl9_14),
% 0.22/0.55    inference(resolution,[],[f54,f223])).
% 0.22/0.55  fof(f223,plain,(
% 0.22/0.55    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl9_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f221])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.55  fof(f238,plain,(
% 0.22/0.55    spl9_16 | ~spl9_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f231,f97,f235])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    spl9_4 <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.55  fof(f231,plain,(
% 0.22/0.55    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl9_4),
% 0.22/0.55    inference(resolution,[],[f54,f99])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl9_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f97])).
% 0.22/0.55  fof(f230,plain,(
% 0.22/0.55    spl9_15 | ~spl9_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f225,f221,f227])).
% 0.22/0.55  fof(f225,plain,(
% 0.22/0.55    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl9_14),
% 0.22/0.55    inference(resolution,[],[f223,f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f224,plain,(
% 0.22/0.55    spl9_14 | ~spl9_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f218,f97,f221])).
% 0.22/0.55  fof(f218,plain,(
% 0.22/0.55    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl9_4),
% 0.22/0.55    inference(resolution,[],[f53,f99])).
% 0.22/0.55  fof(f163,plain,(
% 0.22/0.55    ~spl9_9 | ~spl9_10 | ~spl9_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f49,f160,f156,f152])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ((((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f20,f34,f33,f32,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) => ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.22/0.55    inference(flattening,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.22/0.55    inference(negated_conjecture,[],[f16])).
% 0.22/0.55  fof(f16,conjecture,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    spl9_8 | ~spl9_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f112,f92,f125])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    spl9_3 <=> m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    r1_tarski(sK5,sK2) | ~spl9_3),
% 0.22/0.55    inference(resolution,[],[f60,f94])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    m1_subset_1(sK5,k1_zfmisc_1(sK2)) | ~spl9_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f92])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    spl9_7 | ~spl9_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f111,f87,f119])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    spl9_2 <=> m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    r1_tarski(sK4,sK1) | ~spl9_2),
% 0.22/0.55    inference(resolution,[],[f60,f89])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    m1_subset_1(sK4,k1_zfmisc_1(sK1)) | ~spl9_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f87])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    spl9_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f75,f102])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.55    inference(definition_unfolding,[],[f47,f59])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    spl9_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f74,f97])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.22/0.55    inference(definition_unfolding,[],[f48,f59])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    spl9_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f46,f92])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    spl9_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f45,f87])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    spl9_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f44,f82])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (18356)------------------------------
% 0.22/0.55  % (18356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18355)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (18356)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (18356)Memory used [KB]: 11001
% 0.22/0.55  % (18356)Time elapsed: 0.069 s
% 0.22/0.55  % (18356)------------------------------
% 0.22/0.55  % (18356)------------------------------
% 0.22/0.55  % (18346)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18346)Memory used [KB]: 1791
% 0.22/0.55  % (18346)Time elapsed: 0.133 s
% 0.22/0.55  % (18346)------------------------------
% 0.22/0.55  % (18346)------------------------------
% 0.22/0.55  % (18330)Success in time 0.18 s
%------------------------------------------------------------------------------

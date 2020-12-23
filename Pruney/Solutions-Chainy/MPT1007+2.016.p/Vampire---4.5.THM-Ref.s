%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 251 expanded)
%              Number of leaves         :   34 ( 100 expanded)
%              Depth                    :    9
%              Number of atoms          :  361 ( 683 expanded)
%              Number of equality atoms :   56 ( 133 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f106,f111,f120,f129,f139,f151,f174,f189,f205,f210,f250,f293,f306,f315,f342,f352])).

fof(f352,plain,(
    ~ spl7_25 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl7_25 ),
    inference(unit_resulting_resolution,[],[f46,f341,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f341,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl7_25
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f342,plain,
    ( spl7_25
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f331,f171,f122,f339])).

fof(f122,plain,
    ( spl7_7
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f171,plain,
    ( spl7_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f331,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f330,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f330,plain,
    ( r2_hidden(sK0,k1_relat_1(k1_xboole_0))
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f124,f173])).

fof(f173,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f124,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f315,plain,(
    ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f46,f292,f60])).

fof(f292,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl7_23
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f306,plain,(
    ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f48,f301])).

fof(f301,plain,
    ( ! [X4] : k1_xboole_0 != k2_xboole_0(k1_xboole_0,X4)
    | ~ spl7_18 ),
    inference(superposition,[],[f73,f245])).

fof(f245,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl7_18
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f73,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f293,plain,
    ( ~ spl7_15
    | ~ spl7_14
    | spl7_8
    | spl7_23
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f276,f247,f290,f126,f202,f207])).

fof(f207,plain,
    ( spl7_15
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f202,plain,
    ( spl7_14
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f126,plain,
    ( spl7_8
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f247,plain,
    ( spl7_19
  <=> r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f276,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)
    | r2_hidden(k1_xboole_0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_19 ),
    inference(forward_demodulation,[],[f274,f44])).

fof(f274,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_19 ),
    inference(superposition,[],[f249,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 != X2
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f249,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f247])).

fof(f250,plain,
    ( spl7_18
    | spl7_19
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f240,f171,f137,f247,f243])).

fof(f137,plain,
    ( spl7_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(sK2,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f240,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(resolution,[],[f235,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

% (5825)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (5816)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f235,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(k1_xboole_0,X0),sK1) )
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f138,f173])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(sK2,X0),sK1) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f137])).

% (5818)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f210,plain,
    ( spl7_15
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f196,f171,f117,f207])).

fof(f117,plain,
    ( spl7_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f196,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f119,f173])).

fof(f119,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f205,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f192,f171,f86,f202])).

fof(f86,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f192,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f88,f173])).

fof(f88,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f189,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f88,f93,f98,f150,f105,f110,f68])).

% (5827)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f110,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f105,plain,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f150,plain,
    ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl7_11
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f98,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl7_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f93,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f174,plain,
    ( spl7_12
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f153,f145,f171])).

fof(f145,plain,
    ( spl7_10
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f153,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_10 ),
    inference(resolution,[],[f146,f56])).

fof(f146,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f151,plain,
    ( spl7_10
    | spl7_11
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f143,f108,f148,f145])).

fof(f143,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_5 ),
    inference(superposition,[],[f132,f130])).

fof(f130,plain,
    ( ! [X0] :
        ( k1_mcart_1(X0) = sK0
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_5 ),
    inference(resolution,[],[f115,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

% (5825)Refutation not found, incomplete strategy% (5825)------------------------------
% (5825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5825)Termination reason: Refutation not found, incomplete strategy

% (5825)Memory used [KB]: 10618
% (5825)Time elapsed: 0.131 s
% (5825)------------------------------
% (5825)------------------------------
fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f115,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl7_5 ),
    inference(resolution,[],[f110,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f132,plain,
    ( ! [X2] :
        ( r2_hidden(k1_mcart_1(X2),k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl7_5 ),
    inference(resolution,[],[f115,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f139,plain,
    ( spl7_2
    | spl7_9
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f112,f108,f103,f86,f137,f91])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | k1_xboole_0 = sK1
        | r2_hidden(k1_funct_1(sK2,X0),sK1) )
    | ~ spl7_5 ),
    inference(resolution,[],[f110,f68])).

fof(f129,plain,
    ( ~ spl7_6
    | spl7_7
    | ~ spl7_1
    | ~ spl7_8
    | spl7_3 ),
    inference(avatar_split_clause,[],[f100,f96,f126,f86,f122,f117])).

fof(f100,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl7_3 ),
    inference(superposition,[],[f98,f78])).

fof(f120,plain,
    ( spl7_6
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f113,f108,f117])).

fof(f113,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f110,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f111,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f71,f108])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f40,f70])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f106,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f72,f103])).

fof(f72,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f39,f70])).

fof(f39,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f99,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f42,f96])).

fof(f42,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f41,f91])).

fof(f41,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f38,f86])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (5820)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (5819)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (5815)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (5837)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (5828)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (5829)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (5843)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (5821)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (5817)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (5824)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (5837)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f354,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f89,f94,f99,f106,f111,f120,f129,f139,f151,f174,f189,f205,f210,f250,f293,f306,f315,f342,f352])).
% 0.22/0.54  fof(f352,plain,(
% 0.22/0.54    ~spl7_25),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f345])).
% 0.22/0.54  fof(f345,plain,(
% 0.22/0.54    $false | ~spl7_25),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f46,f341,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.54  fof(f341,plain,(
% 0.22/0.54    r2_hidden(sK0,k1_xboole_0) | ~spl7_25),
% 0.22/0.54    inference(avatar_component_clause,[],[f339])).
% 0.22/0.54  fof(f339,plain,(
% 0.22/0.54    spl7_25 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f342,plain,(
% 0.22/0.54    spl7_25 | ~spl7_7 | ~spl7_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f331,f171,f122,f339])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    spl7_7 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    spl7_12 <=> k1_xboole_0 = sK2),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.54  fof(f331,plain,(
% 0.22/0.54    r2_hidden(sK0,k1_xboole_0) | (~spl7_7 | ~spl7_12)),
% 0.22/0.54    inference(forward_demodulation,[],[f330,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.54  fof(f330,plain,(
% 0.22/0.54    r2_hidden(sK0,k1_relat_1(k1_xboole_0)) | (~spl7_7 | ~spl7_12)),
% 0.22/0.54    inference(forward_demodulation,[],[f124,f173])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | ~spl7_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f171])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl7_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f122])).
% 0.22/0.54  fof(f315,plain,(
% 0.22/0.54    ~spl7_23),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f309])).
% 0.22/0.54  fof(f309,plain,(
% 0.22/0.54    $false | ~spl7_23),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f46,f292,f60])).
% 0.22/0.54  fof(f292,plain,(
% 0.22/0.54    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) | ~spl7_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f290])).
% 0.22/0.54  fof(f290,plain,(
% 0.22/0.54    spl7_23 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.54  fof(f306,plain,(
% 0.22/0.54    ~spl7_18),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f302])).
% 0.22/0.54  fof(f302,plain,(
% 0.22/0.54    $false | ~spl7_18),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f48,f301])).
% 0.22/0.54  fof(f301,plain,(
% 0.22/0.54    ( ! [X4] : (k1_xboole_0 != k2_xboole_0(k1_xboole_0,X4)) ) | ~spl7_18),
% 0.22/0.54    inference(superposition,[],[f73,f245])).
% 0.22/0.54  fof(f245,plain,(
% 0.22/0.54    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl7_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f243])).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    spl7_18 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f57,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f49,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f58,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    ~spl7_15 | ~spl7_14 | spl7_8 | spl7_23 | ~spl7_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f276,f247,f290,f126,f202,f207])).
% 0.22/0.54  fof(f207,plain,(
% 0.22/0.54    spl7_15 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.54  fof(f202,plain,(
% 0.22/0.54    spl7_14 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    spl7_8 <=> r2_hidden(k1_xboole_0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.54  fof(f247,plain,(
% 0.22/0.54    spl7_19 <=> r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.54  fof(f276,plain,(
% 0.22/0.54    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) | r2_hidden(k1_xboole_0,sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl7_19),
% 0.22/0.54    inference(forward_demodulation,[],[f274,f44])).
% 0.22/0.54  fof(f274,plain,(
% 0.22/0.54    r2_hidden(k1_xboole_0,sK1) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~spl7_19),
% 0.22/0.54    inference(superposition,[],[f249,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 != X2 | k1_funct_1(X0,X1) = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.22/0.54  fof(f249,plain,(
% 0.22/0.54    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | ~spl7_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f247])).
% 0.22/0.54  fof(f250,plain,(
% 0.22/0.54    spl7_18 | spl7_19 | ~spl7_9 | ~spl7_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f240,f171,f137,f247,f243])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    spl7_9 <=> ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl7_9 | ~spl7_12)),
% 0.22/0.54    inference(resolution,[],[f235,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.22/0.54  % (5825)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (5816)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(k1_xboole_0,X0),sK1)) ) | (~spl7_9 | ~spl7_12)),
% 0.22/0.54    inference(forward_demodulation,[],[f138,f173])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1)) ) | ~spl7_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f137])).
% 0.22/0.54  % (5818)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    spl7_15 | ~spl7_6 | ~spl7_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f196,f171,f117,f207])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    spl7_6 <=> v1_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.54  fof(f196,plain,(
% 0.22/0.54    v1_relat_1(k1_xboole_0) | (~spl7_6 | ~spl7_12)),
% 0.22/0.54    inference(backward_demodulation,[],[f119,f173])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    v1_relat_1(sK2) | ~spl7_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f117])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    spl7_14 | ~spl7_1 | ~spl7_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f192,f171,f86,f202])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    spl7_1 <=> v1_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    v1_funct_1(k1_xboole_0) | (~spl7_1 | ~spl7_12)),
% 0.22/0.54    inference(backward_demodulation,[],[f88,f173])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    v1_funct_1(sK2) | ~spl7_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f86])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    ~spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_11),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f184])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    $false | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_11)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f88,f93,f98,f150,f105,f110,f68])).
% 0.22/0.54  % (5827)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.54    inference(flattening,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl7_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f108])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    spl7_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl7_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    spl7_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl7_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f148])).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    spl7_11 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl7_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    spl7_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    k1_xboole_0 != sK1 | spl7_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    spl7_2 <=> k1_xboole_0 = sK1),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    spl7_12 | ~spl7_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f153,f145,f171])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    spl7_10 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | ~spl7_10),
% 0.22/0.54    inference(resolution,[],[f146,f56])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl7_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f145])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    spl7_10 | spl7_11 | ~spl7_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f143,f108,f148,f145])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2)) ) | ~spl7_5),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f142])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK2)) ) | ~spl7_5),
% 0.22/0.54    inference(superposition,[],[f132,f130])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    ( ! [X0] : (k1_mcart_1(X0) = sK0 | ~r2_hidden(X0,sK2)) ) | ~spl7_5),
% 0.22/0.54    inference(resolution,[],[f115,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f65,f70])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  % (5825)Refutation not found, incomplete strategy% (5825)------------------------------
% 0.22/0.54  % (5825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5825)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5825)Memory used [KB]: 10618
% 0.22/0.54  % (5825)Time elapsed: 0.131 s
% 0.22/0.54  % (5825)------------------------------
% 0.22/0.54  % (5825)------------------------------
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    ( ! [X2] : (r2_hidden(X2,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X2,sK2)) ) | ~spl7_5),
% 0.22/0.54    inference(resolution,[],[f110,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    ( ! [X2] : (r2_hidden(k1_mcart_1(X2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,sK2)) ) | ~spl7_5),
% 0.22/0.54    inference(resolution,[],[f115,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    spl7_2 | spl7_9 | ~spl7_1 | ~spl7_4 | ~spl7_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f112,f108,f103,f86,f137,f91])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(sK2) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,X0),sK1)) ) | ~spl7_5),
% 0.22/0.54    inference(resolution,[],[f110,f68])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    ~spl7_6 | spl7_7 | ~spl7_1 | ~spl7_8 | spl7_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f100,f96,f126,f86,f122,f117])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ~r2_hidden(k1_xboole_0,sK1) | ~v1_funct_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl7_3),
% 0.22/0.54    inference(superposition,[],[f98,f78])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    spl7_6 | ~spl7_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f113,f108,f117])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    v1_relat_1(sK2) | ~spl7_5),
% 0.22/0.54    inference(resolution,[],[f110,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    spl7_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f71,f108])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.22/0.54    inference(definition_unfolding,[],[f40,f70])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f20])).
% 0.22/0.54  fof(f20,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    spl7_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f72,f103])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.54    inference(definition_unfolding,[],[f39,f70])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ~spl7_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f42,f96])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ~spl7_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f41,f91])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    k1_xboole_0 != sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    spl7_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f38,f86])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (5837)------------------------------
% 0.22/0.54  % (5837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5837)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (5837)Memory used [KB]: 10874
% 0.22/0.54  % (5837)Time elapsed: 0.079 s
% 0.22/0.54  % (5837)------------------------------
% 0.22/0.54  % (5837)------------------------------
% 0.22/0.54  % (5844)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (5811)Success in time 0.179 s
%------------------------------------------------------------------------------

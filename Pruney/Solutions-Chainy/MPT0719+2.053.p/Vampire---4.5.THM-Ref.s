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
% DateTime   : Thu Dec  3 12:55:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 134 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  285 ( 401 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f68,f72,f76,f80,f84,f92,f100,f111,f116,f122,f132,f136])).

fof(f136,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f134,f52])).

fof(f52,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f134,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f133,f47])).

fof(f47,plain,
    ( v1_funct_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f133,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_1
    | ~ spl3_19 ),
    inference(resolution,[],[f131,f42])).

fof(f42,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_1
  <=> v5_funct_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f131,plain,
    ( ! [X0] :
        ( v5_funct_1(k1_xboole_0,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_19
  <=> ! [X0] :
        ( v5_funct_1(k1_xboole_0,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f132,plain,
    ( spl3_19
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f128,f120,f113,f108,f90,f65,f130])).

fof(f65,plain,
    ( spl3_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f90,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( v5_funct_1(X1,X0)
        | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f108,plain,
    ( spl3_16
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f113,plain,
    ( spl3_17
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f120,plain,
    ( spl3_18
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f128,plain,
    ( ! [X0] :
        ( v5_funct_1(k1_xboole_0,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f127,f110])).

fof(f110,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f108])).

fof(f127,plain,
    ( ! [X0] :
        ( v5_funct_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f126,f115])).

fof(f115,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f126,plain,
    ( ! [X0] :
        ( v5_funct_1(k1_xboole_0,X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f125,f121])).

fof(f121,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f125,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
        | v5_funct_1(k1_xboole_0,X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(superposition,[],[f91,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(X0,X1),k1_relat_1(X1))
        | v5_funct_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f122,plain,
    ( spl3_18
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f118,f98,f74,f70,f120])).

fof(f70,plain,
    ( spl3_7
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( spl3_8
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f98,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f118,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f117,f71])).

fof(f71,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(superposition,[],[f99,f75])).

fof(f75,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f99,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f116,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f106,f78,f55,f113])).

fof(f55,plain,
    ( spl3_4
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f78,plain,
    ( spl3_9
  <=> ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f106,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f79,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f79,plain,
    ( ! [X0] : v1_funct_1(k6_relat_1(X0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f111,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f105,f82,f55,f108])).

fof(f82,plain,
    ( spl3_10
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f105,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(superposition,[],[f83,f57])).

fof(f83,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f100,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f38,f98])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).

% (11387)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f92,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f35,f90])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f84,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f80,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f33,f78])).

fof(f33,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f72,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f68,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f58,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f53,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f48,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f26,f40])).

fof(f26,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:21:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (11386)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (11386)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f137,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f68,f72,f76,f80,f84,f92,f100,f111,f116,f122,f132,f136])).
% 0.22/0.44  fof(f136,plain,(
% 0.22/0.44    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_19),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f135])).
% 0.22/0.44  fof(f135,plain,(
% 0.22/0.44    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_19)),
% 0.22/0.44    inference(subsumption_resolution,[],[f134,f52])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    v1_relat_1(sK0) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f50])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    spl3_3 <=> v1_relat_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f134,plain,(
% 0.22/0.44    ~v1_relat_1(sK0) | (spl3_1 | ~spl3_2 | ~spl3_19)),
% 0.22/0.44    inference(subsumption_resolution,[],[f133,f47])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    v1_funct_1(sK0) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    spl3_2 <=> v1_funct_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f133,plain,(
% 0.22/0.44    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl3_1 | ~spl3_19)),
% 0.22/0.44    inference(resolution,[],[f131,f42])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ~v5_funct_1(k1_xboole_0,sK0) | spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl3_1 <=> v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f131,plain,(
% 0.22/0.44    ( ! [X0] : (v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_19),
% 0.22/0.44    inference(avatar_component_clause,[],[f130])).
% 0.22/0.44  fof(f130,plain,(
% 0.22/0.44    spl3_19 <=> ! [X0] : (v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.44  fof(f132,plain,(
% 0.22/0.44    spl3_19 | ~spl3_6 | ~spl3_12 | ~spl3_16 | ~spl3_17 | ~spl3_18),
% 0.22/0.44    inference(avatar_split_clause,[],[f128,f120,f113,f108,f90,f65,f130])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    spl3_6 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f90,plain,(
% 0.22/0.44    spl3_12 <=> ! [X1,X0] : (v5_funct_1(X1,X0) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.44  fof(f108,plain,(
% 0.22/0.44    spl3_16 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.44  fof(f113,plain,(
% 0.22/0.44    spl3_17 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.44  fof(f120,plain,(
% 0.22/0.44    spl3_18 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.44  fof(f128,plain,(
% 0.22/0.44    ( ! [X0] : (v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl3_6 | ~spl3_12 | ~spl3_16 | ~spl3_17 | ~spl3_18)),
% 0.22/0.44    inference(subsumption_resolution,[],[f127,f110])).
% 0.22/0.44  fof(f110,plain,(
% 0.22/0.44    v1_relat_1(k1_xboole_0) | ~spl3_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f108])).
% 0.22/0.44  fof(f127,plain,(
% 0.22/0.44    ( ! [X0] : (v5_funct_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl3_6 | ~spl3_12 | ~spl3_17 | ~spl3_18)),
% 0.22/0.44    inference(subsumption_resolution,[],[f126,f115])).
% 0.22/0.44  fof(f115,plain,(
% 0.22/0.44    v1_funct_1(k1_xboole_0) | ~spl3_17),
% 0.22/0.44    inference(avatar_component_clause,[],[f113])).
% 0.22/0.44  fof(f126,plain,(
% 0.22/0.44    ( ! [X0] : (v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl3_6 | ~spl3_12 | ~spl3_18)),
% 0.22/0.44    inference(subsumption_resolution,[],[f125,f121])).
% 0.22/0.44  fof(f121,plain,(
% 0.22/0.44    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl3_18),
% 0.22/0.44    inference(avatar_component_clause,[],[f120])).
% 0.22/0.44  fof(f125,plain,(
% 0.22/0.44    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl3_6 | ~spl3_12)),
% 0.22/0.44    inference(superposition,[],[f91,f67])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f65])).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f90])).
% 0.22/0.44  fof(f122,plain,(
% 0.22/0.44    spl3_18 | ~spl3_7 | ~spl3_8 | ~spl3_14),
% 0.22/0.44    inference(avatar_split_clause,[],[f118,f98,f74,f70,f120])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    spl3_7 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl3_8 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.44  fof(f98,plain,(
% 0.22/0.44    spl3_14 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.44  fof(f118,plain,(
% 0.22/0.44    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl3_7 | ~spl3_8 | ~spl3_14)),
% 0.22/0.44    inference(subsumption_resolution,[],[f117,f71])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f70])).
% 0.22/0.44  fof(f117,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) ) | (~spl3_8 | ~spl3_14)),
% 0.22/0.44    inference(superposition,[],[f99,f75])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f74])).
% 0.22/0.44  fof(f99,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl3_14),
% 0.22/0.44    inference(avatar_component_clause,[],[f98])).
% 0.22/0.44  fof(f116,plain,(
% 0.22/0.44    spl3_17 | ~spl3_4 | ~spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f106,f78,f55,f113])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    spl3_4 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    spl3_9 <=> ! [X0] : v1_funct_1(k6_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f106,plain,(
% 0.22/0.44    v1_funct_1(k1_xboole_0) | (~spl3_4 | ~spl3_9)),
% 0.22/0.44    inference(superposition,[],[f79,f57])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f55])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) ) | ~spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f78])).
% 0.22/0.44  fof(f111,plain,(
% 0.22/0.44    spl3_16 | ~spl3_4 | ~spl3_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f105,f82,f55,f108])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    spl3_10 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    v1_relat_1(k1_xboole_0) | (~spl3_4 | ~spl3_10)),
% 0.22/0.44    inference(superposition,[],[f83,f57])).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f82])).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    spl3_14),
% 0.22/0.44    inference(avatar_split_clause,[],[f38,f98])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).
% 0.22/0.44  % (11387)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(rectify,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.44  fof(f92,plain,(
% 0.22/0.44    spl3_12),
% 0.22/0.44    inference(avatar_split_clause,[],[f35,f90])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v5_funct_1(X1,X0) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(rectify,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(nnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    spl3_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f32,f82])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f33,f78])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    spl3_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f31,f74])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f30,f70])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f28,f65])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f27,f55])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f50])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    v1_relat_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,negated_conjecture,(
% 0.22/0.44    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.44    inference(negated_conjecture,[],[f8])).
% 0.22/0.44  fof(f8,conjecture,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f25,f45])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    v1_funct_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ~spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f40])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (11386)------------------------------
% 0.22/0.44  % (11386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (11386)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (11386)Memory used [KB]: 10618
% 0.22/0.44  % (11386)Time elapsed: 0.006 s
% 0.22/0.44  % (11386)------------------------------
% 0.22/0.44  % (11386)------------------------------
% 0.22/0.44  % (11380)Success in time 0.073 s
%------------------------------------------------------------------------------

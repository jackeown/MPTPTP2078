%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 122 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  251 ( 371 expanded)
%              Number of equality atoms :  111 ( 186 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f476,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f285,f341,f431,f475])).

fof(f475,plain,
    ( spl4_1
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f451,f153])).

fof(f153,plain,
    ( ! [X3] : k1_xboole_0 = X3
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl4_6
  <=> ! [X3] : k1_xboole_0 = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f451,plain,
    ( k1_xboole_0 != k3_yellow_0(k1_xboole_0)
    | spl4_1
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f92,f153])).

fof(f92,plain,
    ( k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_1
  <=> k1_xboole_0 = k3_yellow_0(k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f431,plain,
    ( spl4_1
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | spl4_1
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f428,f334])).

fof(f334,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl4_19
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f428,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl4_1
    | ~ spl4_8 ),
    inference(trivial_inequality_removal,[],[f427])).

fof(f427,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl4_1
    | ~ spl4_8 ),
    inference(superposition,[],[f92,f424])).

fof(f424,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))
        | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f162,f355])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_8 ),
    inference(superposition,[],[f273,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f273,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl4_8
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f162,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f49,f110])).

fof(f110,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f50,f73])).

fof(f73,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f50,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

% (12483)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f17,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f341,plain,
    ( ~ spl4_2
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl4_2
    | spl4_19 ),
    inference(subsumption_resolution,[],[f338,f139])).

fof(f139,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f132,f97])).

fof(f97,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f132,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
    inference(backward_demodulation,[],[f80,f128])).

fof(f128,plain,(
    ! [X1] : k1_xboole_0 = sK1(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f127,f82])).

fof(f82,plain,(
    ! [X0] : v1_relat_1(sK1(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK1(X0,X1))
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k2_relat_1(sK1(X0,X1)),X0)
        & k1_relat_1(sK1(X0,X1)) = X1
        & v1_relat_1(sK1(X0,X1)) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_relat_1(X2) )
     => ( r1_tarski(k2_relat_1(sK1(X0,X1)),X0)
        & k1_relat_1(sK1(X0,X1)) = X1
        & v1_relat_1(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( v1_relat_1(X2)
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f127,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK1(X1,k1_xboole_0)
      | ~ v1_relat_1(sK1(X1,k1_xboole_0)) ) ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK1(X1,k1_xboole_0)
      | ~ v1_relat_1(sK1(X1,k1_xboole_0)) ) ),
    inference(superposition,[],[f63,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(sK1(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK1(X0,X1)) = X1
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f80,plain,(
    ! [X0] : r1_tarski(k2_relat_1(sK1(X0,k1_xboole_0)),X0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(sK1(X0,X1)),X0)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f338,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl4_19 ),
    inference(resolution,[],[f335,f85])).

fof(f85,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

% (12479)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f335,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f333])).

fof(f285,plain,
    ( spl4_8
    | spl4_6
    | spl4_6 ),
    inference(avatar_split_clause,[],[f284,f152,f152,f272])).

fof(f284,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f235,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k11_relat_1(k1_xboole_0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f68,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t203_relat_1)).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k11_relat_1(k1_xboole_0,X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f58,f165])).

fof(f165,plain,(
    ! [X2,X3] :
      ( k11_relat_1(k1_xboole_0,X3) = X2
      | ~ r2_hidden(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f68,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f67,f95])).

fof(f67,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f93,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f48,f90])).

fof(f48,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f33])).

fof(f33,plain,
    ( ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))
   => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:29:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (12470)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (12476)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (12478)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (12467)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (12466)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (12484)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (12485)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (12473)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (12486)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (12477)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (12482)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (12477)Refutation not found, incomplete strategy% (12477)------------------------------
% 0.22/0.53  % (12477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12477)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (12477)Memory used [KB]: 1663
% 0.22/0.53  % (12477)Time elapsed: 0.078 s
% 0.22/0.53  % (12477)------------------------------
% 0.22/0.53  % (12477)------------------------------
% 0.22/0.54  % (12469)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (12475)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (12475)Refutation not found, incomplete strategy% (12475)------------------------------
% 0.22/0.54  % (12475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12475)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12475)Memory used [KB]: 10618
% 0.22/0.54  % (12475)Time elapsed: 0.123 s
% 0.22/0.54  % (12475)------------------------------
% 0.22/0.54  % (12475)------------------------------
% 0.22/0.54  % (12490)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (12490)Refutation not found, incomplete strategy% (12490)------------------------------
% 0.22/0.54  % (12490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12490)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12490)Memory used [KB]: 6140
% 0.22/0.54  % (12490)Time elapsed: 0.131 s
% 0.22/0.54  % (12490)------------------------------
% 0.22/0.54  % (12490)------------------------------
% 0.22/0.54  % (12484)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f476,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f93,f98,f285,f341,f431,f475])).
% 0.22/0.55  fof(f475,plain,(
% 0.22/0.55    spl4_1 | ~spl4_6),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f474])).
% 0.22/0.55  fof(f474,plain,(
% 0.22/0.55    $false | (spl4_1 | ~spl4_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f451,f153])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    ( ! [X3] : (k1_xboole_0 = X3) ) | ~spl4_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f152])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    spl4_6 <=> ! [X3] : k1_xboole_0 = X3),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.55  fof(f451,plain,(
% 0.22/0.55    k1_xboole_0 != k3_yellow_0(k1_xboole_0) | (spl4_1 | ~spl4_6)),
% 0.22/0.55    inference(backward_demodulation,[],[f92,f153])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) | spl4_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f90])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    spl4_1 <=> k1_xboole_0 = k3_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.55  fof(f431,plain,(
% 0.22/0.55    spl4_1 | ~spl4_8 | ~spl4_19),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f430])).
% 0.22/0.55  fof(f430,plain,(
% 0.22/0.55    $false | (spl4_1 | ~spl4_8 | ~spl4_19)),
% 0.22/0.55    inference(subsumption_resolution,[],[f428,f334])).
% 0.22/0.55  fof(f334,plain,(
% 0.22/0.55    r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | ~spl4_19),
% 0.22/0.55    inference(avatar_component_clause,[],[f333])).
% 0.22/0.55  fof(f333,plain,(
% 0.22/0.55    spl4_19 <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.55  fof(f428,plain,(
% 0.22/0.55    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | (spl4_1 | ~spl4_8)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f427])).
% 0.22/0.55  fof(f427,plain,(
% 0.22/0.55    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | (spl4_1 | ~spl4_8)),
% 0.22/0.55    inference(superposition,[],[f92,f424])).
% 0.22/0.55  fof(f424,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl4_8),
% 0.22/0.55    inference(subsumption_resolution,[],[f162,f355])).
% 0.22/0.55  fof(f355,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) ) | ~spl4_8),
% 0.22/0.55    inference(superposition,[],[f273,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.55  fof(f273,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f272])).
% 0.22/0.55  fof(f272,plain,(
% 0.22/0.55    spl4_8 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(superposition,[],[f49,f110])).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f50,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  % (12483)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  fof(f17,axiom,(
% 0.22/0.55    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.22/0.55    inference(flattening,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,axiom,(
% 0.22/0.55    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.22/0.55  fof(f341,plain,(
% 0.22/0.55    ~spl4_2 | spl4_19),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f340])).
% 0.22/0.55  fof(f340,plain,(
% 0.22/0.55    $false | (~spl4_2 | spl4_19)),
% 0.22/0.55    inference(subsumption_resolution,[],[f338,f139])).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_2),
% 0.22/0.55    inference(forward_demodulation,[],[f132,f97])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f95])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    spl4_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0)) )),
% 0.22/0.55    inference(backward_demodulation,[],[f80,f128])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = sK1(X1,k1_xboole_0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f127,f82])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0] : (v1_relat_1(sK1(X0,k1_xboole_0))) )),
% 0.22/0.55    inference(equality_resolution,[],[f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(sK1(X0,X1)) | k1_xboole_0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(k2_relat_1(sK1(X0,X1)),X0) & k1_relat_1(sK1(X0,X1)) = X1 & v1_relat_1(sK1(X0,X1))) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_relat_1(X2)) => (r1_tarski(k2_relat_1(sK1(X0,X1)),X0) & k1_relat_1(sK1(X0,X1)) = X1 & v1_relat_1(sK1(X0,X1))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_relat_1(X2)) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.55    inference(flattening,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1] : (? [X2] : ((r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1) & v1_relat_1(X2)) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1] : ~(! [X2] : (v1_relat_1(X2) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = sK1(X1,k1_xboole_0) | ~v1_relat_1(sK1(X1,k1_xboole_0))) )),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f124])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1(X1,k1_xboole_0) | ~v1_relat_1(sK1(X1,k1_xboole_0))) )),
% 0.22/0.55    inference(superposition,[],[f63,f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK1(X0,k1_xboole_0))) )),
% 0.22/0.55    inference(equality_resolution,[],[f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relat_1(sK1(X0,X1)) = X1 | k1_xboole_0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(sK1(X0,k1_xboole_0)),X0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(sK1(X0,X1)),X0) | k1_xboole_0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f338,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,sK0) | spl4_19),
% 0.22/0.55    inference(resolution,[],[f335,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.22/0.55  % (12479)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.55    inference(rectify,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.55  fof(f335,plain,(
% 0.22/0.55    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | spl4_19),
% 0.22/0.55    inference(avatar_component_clause,[],[f333])).
% 0.22/0.55  fof(f285,plain,(
% 0.22/0.55    spl4_8 | spl4_6 | spl4_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f284,f152,f152,f272])).
% 0.22/0.55  fof(f284,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f235,f164])).
% 0.22/0.55  fof(f164,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X1) | ~r2_hidden(X1,X0)) )),
% 0.22/0.55    inference(superposition,[],[f68,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(flattening,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2 | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2 | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (r2_hidden(X0,X1) => k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t203_relat_1)).
% 0.22/0.55  fof(f235,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 != k11_relat_1(k1_xboole_0,X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.22/0.55    inference(superposition,[],[f58,f165])).
% 0.22/0.55  fof(f165,plain,(
% 0.22/0.55    ( ! [X2,X3] : (k11_relat_1(k1_xboole_0,X3) = X2 | ~r2_hidden(X3,k1_xboole_0)) )),
% 0.22/0.55    inference(superposition,[],[f68,f84])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    spl4_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f67,f95])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    ~spl4_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f48,f90])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,negated_conjecture,(
% 0.22/0.55    ~! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.22/0.55    inference(negated_conjecture,[],[f18])).
% 0.22/0.55  fof(f18,conjecture,(
% 0.22/0.55    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (12484)------------------------------
% 0.22/0.55  % (12484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12484)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (12484)Memory used [KB]: 6396
% 0.22/0.55  % (12484)Time elapsed: 0.127 s
% 0.22/0.55  % (12484)------------------------------
% 0.22/0.55  % (12484)------------------------------
% 0.22/0.55  % (12464)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (12465)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (12463)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (12474)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (12472)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (12461)Success in time 0.187 s
% 0.22/0.55  % (12471)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (12492)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (12489)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (12488)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (12481)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (12480)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (12473)Refutation not found, incomplete strategy% (12473)------------------------------
% 0.22/0.56  % (12473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (12491)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (12482)Refutation not found, incomplete strategy% (12482)------------------------------
% 0.22/0.56  % (12482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
%------------------------------------------------------------------------------

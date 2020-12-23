%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 139 expanded)
%              Number of leaves         :   15 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  214 ( 360 expanded)
%              Number of equality atoms :   43 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f357,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f46,f76,f150,f231,f242,f245,f261,f326,f356])).

fof(f356,plain,
    ( spl5_1
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | spl5_1
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(trivial_inequality_removal,[],[f353])).

fof(f353,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl5_1
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(superposition,[],[f251,f327])).

fof(f327,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_15 ),
    inference(resolution,[],[f325,f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f325,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl5_15
  <=> ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f251,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl5_1
    | ~ spl5_5 ),
    inference(superposition,[],[f39,f247])).

fof(f247,plain,
    ( k9_relat_1(sK1,sK0) = k2_relat_1(k1_xboole_0)
    | ~ spl5_5 ),
    inference(superposition,[],[f65,f70])).

fof(f70,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_5
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f65,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f30,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f39,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl5_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f326,plain,
    ( ~ spl5_6
    | spl5_15
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f322,f140,f69,f324,f72])).

fof(f72,plain,
    ( spl5_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f140,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK4(X0,X1,sK1),sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f321,f247])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_11 ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k9_relat_1(sK1,sK0)) )
    | ~ spl5_11 ),
    inference(resolution,[],[f141,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(X0,X1,sK1),sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f261,plain,
    ( ~ spl5_6
    | spl5_11
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f255,f41,f140,f72])).

fof(f41,plain,
    ( spl5_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(X0,X1,sK1),sK0)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f244,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f45,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f45,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f245,plain,
    ( spl5_5
    | ~ spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f243,f41,f72,f69])).

fof(f243,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f45,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f242,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl5_14 ),
    inference(resolution,[],[f237,f22])).

fof(f237,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_14 ),
    inference(resolution,[],[f230,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f230,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl5_14
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f231,plain,
    ( spl5_5
    | ~ spl5_14
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f227,f38,f229,f69])).

fof(f227,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f226])).

fof(f226,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl5_1 ),
    inference(superposition,[],[f86,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f86,plain,(
    ! [X0] :
      ( k1_xboole_0 != k9_relat_1(sK1,X0)
      | ~ v1_relat_1(k7_relat_1(sK1,X0))
      | k1_xboole_0 = k7_relat_1(sK1,X0) ) ),
    inference(superposition,[],[f24,f65])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f150,plain,
    ( ~ spl5_6
    | spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f132,f69,f41,f72])).

fof(f132,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl5_5 ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl5_5 ),
    inference(superposition,[],[f32,f70])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f73,f22])).

fof(f73,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f46,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f20,f41,f38])).

fof(f20,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f21,f41,f38])).

fof(f21,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:19:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (30833)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.48  % (30840)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.48  % (30850)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.49  % (30848)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.49  % (30842)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.50  % (30829)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (30838)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (30832)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (30832)Refutation not found, incomplete strategy% (30832)------------------------------
% 0.22/0.51  % (30832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30832)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30832)Memory used [KB]: 10618
% 0.22/0.51  % (30832)Time elapsed: 0.092 s
% 0.22/0.51  % (30832)------------------------------
% 0.22/0.51  % (30832)------------------------------
% 0.22/0.51  % (30852)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (30837)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (30830)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (30842)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f357,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f43,f46,f76,f150,f231,f242,f245,f261,f326,f356])).
% 0.22/0.52  fof(f356,plain,(
% 0.22/0.52    spl5_1 | ~spl5_5 | ~spl5_15),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f355])).
% 0.22/0.52  fof(f355,plain,(
% 0.22/0.52    $false | (spl5_1 | ~spl5_5 | ~spl5_15)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f353])).
% 0.22/0.52  fof(f353,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | (spl5_1 | ~spl5_5 | ~spl5_15)),
% 0.22/0.52    inference(superposition,[],[f251,f327])).
% 0.22/0.52  fof(f327,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl5_15),
% 0.22/0.52    inference(resolution,[],[f325,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.52  fof(f325,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) ) | ~spl5_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f324])).
% 0.22/0.52  fof(f324,plain,(
% 0.22/0.52    spl5_15 <=> ! [X0] : ~r2_hidden(X0,k2_relat_1(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.52  fof(f251,plain,(
% 0.22/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (spl5_1 | ~spl5_5)),
% 0.22/0.52    inference(superposition,[],[f39,f247])).
% 0.22/0.52  fof(f247,plain,(
% 0.22/0.52    k9_relat_1(sK1,sK0) = k2_relat_1(k1_xboole_0) | ~spl5_5),
% 0.22/0.52    inference(superposition,[],[f65,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl5_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl5_5 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.22/0.52    inference(resolution,[],[f30,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    k1_xboole_0 != k9_relat_1(sK1,sK0) | spl5_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    spl5_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.52  fof(f326,plain,(
% 0.22/0.52    ~spl5_6 | spl5_15 | ~spl5_5 | ~spl5_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f322,f140,f69,f324,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    spl5_6 <=> v1_relat_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    spl5_11 <=> ! [X1,X0] : (~r2_hidden(sK4(X0,X1,sK1),sK0) | ~r2_hidden(X0,k9_relat_1(sK1,X1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.52  fof(f322,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1)) ) | (~spl5_5 | ~spl5_11)),
% 0.22/0.52    inference(forward_demodulation,[],[f321,f247])).
% 0.22/0.52  fof(f321,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)) ) | ~spl5_11),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f320])).
% 0.22/0.52  fof(f320,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k9_relat_1(sK1,sK0))) ) | ~spl5_11),
% 0.22/0.52    inference(resolution,[],[f141,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,sK1),sK0) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) ) | ~spl5_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f140])).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    ~spl5_6 | spl5_11 | ~spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f255,f41,f140,f72])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    spl5_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.52  fof(f255,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,sK1),sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) ) | ~spl5_2),
% 0.22/0.52    inference(resolution,[],[f244,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f244,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,sK0)) ) | ~spl5_2),
% 0.22/0.52    inference(resolution,[],[f45,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl5_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f41])).
% 0.22/0.52  fof(f245,plain,(
% 0.22/0.52    spl5_5 | ~spl5_6 | ~spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f243,f41,f72,f69])).
% 0.22/0.52  fof(f243,plain,(
% 0.22/0.52    ~v1_relat_1(sK1) | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl5_2),
% 0.22/0.52    inference(resolution,[],[f45,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.52  fof(f242,plain,(
% 0.22/0.52    spl5_14),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f241])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    $false | spl5_14),
% 0.22/0.52    inference(resolution,[],[f237,f22])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    ~v1_relat_1(sK1) | spl5_14),
% 0.22/0.52    inference(resolution,[],[f230,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.52  fof(f230,plain,(
% 0.22/0.52    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl5_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f229])).
% 0.22/0.52  fof(f229,plain,(
% 0.22/0.52    spl5_14 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.52  fof(f231,plain,(
% 0.22/0.52    spl5_5 | ~spl5_14 | ~spl5_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f227,f38,f229,f69])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    ~v1_relat_1(k7_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl5_1),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f226])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k7_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl5_1),
% 0.22/0.52    inference(superposition,[],[f86,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl5_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f38])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | ~v1_relat_1(k7_relat_1(sK1,X0)) | k1_xboole_0 = k7_relat_1(sK1,X0)) )),
% 0.22/0.52    inference(superposition,[],[f24,f65])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    ~spl5_6 | spl5_2 | ~spl5_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f132,f69,f41,f72])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl5_5),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f130])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl5_5),
% 0.22/0.52    inference(superposition,[],[f32,f70])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    spl5_6),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    $false | spl5_6),
% 0.22/0.52    inference(resolution,[],[f73,f22])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ~v1_relat_1(sK1) | spl5_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f72])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    spl5_1 | spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f20,f41,f38])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ~spl5_1 | ~spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f21,f41,f38])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (30842)------------------------------
% 0.22/0.52  % (30842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30842)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (30842)Memory used [KB]: 10874
% 0.22/0.52  % (30842)Time elapsed: 0.102 s
% 0.22/0.52  % (30842)------------------------------
% 0.22/0.52  % (30842)------------------------------
% 0.22/0.52  % (30851)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (30824)Success in time 0.157 s
%------------------------------------------------------------------------------

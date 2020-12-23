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
% DateTime   : Thu Dec  3 12:48:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 118 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  211 ( 335 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f928,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f49,f247,f500,f575,f585,f590,f613,f927])).

fof(f927,plain,
    ( spl4_2
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f925])).

fof(f925,plain,
    ( $false
    | spl4_2
    | ~ spl4_15 ),
    inference(resolution,[],[f914,f45])).

fof(f45,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f914,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_15 ),
    inference(duplicate_literal_removal,[],[f911])).

fof(f911,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_15 ),
    inference(resolution,[],[f781,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f781,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK3(k1_relat_1(sK1),X4),sK0)
        | r1_xboole_0(k1_relat_1(sK1),X4) )
    | ~ spl4_15 ),
    inference(resolution,[],[f633,f50])).

fof(f50,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f633,plain,
    ( ! [X5] :
        ( r2_hidden(sK3(k1_relat_1(sK1),X5),k1_xboole_0)
        | ~ r2_hidden(sK3(k1_relat_1(sK1),X5),sK0)
        | r1_xboole_0(k1_relat_1(sK1),X5) )
    | ~ spl4_15 ),
    inference(resolution,[],[f308,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f308,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(sK1))
        | r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl4_15
  <=> ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f613,plain,
    ( ~ spl4_8
    | spl4_15
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f612,f41,f307,f234])).

fof(f234,plain,
    ( spl4_8
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f41,plain,
    ( spl4_1
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f612,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f601,f25])).

fof(f25,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f601,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_relat_1(k1_xboole_0))
        | ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl4_1 ),
    inference(superposition,[],[f39,f47])).

fof(f47,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f590,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | spl4_23 ),
    inference(resolution,[],[f588,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f588,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_23 ),
    inference(resolution,[],[f562,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f562,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl4_23
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f585,plain,
    ( ~ spl4_8
    | spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f576,f44,f231,f234])).

fof(f231,plain,
    ( spl4_7
  <=> ! [X4] :
        ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X4))
        | ~ r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X4))),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f576,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X0))),sK0)
        | ~ v1_relat_1(sK1)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f538,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1))),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f538,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f48,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f575,plain,
    ( spl4_1
    | ~ spl4_23
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f556,f498,f561,f41])).

fof(f498,plain,
    ( spl4_20
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f556,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f555])).

fof(f555,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_20 ),
    inference(superposition,[],[f28,f499])).

fof(f499,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f498])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f500,plain,
    ( ~ spl4_8
    | spl4_20
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f496,f231,f498,f234])).

fof(f496,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_7 ),
    inference(duplicate_literal_removal,[],[f494])).

fof(f494,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f232,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1))),X1)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f37,f30])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f232,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X4))),sK0)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X4)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f231])).

fof(f247,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f235,f24])).

fof(f235,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f234])).

fof(f49,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f22,f44,f41])).

fof(f22,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f23,f44,f41])).

fof(f23,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:17:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (27916)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (27915)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (27914)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (27910)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (27932)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (27913)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.52  % (27921)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (27925)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.52  % (27930)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (27924)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (27911)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (27922)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (27920)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (27918)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (27931)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.52  % (27912)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.52  % (27920)Refutation not found, incomplete strategy% (27920)------------------------------
% 0.21/0.52  % (27920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27920)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27920)Memory used [KB]: 10618
% 0.21/0.52  % (27920)Time elapsed: 0.102 s
% 0.21/0.52  % (27920)------------------------------
% 0.21/0.52  % (27920)------------------------------
% 0.21/0.52  % (27917)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (27923)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.53  % (27928)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.53  % (27913)Refutation not found, incomplete strategy% (27913)------------------------------
% 0.21/0.53  % (27913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27913)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27913)Memory used [KB]: 10490
% 0.21/0.53  % (27913)Time elapsed: 0.111 s
% 0.21/0.53  % (27913)------------------------------
% 0.21/0.53  % (27913)------------------------------
% 0.21/0.53  % (27929)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.53  % (27933)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.53  % (27919)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.53  % (27926)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.54  % (27927)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.54  % (27922)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 1.45/0.56  % SZS output start Proof for theBenchmark
% 1.45/0.56  fof(f928,plain,(
% 1.45/0.56    $false),
% 1.45/0.56    inference(avatar_sat_refutation,[],[f46,f49,f247,f500,f575,f585,f590,f613,f927])).
% 1.45/0.56  fof(f927,plain,(
% 1.45/0.56    spl4_2 | ~spl4_15),
% 1.45/0.56    inference(avatar_contradiction_clause,[],[f925])).
% 1.45/0.56  fof(f925,plain,(
% 1.45/0.56    $false | (spl4_2 | ~spl4_15)),
% 1.45/0.56    inference(resolution,[],[f914,f45])).
% 1.45/0.56  fof(f45,plain,(
% 1.45/0.56    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl4_2),
% 1.45/0.56    inference(avatar_component_clause,[],[f44])).
% 1.45/0.56  fof(f44,plain,(
% 1.45/0.56    spl4_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.45/0.56  fof(f914,plain,(
% 1.45/0.56    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl4_15),
% 1.45/0.56    inference(duplicate_literal_removal,[],[f911])).
% 1.45/0.56  fof(f911,plain,(
% 1.45/0.56    r1_xboole_0(k1_relat_1(sK1),sK0) | r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl4_15),
% 1.45/0.56    inference(resolution,[],[f781,f33])).
% 1.45/0.56  fof(f33,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f17])).
% 1.45/0.56  fof(f17,plain,(
% 1.45/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.56    inference(ennf_transformation,[],[f12])).
% 1.45/0.56  fof(f12,plain,(
% 1.45/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.56    inference(rectify,[],[f2])).
% 1.45/0.56  fof(f2,axiom,(
% 1.45/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.45/0.56  fof(f781,plain,(
% 1.45/0.56    ( ! [X4] : (~r2_hidden(sK3(k1_relat_1(sK1),X4),sK0) | r1_xboole_0(k1_relat_1(sK1),X4)) ) | ~spl4_15),
% 1.45/0.56    inference(resolution,[],[f633,f50])).
% 1.45/0.56  fof(f50,plain,(
% 1.45/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.45/0.56    inference(resolution,[],[f36,f27])).
% 1.45/0.56  fof(f27,plain,(
% 1.45/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f4])).
% 1.45/0.56  fof(f4,axiom,(
% 1.45/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.45/0.56  fof(f36,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f20])).
% 1.45/0.56  fof(f20,plain,(
% 1.45/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.45/0.56    inference(ennf_transformation,[],[f5])).
% 1.45/0.56  fof(f5,axiom,(
% 1.45/0.56    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.45/0.56  fof(f633,plain,(
% 1.45/0.56    ( ! [X5] : (r2_hidden(sK3(k1_relat_1(sK1),X5),k1_xboole_0) | ~r2_hidden(sK3(k1_relat_1(sK1),X5),sK0) | r1_xboole_0(k1_relat_1(sK1),X5)) ) | ~spl4_15),
% 1.45/0.56    inference(resolution,[],[f308,f32])).
% 1.45/0.56  fof(f32,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f17])).
% 1.45/0.56  fof(f308,plain,(
% 1.45/0.56    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK1)) | r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,sK0)) ) | ~spl4_15),
% 1.45/0.56    inference(avatar_component_clause,[],[f307])).
% 1.45/0.56  fof(f307,plain,(
% 1.45/0.56    spl4_15 <=> ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X2,sK0))),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.45/0.56  fof(f613,plain,(
% 1.45/0.56    ~spl4_8 | spl4_15 | ~spl4_1),
% 1.45/0.56    inference(avatar_split_clause,[],[f612,f41,f307,f234])).
% 1.45/0.56  fof(f234,plain,(
% 1.45/0.56    spl4_8 <=> v1_relat_1(sK1)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.45/0.56  fof(f41,plain,(
% 1.45/0.56    spl4_1 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.45/0.56  fof(f612,plain,(
% 1.45/0.56    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl4_1),
% 1.45/0.56    inference(forward_demodulation,[],[f601,f25])).
% 1.45/0.56  fof(f25,plain,(
% 1.45/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.45/0.56    inference(cnf_transformation,[],[f7])).
% 1.45/0.56  fof(f7,axiom,(
% 1.45/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.45/0.56  fof(f601,plain,(
% 1.45/0.56    ( ! [X2] : (r2_hidden(X2,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl4_1),
% 1.45/0.56    inference(superposition,[],[f39,f47])).
% 1.45/0.56  fof(f47,plain,(
% 1.45/0.56    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl4_1),
% 1.45/0.56    inference(avatar_component_clause,[],[f41])).
% 1.45/0.56  fof(f39,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f21])).
% 1.45/0.56  fof(f21,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 1.45/0.56    inference(ennf_transformation,[],[f9])).
% 1.45/0.56  fof(f9,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 1.45/0.56  fof(f590,plain,(
% 1.45/0.56    spl4_23),
% 1.45/0.56    inference(avatar_contradiction_clause,[],[f589])).
% 1.45/0.56  fof(f589,plain,(
% 1.45/0.56    $false | spl4_23),
% 1.45/0.56    inference(resolution,[],[f588,f24])).
% 1.45/0.56  fof(f24,plain,(
% 1.45/0.56    v1_relat_1(sK1)),
% 1.45/0.56    inference(cnf_transformation,[],[f13])).
% 1.45/0.56  fof(f13,plain,(
% 1.45/0.56    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.45/0.56    inference(ennf_transformation,[],[f11])).
% 1.45/0.56  fof(f11,negated_conjecture,(
% 1.45/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.45/0.56    inference(negated_conjecture,[],[f10])).
% 1.45/0.56  fof(f10,conjecture,(
% 1.45/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 1.45/0.56  fof(f588,plain,(
% 1.45/0.56    ~v1_relat_1(sK1) | spl4_23),
% 1.45/0.56    inference(resolution,[],[f562,f34])).
% 1.45/0.56  fof(f34,plain,(
% 1.45/0.56    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f18])).
% 1.45/0.56  fof(f18,plain,(
% 1.45/0.56    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f6])).
% 1.45/0.56  fof(f6,axiom,(
% 1.45/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.45/0.56  fof(f562,plain,(
% 1.45/0.56    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl4_23),
% 1.45/0.56    inference(avatar_component_clause,[],[f561])).
% 1.45/0.56  fof(f561,plain,(
% 1.45/0.56    spl4_23 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.45/0.56  fof(f585,plain,(
% 1.45/0.56    ~spl4_8 | spl4_7 | ~spl4_2),
% 1.45/0.56    inference(avatar_split_clause,[],[f576,f44,f231,f234])).
% 1.45/0.56  fof(f231,plain,(
% 1.45/0.56    spl4_7 <=> ! [X4] : (k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X4)) | ~r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X4))),sK0))),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.45/0.56  fof(f576,plain,(
% 1.45/0.56    ( ! [X0] : (~r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X0))),sK0) | ~v1_relat_1(sK1) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl4_2),
% 1.45/0.56    inference(resolution,[],[f538,f83])).
% 1.45/0.56  fof(f83,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1))),k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1))) )),
% 1.45/0.56    inference(resolution,[],[f38,f30])).
% 1.45/0.56  fof(f30,plain,(
% 1.45/0.56    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.45/0.56    inference(cnf_transformation,[],[f16])).
% 1.45/0.56  fof(f16,plain,(
% 1.45/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.45/0.56    inference(ennf_transformation,[],[f3])).
% 1.45/0.56  fof(f3,axiom,(
% 1.45/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.45/0.56  fof(f38,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f21])).
% 1.45/0.56  fof(f538,plain,(
% 1.45/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,sK0)) ) | ~spl4_2),
% 1.45/0.56    inference(resolution,[],[f48,f31])).
% 1.45/0.56  fof(f31,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f17])).
% 1.45/0.56  fof(f48,plain,(
% 1.45/0.56    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl4_2),
% 1.45/0.56    inference(avatar_component_clause,[],[f44])).
% 1.45/0.56  fof(f575,plain,(
% 1.45/0.56    spl4_1 | ~spl4_23 | ~spl4_20),
% 1.45/0.56    inference(avatar_split_clause,[],[f556,f498,f561,f41])).
% 1.45/0.56  fof(f498,plain,(
% 1.45/0.56    spl4_20 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.45/0.56  fof(f556,plain,(
% 1.45/0.56    ~v1_relat_1(k7_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl4_20),
% 1.45/0.56    inference(trivial_inequality_removal,[],[f555])).
% 1.45/0.56  fof(f555,plain,(
% 1.45/0.56    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k7_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl4_20),
% 1.45/0.56    inference(superposition,[],[f28,f499])).
% 1.45/0.56  fof(f499,plain,(
% 1.45/0.56    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl4_20),
% 1.45/0.56    inference(avatar_component_clause,[],[f498])).
% 1.45/0.56  fof(f28,plain,(
% 1.45/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.45/0.56    inference(cnf_transformation,[],[f15])).
% 1.45/0.56  fof(f15,plain,(
% 1.45/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.45/0.56    inference(flattening,[],[f14])).
% 1.45/0.56  fof(f14,plain,(
% 1.45/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f8])).
% 1.45/0.56  fof(f8,axiom,(
% 1.45/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.45/0.56  fof(f500,plain,(
% 1.45/0.56    ~spl4_8 | spl4_20 | ~spl4_7),
% 1.45/0.56    inference(avatar_split_clause,[],[f496,f231,f498,f234])).
% 1.45/0.56  fof(f496,plain,(
% 1.45/0.56    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl4_7),
% 1.45/0.56    inference(duplicate_literal_removal,[],[f494])).
% 1.45/0.56  fof(f494,plain,(
% 1.45/0.56    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl4_7),
% 1.45/0.56    inference(resolution,[],[f232,f80])).
% 1.45/0.56  fof(f80,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1))),X1) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1))) )),
% 1.45/0.56    inference(resolution,[],[f37,f30])).
% 1.45/0.56  fof(f37,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f21])).
% 1.45/0.56  fof(f232,plain,(
% 1.45/0.56    ( ! [X4] : (~r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X4))),sK0) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X4))) ) | ~spl4_7),
% 1.45/0.56    inference(avatar_component_clause,[],[f231])).
% 1.45/0.56  fof(f247,plain,(
% 1.45/0.56    spl4_8),
% 1.45/0.56    inference(avatar_contradiction_clause,[],[f246])).
% 1.45/0.56  fof(f246,plain,(
% 1.45/0.56    $false | spl4_8),
% 1.45/0.56    inference(resolution,[],[f235,f24])).
% 1.45/0.56  fof(f235,plain,(
% 1.45/0.56    ~v1_relat_1(sK1) | spl4_8),
% 1.45/0.56    inference(avatar_component_clause,[],[f234])).
% 1.45/0.56  fof(f49,plain,(
% 1.45/0.56    spl4_1 | spl4_2),
% 1.45/0.56    inference(avatar_split_clause,[],[f22,f44,f41])).
% 1.45/0.56  fof(f22,plain,(
% 1.45/0.56    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f13])).
% 1.45/0.56  fof(f46,plain,(
% 1.45/0.56    ~spl4_1 | ~spl4_2),
% 1.45/0.56    inference(avatar_split_clause,[],[f23,f44,f41])).
% 1.45/0.56  fof(f23,plain,(
% 1.45/0.56    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f13])).
% 1.45/0.56  % SZS output end Proof for theBenchmark
% 1.45/0.56  % (27922)------------------------------
% 1.45/0.56  % (27922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (27922)Termination reason: Refutation
% 1.45/0.56  
% 1.45/0.56  % (27922)Memory used [KB]: 11129
% 1.45/0.56  % (27922)Time elapsed: 0.118 s
% 1.45/0.56  % (27922)------------------------------
% 1.45/0.56  % (27922)------------------------------
% 1.45/0.56  % (27909)Success in time 0.199 s
%------------------------------------------------------------------------------

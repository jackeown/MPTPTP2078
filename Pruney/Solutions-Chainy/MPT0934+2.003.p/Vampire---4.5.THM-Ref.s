%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 181 expanded)
%              Number of leaves         :   14 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  223 ( 852 expanded)
%              Number of equality atoms :   41 ( 323 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f181,f188,f197,f208,f218,f225,f233])).

fof(f233,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f231,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK1 != sK2
    & k2_mcart_1(sK1) = k2_mcart_1(sK2)
    & k1_mcart_1(sK1) = k1_mcart_1(sK2)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0)
    & v1_relat_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k2_mcart_1(X1) = k2_mcart_1(X2)
                & k1_mcart_1(X1) = k1_mcart_1(X2)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,X0) )
        & v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,sK0) )
      & v1_relat_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & k2_mcart_1(X1) = k2_mcart_1(X2)
            & k1_mcart_1(X1) = k1_mcart_1(X2)
            & m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,sK0) )
   => ( ? [X2] :
          ( sK1 != X2
          & k2_mcart_1(X2) = k2_mcart_1(sK1)
          & k1_mcart_1(X2) = k1_mcart_1(sK1)
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k2_mcart_1(X2) = k2_mcart_1(sK1)
        & k1_mcart_1(X2) = k1_mcart_1(sK1)
        & m1_subset_1(X2,sK0) )
   => ( sK1 != sK2
      & k2_mcart_1(sK1) = k2_mcart_1(sK2)
      & k1_mcart_1(sK1) = k1_mcart_1(sK2)
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_relat_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ( k2_mcart_1(X1) = k2_mcart_1(X2)
                    & k1_mcart_1(X1) = k1_mcart_1(X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ( k2_mcart_1(X1) = k2_mcart_1(X2)
                  & k1_mcart_1(X1) = k1_mcart_1(X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_mcart_1)).

fof(f231,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f229,f15])).

fof(f15,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f229,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f219,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f219,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f75,f16])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f75,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(X3)
        | ~ r2_hidden(sK2,X3) )
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_1
  <=> ! [X3] :
        ( ~ r2_hidden(sK2,X3)
        | ~ v1_relat_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f225,plain,
    ( ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f36,f36,f78,f187])).

fof(f187,plain,
    ( ! [X10,X9] :
        ( ~ sQ3_eqProxy(X9,sK1)
        | ~ sQ3_eqProxy(X10,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)))
        | ~ sQ3_eqProxy(X9,X10) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f186])).

% (31237)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f186,plain,
    ( spl4_6
  <=> ! [X9,X10] :
        ( ~ sQ3_eqProxy(X9,X10)
        | ~ sQ3_eqProxy(X10,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)))
        | ~ sQ3_eqProxy(X9,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f78,plain,
    ( sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_2
  <=> sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f36,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f218,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f215,f26])).

fof(f26,plain,(
    sQ3_eqProxy(k2_mcart_1(sK1),k2_mcart_1(sK2)) ),
    inference(equality_proxy_replacement,[],[f20,f24])).

fof(f20,plain,(
    k2_mcart_1(sK1) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f215,plain,
    ( ~ sQ3_eqProxy(k2_mcart_1(sK1),k2_mcart_1(sK2))
    | spl4_8 ),
    inference(resolution,[],[f196,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f24])).

fof(f196,plain,
    ( ~ sQ3_eqProxy(k2_mcart_1(sK2),k2_mcart_1(sK1))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl4_8
  <=> sQ3_eqProxy(k2_mcart_1(sK2),k2_mcart_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f208,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f205,f27])).

fof(f27,plain,(
    sQ3_eqProxy(k1_mcart_1(sK1),k1_mcart_1(sK2)) ),
    inference(equality_proxy_replacement,[],[f19,f24])).

fof(f19,plain,(
    k1_mcart_1(sK1) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f205,plain,
    ( ~ sQ3_eqProxy(k1_mcart_1(sK1),k1_mcart_1(sK2))
    | spl4_7 ),
    inference(resolution,[],[f192,f37])).

fof(f192,plain,
    ( ~ sQ3_eqProxy(k1_mcart_1(sK2),k1_mcart_1(sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl4_7
  <=> sQ3_eqProxy(k1_mcart_1(sK2),k1_mcart_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f197,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | spl4_5 ),
    inference(avatar_split_clause,[],[f182,f178,f194,f190])).

fof(f178,plain,
    ( spl4_5
  <=> sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f182,plain,
    ( ~ sQ3_eqProxy(k2_mcart_1(sK2),k2_mcart_1(sK1))
    | ~ sQ3_eqProxy(k1_mcart_1(sK2),k1_mcart_1(sK1))
    | spl4_5 ),
    inference(resolution,[],[f180,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ3_eqProxy(k4_tarski(X0,X2),k4_tarski(X1,X3))
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f24])).

fof(f180,plain,
    ( ~ sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f178])).

fof(f188,plain,
    ( spl4_1
    | spl4_6 ),
    inference(avatar_split_clause,[],[f104,f186,f74])).

fof(f104,plain,(
    ! [X10,X11,X9] :
      ( ~ sQ3_eqProxy(X9,X10)
      | ~ sQ3_eqProxy(X9,sK1)
      | ~ sQ3_eqProxy(X10,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)))
      | ~ r2_hidden(sK2,X11)
      | ~ v1_relat_1(X11) ) ),
    inference(resolution,[],[f60,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f22,f24])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f60,plain,(
    ! [X2,X3,X1] :
      ( ~ sQ3_eqProxy(X3,sK2)
      | ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X1,sK1)
      | ~ sQ3_eqProxy(X2,X3) ) ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(X0,X2)
      | ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ sQ3_eqProxy(X1,sK2)
      | ~ sQ3_eqProxy(X0,sK1)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(resolution,[],[f45,f38])).

fof(f45,plain,(
    ! [X2] :
      ( ~ sQ3_eqProxy(X2,sK2)
      | ~ sQ3_eqProxy(X2,sK1) ) ),
    inference(resolution,[],[f41,f37])).

fof(f41,plain,(
    ! [X0] :
      ( ~ sQ3_eqProxy(sK1,X0)
      | ~ sQ3_eqProxy(X0,sK2) ) ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,(
    ~ sQ3_eqProxy(sK1,sK2) ),
    inference(equality_proxy_replacement,[],[f21,f24])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f181,plain,
    ( spl4_3
    | ~ spl4_5
    | spl4_2 ),
    inference(avatar_split_clause,[],[f91,f77,f178,f133])).

fof(f133,plain,
    ( spl4_3
  <=> ! [X7] :
        ( ~ r2_hidden(sK1,X7)
        | ~ v1_relat_1(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f91,plain,
    ( ! [X3] :
        ( ~ sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)))
        | ~ r2_hidden(sK1,X3)
        | ~ v1_relat_1(X3) )
    | spl4_2 ),
    inference(resolution,[],[f81,f28])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ sQ3_eqProxy(X0,sK1)
        | ~ sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),X0) )
    | spl4_2 ),
    inference(resolution,[],[f79,f38])).

fof(f79,plain,
    ( ~ sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f147,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f145,f17])).

fof(f17,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f143,f15])).

fof(f143,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f139,f23])).

fof(f139,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f134,f16])).

fof(f134,plain,
    ( ! [X7] :
        ( ~ v1_relat_1(X7)
        | ~ r2_hidden(sK1,X7) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (31236)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (31246)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (31236)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f234,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f147,f181,f188,f197,f208,f218,f225,f233])).
% 0.20/0.47  fof(f233,plain,(
% 0.20/0.47    ~spl4_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f232])).
% 0.20/0.47  fof(f232,plain,(
% 0.20/0.47    $false | ~spl4_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f231,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    m1_subset_1(sK2,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ((sK1 != sK2 & k2_mcart_1(sK1) = k2_mcart_1(sK2) & k1_mcart_1(sK1) = k1_mcart_1(sK2) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,sK0)) & v1_relat_1(sK0) & ~v1_xboole_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X1) = k2_mcart_1(X2) & k1_mcart_1(X1) = k1_mcart_1(X2) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) & v1_relat_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X1) = k2_mcart_1(X2) & k1_mcart_1(X1) = k1_mcart_1(X2) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,sK0)) & v1_relat_1(sK0) & ~v1_xboole_0(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X1) = k2_mcart_1(X2) & k1_mcart_1(X1) = k1_mcart_1(X2) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,sK0)) => (? [X2] : (sK1 != X2 & k2_mcart_1(X2) = k2_mcart_1(sK1) & k1_mcart_1(X2) = k1_mcart_1(sK1) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X2] : (sK1 != X2 & k2_mcart_1(X2) = k2_mcart_1(sK1) & k1_mcart_1(X2) = k1_mcart_1(sK1) & m1_subset_1(X2,sK0)) => (sK1 != sK2 & k2_mcart_1(sK1) = k2_mcart_1(sK2) & k1_mcart_1(sK1) = k1_mcart_1(sK2) & m1_subset_1(sK2,sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X1) = k2_mcart_1(X2) & k1_mcart_1(X1) = k1_mcart_1(X2) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) & v1_relat_1(X0) & ~v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f5])).
% 0.20/0.47  fof(f5,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & (k2_mcart_1(X1) = k2_mcart_1(X2) & k1_mcart_1(X1) = k1_mcart_1(X2))) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) & (v1_relat_1(X0) & ~v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ((k2_mcart_1(X1) = k2_mcart_1(X2) & k1_mcart_1(X1) = k1_mcart_1(X2)) => X1 = X2))))),
% 0.20/0.47    inference(negated_conjecture,[],[f3])).
% 0.20/0.47  fof(f3,conjecture,(
% 0.20/0.47    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ((k2_mcart_1(X1) = k2_mcart_1(X2) & k1_mcart_1(X1) = k1_mcart_1(X2)) => X1 = X2))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_mcart_1)).
% 0.20/0.47  fof(f231,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,sK0) | ~spl4_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f229,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ~v1_xboole_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f229,plain,(
% 0.20/0.47    v1_xboole_0(sK0) | ~m1_subset_1(sK2,sK0) | ~spl4_1),
% 0.20/0.47    inference(resolution,[],[f219,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    ~r2_hidden(sK2,sK0) | ~spl4_1),
% 0.20/0.47    inference(resolution,[],[f75,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ( ! [X3] : (~v1_relat_1(X3) | ~r2_hidden(sK2,X3)) ) | ~spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl4_1 <=> ! [X3] : (~r2_hidden(sK2,X3) | ~v1_relat_1(X3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f225,plain,(
% 0.20/0.47    ~spl4_2 | ~spl4_6),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f221])).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    $false | (~spl4_2 | ~spl4_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f36,f36,f78,f187])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    ( ! [X10,X9] : (~sQ3_eqProxy(X9,sK1) | ~sQ3_eqProxy(X10,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))) | ~sQ3_eqProxy(X9,X10)) ) | ~spl4_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f186])).
% 0.20/0.47  % (31237)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    spl4_6 <=> ! [X9,X10] : (~sQ3_eqProxy(X9,X10) | ~sQ3_eqProxy(X10,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))) | ~sQ3_eqProxy(X9,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),sK1) | ~spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    spl4_2 <=> sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.20/0.47  fof(f218,plain,(
% 0.20/0.47    spl4_8),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f217])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    $false | spl4_8),
% 0.20/0.47    inference(subsumption_resolution,[],[f215,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    sQ3_eqProxy(k2_mcart_1(sK1),k2_mcart_1(sK2))),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f20,f24])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    k2_mcart_1(sK1) = k2_mcart_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f215,plain,(
% 0.20/0.47    ~sQ3_eqProxy(k2_mcart_1(sK1),k2_mcart_1(sK2)) | spl4_8),
% 0.20/0.47    inference(resolution,[],[f196,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f24])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    ~sQ3_eqProxy(k2_mcart_1(sK2),k2_mcart_1(sK1)) | spl4_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f194])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    spl4_8 <=> sQ3_eqProxy(k2_mcart_1(sK2),k2_mcart_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    spl4_7),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f207])).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    $false | spl4_7),
% 0.20/0.47    inference(subsumption_resolution,[],[f205,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    sQ3_eqProxy(k1_mcart_1(sK1),k1_mcart_1(sK2))),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f19,f24])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    k1_mcart_1(sK1) = k1_mcart_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    ~sQ3_eqProxy(k1_mcart_1(sK1),k1_mcart_1(sK2)) | spl4_7),
% 0.20/0.47    inference(resolution,[],[f192,f37])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    ~sQ3_eqProxy(k1_mcart_1(sK2),k1_mcart_1(sK1)) | spl4_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f190])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    spl4_7 <=> sQ3_eqProxy(k1_mcart_1(sK2),k1_mcart_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    ~spl4_7 | ~spl4_8 | spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f182,f178,f194,f190])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    spl4_5 <=> sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    ~sQ3_eqProxy(k2_mcart_1(sK2),k2_mcart_1(sK1)) | ~sQ3_eqProxy(k1_mcart_1(sK2),k1_mcart_1(sK1)) | spl4_5),
% 0.20/0.47    inference(resolution,[],[f180,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (sQ3_eqProxy(k4_tarski(X0,X2),k4_tarski(X1,X3)) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f24])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    ~sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1))) | spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f178])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    spl4_1 | spl4_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f104,f186,f74])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ( ! [X10,X11,X9] : (~sQ3_eqProxy(X9,X10) | ~sQ3_eqProxy(X9,sK1) | ~sQ3_eqProxy(X10,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))) | ~r2_hidden(sK2,X11) | ~v1_relat_1(X11)) )),
% 0.20/0.47    inference(resolution,[],[f60,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (sQ3_eqProxy(k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)),X0) | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f22,f24])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X2,X3,X1] : (~sQ3_eqProxy(X3,sK2) | ~sQ3_eqProxy(X1,X2) | ~sQ3_eqProxy(X1,sK1) | ~sQ3_eqProxy(X2,X3)) )),
% 0.20/0.47    inference(resolution,[],[f50,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (sQ3_eqProxy(X0,X2) | ~sQ3_eqProxy(X1,X2) | ~sQ3_eqProxy(X0,X1)) )),
% 0.20/0.47    inference(equality_proxy_axiom,[],[f24])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~sQ3_eqProxy(X1,sK2) | ~sQ3_eqProxy(X0,sK1) | ~sQ3_eqProxy(X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f45,f38])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X2] : (~sQ3_eqProxy(X2,sK2) | ~sQ3_eqProxy(X2,sK1)) )),
% 0.20/0.47    inference(resolution,[],[f41,f37])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0] : (~sQ3_eqProxy(sK1,X0) | ~sQ3_eqProxy(X0,sK2)) )),
% 0.20/0.47    inference(resolution,[],[f38,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ~sQ3_eqProxy(sK1,sK2)),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f21,f24])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    sK1 != sK2),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    spl4_3 | ~spl4_5 | spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f91,f77,f178,f133])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    spl4_3 <=> ! [X7] : (~r2_hidden(sK1,X7) | ~v1_relat_1(X7))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    ( ! [X3] : (~sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1))) | ~r2_hidden(sK1,X3) | ~v1_relat_1(X3)) ) | spl4_2),
% 0.20/0.47    inference(resolution,[],[f81,f28])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X0] : (~sQ3_eqProxy(X0,sK1) | ~sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),X0)) ) | spl4_2),
% 0.20/0.47    inference(resolution,[],[f79,f38])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ~sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),sK1) | spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f77])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    ~spl4_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f146])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    $false | ~spl4_3),
% 0.20/0.47    inference(subsumption_resolution,[],[f145,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    m1_subset_1(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,sK0) | ~spl4_3),
% 0.20/0.47    inference(subsumption_resolution,[],[f143,f15])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    v1_xboole_0(sK0) | ~m1_subset_1(sK1,sK0) | ~spl4_3),
% 0.20/0.47    inference(resolution,[],[f139,f23])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ~r2_hidden(sK1,sK0) | ~spl4_3),
% 0.20/0.47    inference(resolution,[],[f134,f16])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ( ! [X7] : (~v1_relat_1(X7) | ~r2_hidden(sK1,X7)) ) | ~spl4_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f133])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (31236)------------------------------
% 0.20/0.47  % (31236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (31236)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (31236)Memory used [KB]: 6268
% 0.20/0.47  % (31236)Time elapsed: 0.019 s
% 0.20/0.47  % (31236)------------------------------
% 0.20/0.47  % (31236)------------------------------
% 0.20/0.47  % (31229)Success in time 0.116 s
%------------------------------------------------------------------------------

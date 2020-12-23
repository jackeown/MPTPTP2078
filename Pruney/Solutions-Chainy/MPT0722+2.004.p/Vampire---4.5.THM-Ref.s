%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 142 expanded)
%              Number of leaves         :   18 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  241 ( 495 expanded)
%              Number of equality atoms :   32 (  73 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f60,f66,f72,f78,f87,f101,f121])).

fof(f121,plain,
    ( ~ spl2_10
    | spl2_1
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f120,f83,f75,f69,f63,f37,f97])).

fof(f97,plain,
    ( spl2_10
  <=> sK1 = k10_relat_1(sK0,k9_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f37,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f63,plain,
    ( spl2_6
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f69,plain,
    ( spl2_7
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f75,plain,
    ( spl2_8
  <=> v2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f83,plain,
    ( spl2_9
  <=> sK0 = k2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f120,plain,
    ( sK1 != k10_relat_1(sK0,k9_relat_1(sK0,sK1))
    | spl2_1
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(superposition,[],[f39,f107])).

fof(f107,plain,
    ( ! [X0] : k9_relat_1(k2_funct_1(sK0),X0) = k10_relat_1(sK0,X0)
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f102,f85])).

fof(f85,plain,
    ( sK0 = k2_funct_1(k2_funct_1(sK0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f102,plain,
    ( ! [X0] : k9_relat_1(k2_funct_1(sK0),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK0)),X0)
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f65,f71,f77,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f77,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f71,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f65,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f39,plain,
    ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f101,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_10
    | ~ spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f95,f42,f47,f97,f52,f57])).

fof(f57,plain,
    ( spl2_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f52,plain,
    ( spl2_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f47,plain,
    ( spl2_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f42,plain,
    ( spl2_2
  <=> r1_tarski(sK1,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f95,plain,
    ( ~ v2_funct_1(sK0)
    | sK1 = k10_relat_1(sK0,k9_relat_1(sK0,sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f28,f44])).

fof(f44,plain,
    ( r1_tarski(sK1,k1_relat_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f87,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_9
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f80,f47,f83,f52,f57])).

fof(f80,plain,
    ( sK0 = k2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f30,f49])).

fof(f49,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f78,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f73,f57,f52,f47,f75])).

fof(f73,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f59,f54,f49,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f54,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f59,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f72,plain,
    ( spl2_7
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f67,f57,f52,f69])).

fof(f67,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f59,f54,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f66,plain,
    ( spl2_6
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f61,f57,f52,f63])).

fof(f61,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f59,f54,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
    & r1_tarski(sK1,k1_relat_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
            & r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(sK0))
          & v2_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
        & r1_tarski(X1,k1_relat_1(sK0))
        & v2_funct_1(sK0) )
   => ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
      & r1_tarski(sK1,k1_relat_1(sK0))
      & v2_funct_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( r1_tarski(X1,k1_relat_1(X0))
              & v2_funct_1(X0) )
           => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

fof(f55,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f25,f47])).

fof(f25,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f42])).

fof(f26,plain,(
    r1_tarski(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f27,f37])).

fof(f27,plain,(
    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:02:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.47  % (5162)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.47  % (5162)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (5170)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f60,f66,f72,f78,f87,f101,f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ~spl2_10 | spl2_1 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f120,f83,f75,f69,f63,f37,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl2_10 <=> sK1 = k10_relat_1(sK0,k9_relat_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl2_1 <=> sK1 = k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl2_6 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl2_7 <=> v1_funct_1(k2_funct_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl2_8 <=> v2_funct_1(k2_funct_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl2_9 <=> sK0 = k2_funct_1(k2_funct_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    sK1 != k10_relat_1(sK0,k9_relat_1(sK0,sK1)) | (spl2_1 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_9)),
% 0.21/0.48    inference(superposition,[],[f39,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0] : (k9_relat_1(k2_funct_1(sK0),X0) = k10_relat_1(sK0,X0)) ) | (~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f102,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    sK0 = k2_funct_1(k2_funct_1(sK0)) | ~spl2_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X0] : (k9_relat_1(k2_funct_1(sK0),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK0)),X0)) ) | (~spl2_6 | ~spl2_7 | ~spl2_8)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f65,f71,f77,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    v2_funct_1(k2_funct_1(sK0)) | ~spl2_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_1(sK0)) | ~spl2_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    v1_relat_1(k2_funct_1(sK0)) | ~spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) | spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f37])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ~spl2_5 | ~spl2_4 | spl2_10 | ~spl2_3 | ~spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f95,f42,f47,f97,f52,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl2_5 <=> v1_relat_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl2_4 <=> v1_funct_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl2_3 <=> v2_funct_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl2_2 <=> r1_tarski(sK1,k1_relat_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ~v2_funct_1(sK0) | sK1 = k10_relat_1(sK0,k9_relat_1(sK0,sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_2),
% 0.21/0.48    inference(resolution,[],[f28,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    r1_tarski(sK1,k1_relat_1(sK0)) | ~spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f42])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ~spl2_5 | ~spl2_4 | spl2_9 | ~spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f80,f47,f83,f52,f57])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    sK0 = k2_funct_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_3),
% 0.21/0.48    inference(resolution,[],[f30,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    v2_funct_1(sK0) | ~spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f47])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl2_8 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f73,f57,f52,f47,f75])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    v2_funct_1(k2_funct_1(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f59,f54,f49,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    v1_funct_1(sK0) | ~spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    v1_relat_1(sK0) | ~spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl2_7 | ~spl2_4 | ~spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f67,f57,f52,f69])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_1(sK0)) | (~spl2_4 | ~spl2_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f59,f54,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl2_6 | ~spl2_4 | ~spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f61,f57,f52,f63])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    v1_relat_1(k2_funct_1(sK0)) | (~spl2_4 | ~spl2_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f59,f54,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f57])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    (sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) & r1_tarski(sK1,k1_relat_1(sK0)) & v2_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f21,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1 & r1_tarski(X1,k1_relat_1(sK0)) & v2_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X1] : (k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1 & r1_tarski(X1,k1_relat_1(sK0)) & v2_funct_1(sK0)) => (sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) & r1_tarski(sK1,k1_relat_1(sK0)) & v2_funct_1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & (r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f52])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v1_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f47])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    v2_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f42])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    r1_tarski(sK1,k1_relat_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ~spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f37])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (5162)------------------------------
% 0.21/0.48  % (5162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5162)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (5162)Memory used [KB]: 10618
% 0.21/0.48  % (5162)Time elapsed: 0.064 s
% 0.21/0.48  % (5162)------------------------------
% 0.21/0.48  % (5162)------------------------------
% 0.21/0.48  % (5155)Success in time 0.127 s
%------------------------------------------------------------------------------

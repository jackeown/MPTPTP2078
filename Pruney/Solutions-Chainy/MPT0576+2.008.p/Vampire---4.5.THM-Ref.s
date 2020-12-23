%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 223 expanded)
%              Number of leaves         :   21 (  94 expanded)
%              Depth                    :    7
%              Number of atoms          :  224 ( 682 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f49,f56,f61,f69,f74,f82,f87,f92,f100,f105,f110,f119,f120])).

fof(f120,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f55,f28,f64,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f64,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK3,X0))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f48,f43,f38,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

fof(f38,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f43,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f48,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f28,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl4_1
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f55,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_6
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f119,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f28,f60,f64,f24])).

fof(f60,plain,
    ( r1_tarski(k10_relat_1(sK3,sK0),k10_relat_1(sK3,sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_7
  <=> r1_tarski(k10_relat_1(sK3,sK0),k10_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f110,plain,
    ( ~ spl4_15
    | spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f93,f58,f26,f107])).

fof(f107,plain,
    ( spl4_15
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f93,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK0))
    | spl4_1
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f28,f60,f24])).

fof(f105,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f94,f58,f41,f102])).

fof(f102,plain,
    ( spl4_14
  <=> r1_tarski(k10_relat_1(sK3,k10_relat_1(sK3,sK0)),k10_relat_1(sK3,k10_relat_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f94,plain,
    ( r1_tarski(k10_relat_1(sK3,k10_relat_1(sK3,sK0)),k10_relat_1(sK3,k10_relat_1(sK3,sK1)))
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f43,f60,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f100,plain,
    ( spl4_13
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f95,f58,f46,f97])).

fof(f97,plain,
    ( spl4_13
  <=> r1_tarski(k10_relat_1(sK2,k10_relat_1(sK3,sK0)),k10_relat_1(sK2,k10_relat_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f95,plain,
    ( r1_tarski(k10_relat_1(sK2,k10_relat_1(sK3,sK0)),k10_relat_1(sK2,k10_relat_1(sK3,sK1)))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f48,f60,f23])).

fof(f92,plain,
    ( ~ spl4_12
    | spl4_1
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f75,f53,f26,f89])).

fof(f89,plain,
    ( spl4_12
  <=> r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f75,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK3,sK1))
    | spl4_1
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f28,f55,f24])).

% (6571)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
fof(f87,plain,
    ( spl4_11
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f76,f53,f41,f84])).

fof(f84,plain,
    ( spl4_11
  <=> r1_tarski(k10_relat_1(sK3,k10_relat_1(sK2,sK0)),k10_relat_1(sK3,k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f76,plain,
    ( r1_tarski(k10_relat_1(sK3,k10_relat_1(sK2,sK0)),k10_relat_1(sK3,k10_relat_1(sK2,sK1)))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f43,f55,f23])).

fof(f82,plain,
    ( spl4_10
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f77,f53,f46,f79])).

fof(f79,plain,
    ( spl4_10
  <=> r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f77,plain,
    ( r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k10_relat_1(sK2,sK1)))
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f48,f55,f23])).

fof(f74,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f62,f41,f36,f71])).

fof(f71,plain,
    ( spl4_9
  <=> r1_tarski(k10_relat_1(sK3,sK2),k10_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f62,plain,
    ( r1_tarski(k10_relat_1(sK3,sK2),k10_relat_1(sK3,sK3))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f43,f38,f23])).

fof(f69,plain,
    ( spl4_8
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f63,f46,f36,f66])).

fof(f66,plain,
    ( spl4_8
  <=> r1_tarski(k10_relat_1(sK2,sK2),k10_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f63,plain,
    ( r1_tarski(k10_relat_1(sK2,sK2),k10_relat_1(sK2,sK3))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f48,f38,f23])).

fof(f61,plain,
    ( spl4_7
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f50,f41,f31,f58])).

fof(f31,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f50,plain,
    ( r1_tarski(k10_relat_1(sK3,sK0),k10_relat_1(sK3,sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f43,f33,f23])).

fof(f33,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f56,plain,
    ( spl4_6
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f51,f46,f31,f53])).

fof(f51,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f48,f33,f23])).

fof(f49,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f17,f46])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t180_relat_1)).

fof(f44,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f20,f31])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f26])).

fof(f21,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:13:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.40  % (6579)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.47  % (6580)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.47  % (6579)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f49,f56,f61,f69,f74,f82,f87,f92,f100,f105,f110,f119,f120])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    $false | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f55,f28,f64,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK3,X0))) ) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f48,f43,f38,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    r1_tarski(sK2,sK3) | ~spl4_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    spl4_3 <=> r1_tarski(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    v1_relat_1(sK3) | ~spl4_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    spl4_4 <=> v1_relat_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    v1_relat_1(sK2) | ~spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    spl4_5 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) | spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    spl4_1 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl4_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl4_6 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    $false | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f60,f64,f24])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    r1_tarski(k10_relat_1(sK3,sK0),k10_relat_1(sK3,sK1)) | ~spl4_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl4_7 <=> r1_tarski(k10_relat_1(sK3,sK0),k10_relat_1(sK3,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ~spl4_15 | spl4_1 | ~spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f93,f58,f26,f107])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    spl4_15 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK0)) | (spl4_1 | ~spl4_7)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f60,f24])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    spl4_14 | ~spl4_4 | ~spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f94,f58,f41,f102])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    spl4_14 <=> r1_tarski(k10_relat_1(sK3,k10_relat_1(sK3,sK0)),k10_relat_1(sK3,k10_relat_1(sK3,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    r1_tarski(k10_relat_1(sK3,k10_relat_1(sK3,sK0)),k10_relat_1(sK3,k10_relat_1(sK3,sK1))) | (~spl4_4 | ~spl4_7)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f43,f60,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    spl4_13 | ~spl4_5 | ~spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f95,f58,f46,f97])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl4_13 <=> r1_tarski(k10_relat_1(sK2,k10_relat_1(sK3,sK0)),k10_relat_1(sK2,k10_relat_1(sK3,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    r1_tarski(k10_relat_1(sK2,k10_relat_1(sK3,sK0)),k10_relat_1(sK2,k10_relat_1(sK3,sK1))) | (~spl4_5 | ~spl4_7)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f48,f60,f23])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ~spl4_12 | spl4_1 | ~spl4_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f75,f53,f26,f89])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl4_12 <=> r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK3,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ~r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK3,sK1)) | (spl4_1 | ~spl4_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f28,f55,f24])).
% 0.20/0.47  % (6571)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl4_11 | ~spl4_4 | ~spl4_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f76,f53,f41,f84])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl4_11 <=> r1_tarski(k10_relat_1(sK3,k10_relat_1(sK2,sK0)),k10_relat_1(sK3,k10_relat_1(sK2,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    r1_tarski(k10_relat_1(sK3,k10_relat_1(sK2,sK0)),k10_relat_1(sK3,k10_relat_1(sK2,sK1))) | (~spl4_4 | ~spl4_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f43,f55,f23])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl4_10 | ~spl4_5 | ~spl4_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f77,f53,f46,f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl4_10 <=> r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k10_relat_1(sK2,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k10_relat_1(sK2,sK1))) | (~spl4_5 | ~spl4_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f48,f55,f23])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl4_9 | ~spl4_3 | ~spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f62,f41,f36,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl4_9 <=> r1_tarski(k10_relat_1(sK3,sK2),k10_relat_1(sK3,sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    r1_tarski(k10_relat_1(sK3,sK2),k10_relat_1(sK3,sK3)) | (~spl4_3 | ~spl4_4)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f43,f38,f23])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl4_8 | ~spl4_3 | ~spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f63,f46,f36,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl4_8 <=> r1_tarski(k10_relat_1(sK2,sK2),k10_relat_1(sK2,sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    r1_tarski(k10_relat_1(sK2,sK2),k10_relat_1(sK2,sK3)) | (~spl4_3 | ~spl4_5)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f48,f38,f23])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl4_7 | ~spl4_2 | ~spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f50,f41,f31,f58])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    spl4_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    r1_tarski(k10_relat_1(sK3,sK0),k10_relat_1(sK3,sK1)) | (~spl4_2 | ~spl4_4)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f43,f33,f23])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1) | ~spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f31])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl4_6 | ~spl4_2 | ~spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f51,f46,f31,f53])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | (~spl4_2 | ~spl4_5)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f48,f33,f23])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f46])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X3] : (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f4])).
% 0.20/0.47  fof(f4,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t180_relat_1)).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f41])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    v1_relat_1(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl4_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f36])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    r1_tarski(sK2,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f31])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ~spl4_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f26])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (6579)------------------------------
% 0.20/0.47  % (6579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (6579)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (6579)Memory used [KB]: 5373
% 0.20/0.47  % (6579)Time elapsed: 0.069 s
% 0.20/0.47  % (6579)------------------------------
% 0.20/0.47  % (6579)------------------------------
% 0.20/0.47  % (6565)Success in time 0.125 s
%------------------------------------------------------------------------------

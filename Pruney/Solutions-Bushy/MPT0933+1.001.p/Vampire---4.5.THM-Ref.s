%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0933+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:56 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   44 (  80 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 274 expanded)
%              Number of equality atoms :   33 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f24,f29,f34,f40,f45,f54,f57])).

fof(f57,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f55,f33])).

fof(f33,plain,
    ( sK0 != sK2
    | spl3_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f55,plain,
    ( sK0 = sK2
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f49,f53])).

fof(f53,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_7
  <=> sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f49,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f48,f39])).

fof(f39,plain,
    ( k1_mcart_1(sK0) = k1_mcart_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_5
  <=> k1_mcart_1(sK0) = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f48,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f46,f44])).

fof(f44,plain,
    ( k2_mcart_1(sK0) = k2_mcart_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_6
  <=> k2_mcart_1(sK0) = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f46,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl3_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f35,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 )
    | ~ spl3_1 ),
    inference(resolution,[],[f18,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f18,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

% (6351)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f54,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f47,f26,f16,f51])).

fof(f26,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f47,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f26])).

fof(f45,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f11,f42])).

fof(f11,plain,(
    k2_mcart_1(sK0) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
              & k1_mcart_1(X0) = k1_mcart_1(X2)
              & r2_hidden(X0,X1)
              & r2_hidden(X2,X1) )
           => X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
         => X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_mcart_1)).

fof(f40,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f10,f37])).

fof(f10,plain,(
    k1_mcart_1(sK0) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f34,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f12,f31])).

fof(f12,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f5])).

fof(f29,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f9,f26])).

fof(f9,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f24,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f8,f21])).

fof(f8,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f19,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f16])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------

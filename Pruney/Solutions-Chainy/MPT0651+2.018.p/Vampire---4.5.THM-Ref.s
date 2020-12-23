%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 172 expanded)
%              Number of leaves         :   23 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :  284 ( 507 expanded)
%              Number of equality atoms :   63 ( 140 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f353,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f71,f89,f101,f119,f139,f165,f170,f240,f246,f270,f352])).

fof(f352,plain,
    ( ~ spl1_21
    | spl1_31
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f342,f86,f267,f167])).

fof(f167,plain,
    ( spl1_21
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f267,plain,
    ( spl1_31
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).

fof(f86,plain,
    ( spl1_9
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f342,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_9 ),
    inference(superposition,[],[f109,f88])).

fof(f88,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f109,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f41,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f270,plain,
    ( ~ spl1_21
    | ~ spl1_5
    | ~ spl1_31
    | ~ spl1_9
    | ~ spl1_11
    | spl1_28 ),
    inference(avatar_split_clause,[],[f265,f243,f98,f86,f267,f62,f167])).

fof(f62,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f98,plain,
    ( spl1_11
  <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f243,plain,
    ( spl1_28
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f265,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_9
    | ~ spl1_11
    | spl1_28 ),
    inference(forward_demodulation,[],[f264,f88])).

fof(f264,plain,
    ( ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_11
    | spl1_28 ),
    inference(trivial_inequality_removal,[],[f263])).

fof(f263,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_11
    | spl1_28 ),
    inference(forward_demodulation,[],[f261,f100])).

fof(f100,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f98])).

fof(f261,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_28 ),
    inference(superposition,[],[f245,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f245,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_28 ),
    inference(avatar_component_clause,[],[f243])).

fof(f246,plain,
    ( ~ spl1_28
    | spl1_2
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f241,f135,f47,f243])).

fof(f47,plain,
    ( spl1_2
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f135,plain,
    ( spl1_16
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f241,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_2
    | ~ spl1_16 ),
    inference(forward_demodulation,[],[f49,f137])).

fof(f137,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f49,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f240,plain,
    ( ~ spl1_5
    | ~ spl1_21
    | ~ spl1_9
    | ~ spl1_13
    | spl1_20 ),
    inference(avatar_split_clause,[],[f239,f162,f116,f86,f167,f62])).

fof(f116,plain,
    ( spl1_13
  <=> k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f162,plain,
    ( spl1_20
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f239,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_9
    | ~ spl1_13
    | spl1_20 ),
    inference(trivial_inequality_removal,[],[f238])).

fof(f238,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_9
    | ~ spl1_13
    | spl1_20 ),
    inference(forward_demodulation,[],[f237,f118])).

fof(f118,plain,
    ( k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f237,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_9
    | spl1_20 ),
    inference(forward_demodulation,[],[f215,f88])).

fof(f215,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_20 ),
    inference(superposition,[],[f164,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f164,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_20 ),
    inference(avatar_component_clause,[],[f162])).

fof(f170,plain,
    ( spl1_21
    | ~ spl1_6
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f153,f135,f68,f167])).

fof(f68,plain,
    ( spl1_6
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f153,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_6
    | ~ spl1_16 ),
    inference(backward_demodulation,[],[f70,f137])).

fof(f70,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f165,plain,
    ( ~ spl1_20
    | spl1_1
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f152,f135,f43,f162])).

fof(f43,plain,
    ( spl1_1
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f152,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_1
    | ~ spl1_16 ),
    inference(backward_demodulation,[],[f45,f137])).

fof(f45,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f139,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_16
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f133,f52,f135,f57,f62])).

fof(f57,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f52,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f133,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f37,f54])).

fof(f54,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f119,plain,
    ( spl1_13
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f105,f62,f116])).

% (14252)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
fof(f105,plain,
    ( k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f64,f36])).

fof(f64,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f101,plain,
    ( spl1_11
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f90,f62,f98])).

fof(f90,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f64,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f89,plain,
    ( spl1_9
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f78,f62,f86])).

fof(f78,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f64,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,
    ( spl1_6
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f66,f62,f57,f68])).

fof(f66,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f64,f59,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f59,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f65,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f60,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f30,f47,f43])).

fof(f30,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:03:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (14233)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.54  % (14238)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.54  % (14239)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.54  % (14236)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.54  % (14249)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.54  % (14236)Refutation not found, incomplete strategy% (14236)------------------------------
% 0.21/0.54  % (14236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14236)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14236)Memory used [KB]: 10490
% 0.21/0.54  % (14236)Time elapsed: 0.106 s
% 0.21/0.54  % (14236)------------------------------
% 0.21/0.54  % (14236)------------------------------
% 0.21/0.54  % (14234)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.55  % (14254)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.55  % (14235)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.55  % (14237)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.55  % (14256)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.55  % (14246)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.56  % (14248)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.56  % (14244)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.56  % (14256)Refutation not found, incomplete strategy% (14256)------------------------------
% 0.21/0.56  % (14256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (14256)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (14256)Memory used [KB]: 10618
% 0.21/0.56  % (14256)Time elapsed: 0.074 s
% 0.21/0.56  % (14256)------------------------------
% 0.21/0.56  % (14256)------------------------------
% 0.21/0.56  % (14250)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.56  % (14251)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.56  % (14239)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f353,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f71,f89,f101,f119,f139,f165,f170,f240,f246,f270,f352])).
% 0.21/0.56  fof(f352,plain,(
% 0.21/0.56    ~spl1_21 | spl1_31 | ~spl1_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f342,f86,f267,f167])).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    spl1_21 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.21/0.56  fof(f267,plain,(
% 0.21/0.56    spl1_31 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    spl1_9 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.56  fof(f342,plain,(
% 0.21/0.56    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | ~spl1_9),
% 0.21/0.56    inference(superposition,[],[f109,f88])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f86])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f108])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(superposition,[],[f41,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.56  fof(f270,plain,(
% 0.21/0.56    ~spl1_21 | ~spl1_5 | ~spl1_31 | ~spl1_9 | ~spl1_11 | spl1_28),
% 0.21/0.56    inference(avatar_split_clause,[],[f265,f243,f98,f86,f267,f62,f167])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    spl1_5 <=> v1_relat_1(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    spl1_11 <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.56  fof(f243,plain,(
% 0.21/0.56    spl1_28 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).
% 0.21/0.56  fof(f265,plain,(
% 0.21/0.56    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_9 | ~spl1_11 | spl1_28)),
% 0.21/0.56    inference(forward_demodulation,[],[f264,f88])).
% 0.21/0.56  fof(f264,plain,(
% 0.21/0.56    ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_11 | spl1_28)),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f263])).
% 0.21/0.56  fof(f263,plain,(
% 0.21/0.56    k1_relat_1(sK0) != k1_relat_1(sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_11 | spl1_28)),
% 0.21/0.56    inference(forward_demodulation,[],[f261,f100])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_11),
% 0.21/0.56    inference(avatar_component_clause,[],[f98])).
% 0.21/0.56  fof(f261,plain,(
% 0.21/0.56    k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | spl1_28),
% 0.21/0.56    inference(superposition,[],[f245,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 0.21/0.56  fof(f245,plain,(
% 0.21/0.56    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | spl1_28),
% 0.21/0.56    inference(avatar_component_clause,[],[f243])).
% 0.21/0.56  fof(f246,plain,(
% 0.21/0.56    ~spl1_28 | spl1_2 | ~spl1_16),
% 0.21/0.56    inference(avatar_split_clause,[],[f241,f135,f47,f243])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    spl1_2 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.56  fof(f135,plain,(
% 0.21/0.56    spl1_16 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.21/0.56  fof(f241,plain,(
% 0.21/0.56    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (spl1_2 | ~spl1_16)),
% 0.21/0.56    inference(forward_demodulation,[],[f49,f137])).
% 0.21/0.56  fof(f137,plain,(
% 0.21/0.56    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_16),
% 0.21/0.56    inference(avatar_component_clause,[],[f135])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f47])).
% 0.21/0.56  fof(f240,plain,(
% 0.21/0.56    ~spl1_5 | ~spl1_21 | ~spl1_9 | ~spl1_13 | spl1_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f239,f162,f116,f86,f167,f62])).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    spl1_13 <=> k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.21/0.56  fof(f162,plain,(
% 0.21/0.56    spl1_20 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.21/0.56  fof(f239,plain,(
% 0.21/0.56    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_9 | ~spl1_13 | spl1_20)),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f238])).
% 0.21/0.56  fof(f238,plain,(
% 0.21/0.56    k1_relat_1(sK0) != k1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_9 | ~spl1_13 | spl1_20)),
% 0.21/0.56    inference(forward_demodulation,[],[f237,f118])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) | ~spl1_13),
% 0.21/0.56    inference(avatar_component_clause,[],[f116])).
% 0.21/0.56  fof(f237,plain,(
% 0.21/0.56    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_9 | spl1_20)),
% 0.21/0.56    inference(forward_demodulation,[],[f215,f88])).
% 0.21/0.56  fof(f215,plain,(
% 0.21/0.56    k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | spl1_20),
% 0.21/0.56    inference(superposition,[],[f164,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.56  fof(f164,plain,(
% 0.21/0.56    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | spl1_20),
% 0.21/0.56    inference(avatar_component_clause,[],[f162])).
% 0.21/0.56  fof(f170,plain,(
% 0.21/0.56    spl1_21 | ~spl1_6 | ~spl1_16),
% 0.21/0.56    inference(avatar_split_clause,[],[f153,f135,f68,f167])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    spl1_6 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.56  fof(f153,plain,(
% 0.21/0.56    v1_relat_1(k4_relat_1(sK0)) | (~spl1_6 | ~spl1_16)),
% 0.21/0.56    inference(backward_demodulation,[],[f70,f137])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    v1_relat_1(k2_funct_1(sK0)) | ~spl1_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f68])).
% 0.21/0.56  fof(f165,plain,(
% 0.21/0.56    ~spl1_20 | spl1_1 | ~spl1_16),
% 0.21/0.56    inference(avatar_split_clause,[],[f152,f135,f43,f162])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    spl1_1 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.56  fof(f152,plain,(
% 0.21/0.56    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (spl1_1 | ~spl1_16)),
% 0.21/0.56    inference(backward_demodulation,[],[f45,f137])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f43])).
% 0.21/0.56  fof(f139,plain,(
% 0.21/0.56    ~spl1_5 | ~spl1_4 | spl1_16 | ~spl1_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f133,f52,f135,f57,f62])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    spl1_4 <=> v1_funct_1(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    spl1_3 <=> v2_funct_1(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.56  fof(f133,plain,(
% 0.21/0.56    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.21/0.56    inference(resolution,[],[f37,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    v2_funct_1(sK0) | ~spl1_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f52])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    spl1_13 | ~spl1_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f105,f62,f116])).
% 0.21/0.56  % (14252)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) | ~spl1_5),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f64,f36])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    v1_relat_1(sK0) | ~spl1_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f62])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    spl1_11 | ~spl1_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f90,f62,f98])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f64,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    spl1_9 | ~spl1_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f78,f62,f86])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f64,f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    spl1_6 | ~spl1_4 | ~spl1_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f66,f62,f57,f68])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    v1_relat_1(k2_funct_1(sK0)) | (~spl1_4 | ~spl1_5)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f64,f59,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    v1_funct_1(sK0) | ~spl1_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f57])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    spl1_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f27,f62])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    v1_relat_1(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,negated_conjecture,(
% 0.21/0.56    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.56    inference(negated_conjecture,[],[f9])).
% 0.21/0.56  fof(f9,conjecture,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    spl1_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f28,f57])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    v1_funct_1(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    spl1_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f29,f52])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    v2_funct_1(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ~spl1_1 | ~spl1_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f30,f47,f43])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (14239)------------------------------
% 0.21/0.56  % (14239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (14239)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (14239)Memory used [KB]: 10874
% 0.21/0.56  % (14239)Time elapsed: 0.141 s
% 0.21/0.56  % (14239)------------------------------
% 0.21/0.56  % (14239)------------------------------
% 0.21/0.56  % (14232)Success in time 0.203 s
%------------------------------------------------------------------------------

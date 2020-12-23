%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:58 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 161 expanded)
%              Number of leaves         :   27 (  77 expanded)
%              Depth                    :    6
%              Number of atoms          :  285 ( 469 expanded)
%              Number of equality atoms :   63 ( 103 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f52,f56,f60,f64,f68,f81,f100,f106,f117,f146,f166,f192,f211,f254,f267])).

fof(f267,plain,
    ( spl2_1
    | ~ spl2_11
    | ~ spl2_23
    | ~ spl2_43 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl2_1
    | ~ spl2_11
    | ~ spl2_23
    | ~ spl2_43 ),
    inference(subsumption_resolution,[],[f265,f33])).

fof(f33,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_1
  <=> k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f265,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))
    | ~ spl2_11
    | ~ spl2_23
    | ~ spl2_43 ),
    inference(forward_demodulation,[],[f264,f80])).

fof(f80,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_11
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f264,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k9_relat_1(sK0,k1_relat_1(sK0)))
    | ~ spl2_23
    | ~ spl2_43 ),
    inference(superposition,[],[f253,f145])).

fof(f145,plain,
    ( k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl2_23
  <=> k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f253,plain,
    ( ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl2_43
  <=> ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f254,plain,
    ( spl2_43
    | ~ spl2_2
    | ~ spl2_32
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f250,f209,f190,f36,f252])).

fof(f36,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f190,plain,
    ( spl2_32
  <=> ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f209,plain,
    ( spl2_36
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,X2),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f250,plain,
    ( ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0))
    | ~ spl2_2
    | ~ spl2_32
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f247,f191])).

fof(f191,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f190])).

fof(f247,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0))
    | ~ spl2_2
    | ~ spl2_36 ),
    inference(resolution,[],[f210,f38])).

fof(f38,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f210,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,X2),X3)) )
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f209])).

fof(f211,plain,
    ( spl2_36
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f202,f98,f41,f209])).

fof(f41,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f98,plain,
    ( spl2_15
  <=> ! [X3,X2,X4] :
        ( k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f202,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,X2),X3)) )
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(resolution,[],[f99,f43])).

fof(f43,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f99,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f98])).

fof(f192,plain,
    ( spl2_32
    | ~ spl2_2
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f186,f164,f36,f190])).

fof(f164,plain,
    ( spl2_27
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f186,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))
    | ~ spl2_2
    | ~ spl2_27 ),
    inference(resolution,[],[f165,f38])).

fof(f165,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f164])).

fof(f166,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f157,f62,f41,f164])).

fof(f62,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f157,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)) )
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f63,f43])).

fof(f63,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f146,plain,
    ( spl2_23
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f139,f115,f36,f143])).

fof(f115,plain,
    ( spl2_18
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(sK0,X1) = k7_relat_1(k5_relat_1(sK0,X1),k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f139,plain,
    ( k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0))
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(resolution,[],[f116,f38])).

fof(f116,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(sK0,X1) = k7_relat_1(k5_relat_1(sK0,X1),k1_relat_1(sK0)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f108,f104,f41,f115])).

fof(f104,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( k5_relat_1(X0,X1) = k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f108,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(sK0,X1) = k7_relat_1(k5_relat_1(sK0,X1),k1_relat_1(sK0)) )
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(resolution,[],[f105,f43])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(X0,X1) = k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0)) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,
    ( spl2_16
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f102,f66,f58,f50,f104])).

fof(f50,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f58,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f66,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(X0,X1) = k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f101,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(X0,X1) = k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0))
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(resolution,[],[f59,f51])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f100,plain,
    ( spl2_15
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f88,f66,f54,f98])).

fof(f54,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f88,plain,
    ( ! [X4,X2,X3] :
        ( k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(resolution,[],[f55,f67])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f81,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f70,f46,f41,f78])).

fof(f46,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f70,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f47,f43])).

fof(f47,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f68,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f64,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(f60,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f56,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f48,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
        & v1_relat_1(X1) )
   => ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f39,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f31])).

fof(f23,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.39  % (14082)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.13/0.39  % (14082)Refutation found. Thanks to Tanya!
% 0.13/0.39  % SZS status Theorem for theBenchmark
% 0.13/0.39  % SZS output start Proof for theBenchmark
% 0.13/0.39  fof(f268,plain,(
% 0.13/0.39    $false),
% 0.13/0.39    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f52,f56,f60,f64,f68,f81,f100,f106,f117,f146,f166,f192,f211,f254,f267])).
% 0.13/0.39  fof(f267,plain,(
% 0.13/0.39    spl2_1 | ~spl2_11 | ~spl2_23 | ~spl2_43),
% 0.13/0.39    inference(avatar_contradiction_clause,[],[f266])).
% 0.13/0.39  fof(f266,plain,(
% 0.13/0.39    $false | (spl2_1 | ~spl2_11 | ~spl2_23 | ~spl2_43)),
% 0.13/0.39    inference(subsumption_resolution,[],[f265,f33])).
% 0.13/0.39  fof(f33,plain,(
% 0.13/0.39    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) | spl2_1),
% 0.13/0.39    inference(avatar_component_clause,[],[f31])).
% 0.13/0.39  fof(f31,plain,(
% 0.13/0.39    spl2_1 <=> k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.13/0.39  fof(f265,plain,(
% 0.13/0.39    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) | (~spl2_11 | ~spl2_23 | ~spl2_43)),
% 0.13/0.39    inference(forward_demodulation,[],[f264,f80])).
% 0.13/0.39  fof(f80,plain,(
% 0.13/0.39    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl2_11),
% 0.13/0.39    inference(avatar_component_clause,[],[f78])).
% 0.13/0.39  fof(f78,plain,(
% 0.13/0.39    spl2_11 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.13/0.39  fof(f264,plain,(
% 0.13/0.39    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k9_relat_1(sK0,k1_relat_1(sK0))) | (~spl2_23 | ~spl2_43)),
% 0.13/0.39    inference(superposition,[],[f253,f145])).
% 0.13/0.39  fof(f145,plain,(
% 0.13/0.39    k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0)) | ~spl2_23),
% 0.13/0.39    inference(avatar_component_clause,[],[f143])).
% 0.13/0.39  fof(f143,plain,(
% 0.13/0.39    spl2_23 <=> k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.13/0.39  fof(f253,plain,(
% 0.13/0.39    ( ! [X0] : (k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0))) ) | ~spl2_43),
% 0.13/0.39    inference(avatar_component_clause,[],[f252])).
% 0.13/0.39  fof(f252,plain,(
% 0.13/0.39    spl2_43 <=> ! [X0] : k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.13/0.39  fof(f254,plain,(
% 0.13/0.39    spl2_43 | ~spl2_2 | ~spl2_32 | ~spl2_36),
% 0.13/0.39    inference(avatar_split_clause,[],[f250,f209,f190,f36,f252])).
% 0.13/0.39  fof(f36,plain,(
% 0.13/0.39    spl2_2 <=> v1_relat_1(sK1)),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.13/0.39  fof(f190,plain,(
% 0.13/0.39    spl2_32 <=> ! [X0] : k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.13/0.39  fof(f209,plain,(
% 0.13/0.39    spl2_36 <=> ! [X3,X2] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,X2),X3)))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.13/0.39  fof(f250,plain,(
% 0.13/0.39    ( ! [X0] : (k9_relat_1(sK1,k9_relat_1(sK0,X0)) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0))) ) | (~spl2_2 | ~spl2_32 | ~spl2_36)),
% 0.13/0.39    inference(forward_demodulation,[],[f247,f191])).
% 0.13/0.39  fof(f191,plain,(
% 0.13/0.39    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))) ) | ~spl2_32),
% 0.13/0.39    inference(avatar_component_clause,[],[f190])).
% 0.13/0.39  fof(f247,plain,(
% 0.13/0.39    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0))) ) | (~spl2_2 | ~spl2_36)),
% 0.13/0.39    inference(resolution,[],[f210,f38])).
% 0.13/0.39  fof(f38,plain,(
% 0.13/0.39    v1_relat_1(sK1) | ~spl2_2),
% 0.13/0.39    inference(avatar_component_clause,[],[f36])).
% 0.13/0.39  fof(f210,plain,(
% 0.13/0.39    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,X2),X3))) ) | ~spl2_36),
% 0.13/0.39    inference(avatar_component_clause,[],[f209])).
% 0.13/0.39  fof(f211,plain,(
% 0.13/0.39    spl2_36 | ~spl2_3 | ~spl2_15),
% 0.13/0.39    inference(avatar_split_clause,[],[f202,f98,f41,f209])).
% 0.13/0.39  fof(f41,plain,(
% 0.13/0.39    spl2_3 <=> v1_relat_1(sK0)),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.13/0.39  fof(f98,plain,(
% 0.13/0.39    spl2_15 <=> ! [X3,X2,X4] : (k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4) | ~v1_relat_1(X3) | ~v1_relat_1(X2))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.13/0.39  fof(f202,plain,(
% 0.13/0.39    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k2_relat_1(k7_relat_1(k5_relat_1(sK0,X2),X3))) ) | (~spl2_3 | ~spl2_15)),
% 0.13/0.39    inference(resolution,[],[f99,f43])).
% 0.13/0.39  fof(f43,plain,(
% 0.13/0.39    v1_relat_1(sK0) | ~spl2_3),
% 0.13/0.39    inference(avatar_component_clause,[],[f41])).
% 0.13/0.39  fof(f99,plain,(
% 0.13/0.39    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4)) ) | ~spl2_15),
% 0.13/0.39    inference(avatar_component_clause,[],[f98])).
% 0.13/0.39  fof(f192,plain,(
% 0.13/0.39    spl2_32 | ~spl2_2 | ~spl2_27),
% 0.13/0.39    inference(avatar_split_clause,[],[f186,f164,f36,f190])).
% 0.13/0.39  fof(f164,plain,(
% 0.13/0.39    spl2_27 <=> ! [X3,X2] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3)))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.13/0.39  fof(f186,plain,(
% 0.13/0.39    ( ! [X0] : (k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0))) ) | (~spl2_2 | ~spl2_27)),
% 0.13/0.39    inference(resolution,[],[f165,f38])).
% 0.13/0.39  fof(f165,plain,(
% 0.13/0.39    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3))) ) | ~spl2_27),
% 0.13/0.39    inference(avatar_component_clause,[],[f164])).
% 0.13/0.39  fof(f166,plain,(
% 0.13/0.39    spl2_27 | ~spl2_3 | ~spl2_8),
% 0.13/0.39    inference(avatar_split_clause,[],[f157,f62,f41,f164])).
% 0.13/0.39  fof(f62,plain,(
% 0.13/0.39    spl2_8 <=> ! [X1,X0,X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.13/0.39  fof(f157,plain,(
% 0.13/0.39    ( ! [X2,X3] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(sK0,X2),X3) = k9_relat_1(X2,k9_relat_1(sK0,X3))) ) | (~spl2_3 | ~spl2_8)),
% 0.13/0.39    inference(resolution,[],[f63,f43])).
% 0.13/0.39  fof(f63,plain,(
% 0.13/0.39    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) ) | ~spl2_8),
% 0.13/0.39    inference(avatar_component_clause,[],[f62])).
% 0.13/0.39  fof(f146,plain,(
% 0.13/0.39    spl2_23 | ~spl2_2 | ~spl2_18),
% 0.13/0.39    inference(avatar_split_clause,[],[f139,f115,f36,f143])).
% 0.13/0.39  fof(f115,plain,(
% 0.13/0.39    spl2_18 <=> ! [X1] : (~v1_relat_1(X1) | k5_relat_1(sK0,X1) = k7_relat_1(k5_relat_1(sK0,X1),k1_relat_1(sK0)))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.13/0.39  fof(f139,plain,(
% 0.13/0.39    k5_relat_1(sK0,sK1) = k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0)) | (~spl2_2 | ~spl2_18)),
% 0.13/0.39    inference(resolution,[],[f116,f38])).
% 0.13/0.39  fof(f116,plain,(
% 0.13/0.39    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(sK0,X1) = k7_relat_1(k5_relat_1(sK0,X1),k1_relat_1(sK0))) ) | ~spl2_18),
% 0.13/0.39    inference(avatar_component_clause,[],[f115])).
% 0.13/0.39  fof(f117,plain,(
% 0.13/0.39    spl2_18 | ~spl2_3 | ~spl2_16),
% 0.13/0.39    inference(avatar_split_clause,[],[f108,f104,f41,f115])).
% 0.13/0.39  fof(f104,plain,(
% 0.13/0.39    spl2_16 <=> ! [X1,X0] : (k5_relat_1(X0,X1) = k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.13/0.39  fof(f108,plain,(
% 0.13/0.39    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(sK0,X1) = k7_relat_1(k5_relat_1(sK0,X1),k1_relat_1(sK0))) ) | (~spl2_3 | ~spl2_16)),
% 0.13/0.39    inference(resolution,[],[f105,f43])).
% 0.13/0.39  fof(f105,plain,(
% 0.13/0.39    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(X0,X1) = k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0))) ) | ~spl2_16),
% 0.13/0.39    inference(avatar_component_clause,[],[f104])).
% 0.13/0.39  fof(f106,plain,(
% 0.13/0.39    spl2_16 | ~spl2_5 | ~spl2_7 | ~spl2_9),
% 0.13/0.39    inference(avatar_split_clause,[],[f102,f66,f58,f50,f104])).
% 0.13/0.39  fof(f50,plain,(
% 0.13/0.39    spl2_5 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.13/0.39  fof(f58,plain,(
% 0.13/0.39    spl2_7 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.13/0.39  fof(f66,plain,(
% 0.13/0.39    spl2_9 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.13/0.39  fof(f102,plain,(
% 0.13/0.39    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | (~spl2_5 | ~spl2_7 | ~spl2_9)),
% 0.13/0.39    inference(subsumption_resolution,[],[f101,f67])).
% 0.13/0.39  fof(f67,plain,(
% 0.13/0.39    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_9),
% 0.13/0.39    inference(avatar_component_clause,[],[f66])).
% 0.13/0.39  fof(f101,plain,(
% 0.13/0.39    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | (~spl2_5 | ~spl2_7)),
% 0.13/0.39    inference(resolution,[],[f59,f51])).
% 0.13/0.39  fof(f51,plain,(
% 0.13/0.39    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.13/0.39    inference(avatar_component_clause,[],[f50])).
% 0.13/0.39  fof(f59,plain,(
% 0.13/0.39    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl2_7),
% 0.13/0.39    inference(avatar_component_clause,[],[f58])).
% 0.13/0.39  fof(f100,plain,(
% 0.13/0.39    spl2_15 | ~spl2_6 | ~spl2_9),
% 0.13/0.39    inference(avatar_split_clause,[],[f88,f66,f54,f98])).
% 0.13/0.39  fof(f54,plain,(
% 0.13/0.39    spl2_6 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.13/0.39  fof(f88,plain,(
% 0.13/0.39    ( ! [X4,X2,X3] : (k2_relat_1(k7_relat_1(k5_relat_1(X2,X3),X4)) = k9_relat_1(k5_relat_1(X2,X3),X4) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) ) | (~spl2_6 | ~spl2_9)),
% 0.13/0.39    inference(resolution,[],[f55,f67])).
% 0.13/0.39  fof(f55,plain,(
% 0.13/0.39    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_6),
% 0.13/0.39    inference(avatar_component_clause,[],[f54])).
% 0.13/0.39  fof(f81,plain,(
% 0.13/0.39    spl2_11 | ~spl2_3 | ~spl2_4),
% 0.13/0.39    inference(avatar_split_clause,[],[f70,f46,f41,f78])).
% 0.13/0.39  fof(f46,plain,(
% 0.13/0.39    spl2_4 <=> ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.13/0.39    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.13/0.39  fof(f70,plain,(
% 0.13/0.39    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | (~spl2_3 | ~spl2_4)),
% 0.13/0.39    inference(resolution,[],[f47,f43])).
% 0.13/0.39  fof(f47,plain,(
% 0.13/0.39    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) ) | ~spl2_4),
% 0.13/0.39    inference(avatar_component_clause,[],[f46])).
% 0.13/0.39  fof(f68,plain,(
% 0.13/0.39    spl2_9),
% 0.13/0.39    inference(avatar_split_clause,[],[f29,f66])).
% 0.13/0.39  fof(f29,plain,(
% 0.13/0.39    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f17])).
% 0.13/0.39  fof(f17,plain,(
% 0.13/0.39    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.13/0.39    inference(flattening,[],[f16])).
% 0.13/0.39  fof(f16,plain,(
% 0.13/0.39    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.13/0.39    inference(ennf_transformation,[],[f1])).
% 0.13/0.39  fof(f1,axiom,(
% 0.13/0.39    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.13/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.13/0.39  fof(f64,plain,(
% 0.13/0.39    spl2_8),
% 0.13/0.39    inference(avatar_split_clause,[],[f28,f62])).
% 0.13/0.39  fof(f28,plain,(
% 0.13/0.39    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f15])).
% 0.13/0.39  fof(f15,plain,(
% 0.13/0.39    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.13/0.39    inference(ennf_transformation,[],[f4])).
% 0.13/0.39  fof(f4,axiom,(
% 0.13/0.39    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.13/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 0.13/0.39  fof(f60,plain,(
% 0.13/0.39    spl2_7),
% 0.13/0.39    inference(avatar_split_clause,[],[f27,f58])).
% 0.13/0.39  fof(f27,plain,(
% 0.13/0.39    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f14])).
% 0.13/0.39  fof(f14,plain,(
% 0.13/0.39    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.13/0.39    inference(flattening,[],[f13])).
% 0.13/0.39  fof(f13,plain,(
% 0.13/0.39    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.13/0.39    inference(ennf_transformation,[],[f6])).
% 0.13/0.39  fof(f6,axiom,(
% 0.13/0.39    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.13/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.13/0.39  fof(f56,plain,(
% 0.13/0.39    spl2_6),
% 0.13/0.39    inference(avatar_split_clause,[],[f26,f54])).
% 0.13/0.39  fof(f26,plain,(
% 0.13/0.39    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f12])).
% 0.13/0.39  fof(f12,plain,(
% 0.13/0.39    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.13/0.39    inference(ennf_transformation,[],[f3])).
% 0.13/0.39  fof(f3,axiom,(
% 0.13/0.39    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.13/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.13/0.39  fof(f52,plain,(
% 0.13/0.39    spl2_5),
% 0.13/0.39    inference(avatar_split_clause,[],[f25,f50])).
% 0.13/0.39  fof(f25,plain,(
% 0.13/0.39    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f11])).
% 0.13/0.39  fof(f11,plain,(
% 0.13/0.39    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.13/0.39    inference(ennf_transformation,[],[f5])).
% 0.13/0.39  fof(f5,axiom,(
% 0.13/0.39    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.13/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.13/0.39  fof(f48,plain,(
% 0.13/0.39    spl2_4),
% 0.13/0.39    inference(avatar_split_clause,[],[f24,f46])).
% 0.13/0.39  fof(f24,plain,(
% 0.13/0.39    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f10])).
% 0.13/0.39  fof(f10,plain,(
% 0.13/0.39    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.13/0.39    inference(ennf_transformation,[],[f2])).
% 0.13/0.39  fof(f2,axiom,(
% 0.13/0.39    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.13/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.13/0.39  fof(f44,plain,(
% 0.13/0.39    spl2_3),
% 0.13/0.39    inference(avatar_split_clause,[],[f21,f41])).
% 0.13/0.39  fof(f21,plain,(
% 0.13/0.39    v1_relat_1(sK0)),
% 0.13/0.39    inference(cnf_transformation,[],[f20])).
% 0.13/0.39  fof(f20,plain,(
% 0.13/0.39    (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.13/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).
% 0.13/0.39  fof(f18,plain,(
% 0.13/0.39    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.13/0.39    introduced(choice_axiom,[])).
% 0.13/0.39  fof(f19,plain,(
% 0.13/0.39    ? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) => (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1))),
% 0.13/0.39    introduced(choice_axiom,[])).
% 0.13/0.39  fof(f9,plain,(
% 0.13/0.39    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.13/0.39    inference(ennf_transformation,[],[f8])).
% 0.13/0.39  fof(f8,negated_conjecture,(
% 0.13/0.39    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.13/0.39    inference(negated_conjecture,[],[f7])).
% 0.13/0.39  fof(f7,conjecture,(
% 0.13/0.39    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.13/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.13/0.39  fof(f39,plain,(
% 0.13/0.39    spl2_2),
% 0.13/0.39    inference(avatar_split_clause,[],[f22,f36])).
% 0.13/0.39  fof(f22,plain,(
% 0.13/0.39    v1_relat_1(sK1)),
% 0.13/0.39    inference(cnf_transformation,[],[f20])).
% 0.13/0.39  fof(f34,plain,(
% 0.13/0.39    ~spl2_1),
% 0.13/0.39    inference(avatar_split_clause,[],[f23,f31])).
% 0.13/0.39  fof(f23,plain,(
% 0.13/0.39    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.13/0.39    inference(cnf_transformation,[],[f20])).
% 0.13/0.39  % SZS output end Proof for theBenchmark
% 0.13/0.39  % (14082)------------------------------
% 0.13/0.39  % (14082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.39  % (14082)Termination reason: Refutation
% 0.13/0.39  
% 0.13/0.39  % (14082)Memory used [KB]: 10746
% 0.13/0.39  % (14082)Time elapsed: 0.007 s
% 0.13/0.39  % (14082)------------------------------
% 0.13/0.39  % (14082)------------------------------
% 0.20/0.39  % (14074)Success in time 0.039 s
%------------------------------------------------------------------------------

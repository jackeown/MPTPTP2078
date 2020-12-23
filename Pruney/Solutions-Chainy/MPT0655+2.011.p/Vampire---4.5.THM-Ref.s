%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 320 expanded)
%              Number of leaves         :   17 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  306 (1078 expanded)
%              Number of equality atoms :   49 ( 101 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f91,f95,f100,f110,f124,f236,f252,f254])).

fof(f254,plain,(
    spl1_25 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | spl1_25 ),
    inference(resolution,[],[f251,f30])).

fof(f30,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f251,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK0)))
    | spl1_25 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl1_25
  <=> v2_funct_1(k6_relat_1(k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).

fof(f252,plain,
    ( ~ spl1_6
    | ~ spl1_5
    | ~ spl1_25
    | ~ spl1_3
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f248,f108,f77,f250,f86,f89])).

fof(f89,plain,
    ( spl1_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f86,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f77,plain,
    ( spl1_3
  <=> ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f108,plain,
    ( spl1_8
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f248,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ spl1_3
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f247,f65])).

fof(f65,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_subsumption,[],[f25,f26,f63])).

fof(f63,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(resolution,[],[f38,f27])).

fof(f27,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f247,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_funct_1(sK0)
    | ~ spl1_3
    | ~ spl1_8 ),
    inference(resolution,[],[f109,f78])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0))
        | ~ v1_funct_1(X0) )
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f109,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f236,plain,(
    spl1_7 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl1_7 ),
    inference(trivial_inequality_removal,[],[f232])).

fof(f232,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | spl1_7 ),
    inference(superposition,[],[f106,f191])).

fof(f191,plain,(
    k2_relat_1(sK0) = k1_relat_1(k6_relat_1(k2_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f190,f65])).

fof(f190,plain,(
    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(forward_demodulation,[],[f187,f159])).

fof(f159,plain,(
    k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) ),
    inference(global_subsumption,[],[f25,f158])).

fof(f158,plain,
    ( k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f157,f46])).

fof(f46,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(global_subsumption,[],[f25,f26,f44])).

fof(f44,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f35,f27])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f157,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f155,f50])).

fof(f50,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(global_subsumption,[],[f25,f26,f48])).

fof(f48,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f36,f27])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f155,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f43,f26])).

fof(f43,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | k10_relat_1(k2_funct_1(X1),k2_relat_1(k2_funct_1(X1))) = k1_relat_1(k2_funct_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f31,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f187,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) ),
    inference(resolution,[],[f181,f25])).

fof(f181,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(X0)) ) ),
    inference(global_subsumption,[],[f25,f175])).

fof(f175,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f57,f26])).

fof(f57,plain,(
    ! [X4,X3] :
      ( ~ v1_funct_1(X4)
      | ~ v1_relat_1(X3)
      | k1_relat_1(k5_relat_1(k2_funct_1(X4),X3)) = k10_relat_1(k2_funct_1(X4),k1_relat_1(X3))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f32,f33])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f106,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0)))
    | spl1_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl1_7
  <=> k2_relat_1(sK0) = k1_relat_1(k6_relat_1(k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f124,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | spl1_2 ),
    inference(avatar_split_clause,[],[f123,f74,f89,f86])).

fof(f74,plain,
    ( spl1_2
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f123,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2 ),
    inference(resolution,[],[f75,f33])).

fof(f75,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f110,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_7
    | spl1_8 ),
    inference(avatar_split_clause,[],[f103,f108,f105,f74,f71])).

fof(f71,plain,
    ( spl1_1
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f103,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0)) ),
    inference(global_subsumption,[],[f25,f26,f102])).

fof(f102,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f101,f50])).

fof(f101,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f93,f46])).

fof(f93,plain,
    ( k1_relat_1(k2_funct_1(sK0)) != k1_relat_1(k6_relat_1(k2_relat_1(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) ),
    inference(superposition,[],[f39,f65])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f100,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl1_6 ),
    inference(resolution,[],[f90,f26])).

fof(f90,plain,
    ( ~ v1_funct_1(sK0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f95,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl1_5 ),
    inference(resolution,[],[f87,f25])).

fof(f87,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f91,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | spl1_1 ),
    inference(avatar_split_clause,[],[f84,f71,f89,f86])).

fof(f84,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(resolution,[],[f72,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f79,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | spl1_3 ),
    inference(avatar_split_clause,[],[f69,f77,f74,f71])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0))
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f28,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f40,f50])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
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
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(f28,plain,(
    ~ v2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:12:52 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.46  % (18394)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.47  % (18386)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.47  % (18386)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (18375)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f79,f91,f95,f100,f110,f124,f236,f252,f254])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    spl1_25),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f253])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    $false | spl1_25),
% 0.21/0.48    inference(resolution,[],[f251,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ~v2_funct_1(k6_relat_1(k2_relat_1(sK0))) | spl1_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f250])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    spl1_25 <=> v2_funct_1(k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    ~spl1_6 | ~spl1_5 | ~spl1_25 | ~spl1_3 | ~spl1_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f248,f108,f77,f250,f86,f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl1_6 <=> v1_funct_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl1_5 <=> v1_relat_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl1_3 <=> ! [X0] : (~r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_funct_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl1_8 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    ~v2_funct_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | (~spl1_3 | ~spl1_8)),
% 0.21/0.48    inference(forward_demodulation,[],[f247,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.21/0.48    inference(global_subsumption,[],[f25,f26,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f38,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v2_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : ((~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    v1_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),sK0)) | ~v1_funct_1(sK0) | (~spl1_3 | ~spl1_8)),
% 0.21/0.48    inference(resolution,[],[f109,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_funct_1(X0)) ) | ~spl1_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f77])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~spl1_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f108])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    spl1_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f235])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    $false | spl1_7),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f232])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    k2_relat_1(sK0) != k2_relat_1(sK0) | spl1_7),
% 0.21/0.48    inference(superposition,[],[f106,f191])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    k2_relat_1(sK0) = k1_relat_1(k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.48    inference(forward_demodulation,[],[f190,f65])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.48    inference(forward_demodulation,[],[f187,f159])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))),
% 0.21/0.48    inference(global_subsumption,[],[f25,f158])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(forward_demodulation,[],[f157,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(global_subsumption,[],[f25,f26,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f35,f27])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(forward_demodulation,[],[f155,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(global_subsumption,[],[f25,f26,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f36,f27])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f43,f26])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_funct_1(X1) | k10_relat_1(k2_funct_1(X1),k2_relat_1(k2_funct_1(X1))) = k1_relat_1(k2_funct_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(resolution,[],[f31,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f181,f25])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(X0))) )),
% 0.21/0.48    inference(global_subsumption,[],[f25,f175])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(X0)) | ~v1_relat_1(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f57,f26])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X4,X3] : (~v1_funct_1(X4) | ~v1_relat_1(X3) | k1_relat_1(k5_relat_1(k2_funct_1(X4),X3)) = k10_relat_1(k2_funct_1(X4),k1_relat_1(X3)) | ~v1_relat_1(X4)) )),
% 0.21/0.48    inference(resolution,[],[f32,f33])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    k2_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0))) | spl1_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl1_7 <=> k2_relat_1(sK0) = k1_relat_1(k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ~spl1_5 | ~spl1_6 | spl1_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f123,f74,f89,f86])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl1_2 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_2),
% 0.21/0.48    inference(resolution,[],[f75,f33])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ~v1_relat_1(k2_funct_1(sK0)) | spl1_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ~spl1_1 | ~spl1_2 | ~spl1_7 | spl1_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f103,f108,f105,f74,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl1_1 <=> v1_funct_1(k2_funct_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(global_subsumption,[],[f25,f26,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_funct_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(forward_demodulation,[],[f101,f50])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    k2_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_funct_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))),
% 0.21/0.48    inference(forward_demodulation,[],[f93,f46])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    k1_relat_1(k2_funct_1(sK0)) != k1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_funct_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))),
% 0.21/0.48    inference(superposition,[],[f39,f65])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl1_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    $false | spl1_6),
% 0.21/0.48    inference(resolution,[],[f90,f26])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | spl1_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f89])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl1_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    $false | spl1_5),
% 0.21/0.48    inference(resolution,[],[f87,f25])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | spl1_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~spl1_5 | ~spl1_6 | spl1_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f84,f71,f89,f86])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_1),
% 0.21/0.48    inference(resolution,[],[f72,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ~v1_funct_1(k2_funct_1(sK0)) | spl1_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ~spl1_1 | ~spl1_2 | spl1_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f69,f77,f74,f71])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(global_subsumption,[],[f28,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(sK0))) )),
% 0.21/0.48    inference(superposition,[],[f40,f50])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ~v2_funct_1(k2_funct_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (18386)------------------------------
% 0.21/0.48  % (18386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18386)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (18386)Memory used [KB]: 10874
% 0.21/0.48  % (18386)Time elapsed: 0.070 s
% 0.21/0.48  % (18386)------------------------------
% 0.21/0.48  % (18386)------------------------------
% 0.21/0.48  % (18373)Success in time 0.123 s
%------------------------------------------------------------------------------

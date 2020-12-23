%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:58 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 183 expanded)
%              Number of leaves         :   24 (  86 expanded)
%              Depth                    :    7
%              Number of atoms          :  296 ( 546 expanded)
%              Number of equality atoms :   65 ( 135 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f68,f81,f100,f116,f122,f130,f138,f148,f188,f272,f278,f284])).

fof(f284,plain,
    ( ~ spl1_37
    | spl1_2
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f283,f126,f65,f59,f44,f275])).

fof(f275,plain,
    ( spl1_37
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_37])])).

fof(f44,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f59,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f65,plain,
    ( spl1_6
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f126,plain,
    ( spl1_16
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f283,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | spl1_2
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_16 ),
    inference(forward_demodulation,[],[f279,f128])).

fof(f128,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f279,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | spl1_2
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f61,f67,f46,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f46,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f67,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f61,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f278,plain,
    ( spl1_37
    | ~ spl1_19
    | ~ spl1_36 ),
    inference(avatar_split_clause,[],[f273,f268,f145,f275])).

fof(f145,plain,
    ( spl1_19
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f268,plain,
    ( spl1_36
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).

fof(f273,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ spl1_19
    | ~ spl1_36 ),
    inference(backward_demodulation,[],[f147,f270])).

fof(f270,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl1_36 ),
    inference(avatar_component_clause,[],[f268])).

fof(f147,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0))
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f145])).

fof(f272,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_36
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f266,f49,f268,f54,f59])).

fof(f54,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f49,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f266,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f30,f51])).

fof(f51,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f188,plain,
    ( ~ spl1_6
    | ~ spl1_5
    | spl1_1
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f187,f132,f40,f59,f65])).

fof(f40,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f132,plain,
    ( spl1_17
  <=> k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f187,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_1
    | ~ spl1_17 ),
    inference(trivial_inequality_removal,[],[f186])).

fof(f186,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_1
    | ~ spl1_17 ),
    inference(forward_demodulation,[],[f165,f134])).

fof(f134,plain,
    ( k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f165,plain,
    ( k2_relat_1(sK0) != k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(superposition,[],[f42,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f42,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f148,plain,
    ( spl1_19
    | ~ spl1_11
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f137,f126,f97,f145])).

fof(f97,plain,
    ( spl1_11
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k2_relat_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f137,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0))
    | ~ spl1_11
    | ~ spl1_16 ),
    inference(backward_demodulation,[],[f99,f128])).

fof(f99,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k2_relat_1(k2_funct_1(sK0)))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f138,plain,
    ( spl1_17
    | ~ spl1_15
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f135,f126,f118,f132])).

fof(f118,plain,
    ( spl1_15
  <=> k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f135,plain,
    ( k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))
    | ~ spl1_15
    | ~ spl1_16 ),
    inference(backward_demodulation,[],[f120,f128])).

fof(f120,plain,
    ( k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f118])).

fof(f130,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_16
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f124,f49,f126,f54,f59])).

fof(f124,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f32,f51])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f122,plain,
    ( spl1_15
    | ~ spl1_8
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f121,f113,f78,f118])).

fof(f78,plain,
    ( spl1_8
  <=> k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f113,plain,
    ( spl1_14
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f121,plain,
    ( k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ spl1_8
    | ~ spl1_14 ),
    inference(backward_demodulation,[],[f80,f115])).

fof(f115,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f113])).

fof(f80,plain,
    ( k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f116,plain,
    ( spl1_14
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f111,f59,f54,f49,f113])).

fof(f111,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f61,f56,f51,f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f100,plain,
    ( spl1_11
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f89,f65,f59,f97])).

fof(f89,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k2_relat_1(k2_funct_1(sK0)))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f61,f67,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f81,plain,
    ( spl1_8
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f76,f65,f78])).

fof(f76,plain,
    ( k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f67,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f68,plain,
    ( spl1_6
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f63,f59,f54,f65])).

fof(f63,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f61,f56,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f62,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f57,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f27,f49])).

fof(f27,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f28,f44,f40])).

fof(f28,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:24:24 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (1999)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (2007)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.53  % (1995)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.53  % (1997)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.53  % (2008)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.53  % (1993)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.54  % (1994)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.41/0.54  % (1997)Refutation found. Thanks to Tanya!
% 1.41/0.54  % SZS status Theorem for theBenchmark
% 1.41/0.54  % (1992)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.41/0.54  % (1994)Refutation not found, incomplete strategy% (1994)------------------------------
% 1.41/0.54  % (1994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (2001)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.41/0.54  % (1991)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.41/0.54  % (2013)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.41/0.54  % (2014)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.41/0.54  % (2002)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.41/0.54  % (1994)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (1994)Memory used [KB]: 10490
% 1.41/0.54  % (1994)Time elapsed: 0.112 s
% 1.41/0.54  % (1994)------------------------------
% 1.41/0.54  % (1994)------------------------------
% 1.41/0.54  % (2005)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.41/0.54  % (2014)Refutation not found, incomplete strategy% (2014)------------------------------
% 1.41/0.54  % (2014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (2014)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (2014)Memory used [KB]: 10618
% 1.41/0.54  % (2014)Time elapsed: 0.110 s
% 1.41/0.54  % (2014)------------------------------
% 1.41/0.54  % (2014)------------------------------
% 1.41/0.54  % (1998)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.41/0.54  % (1998)Refutation not found, incomplete strategy% (1998)------------------------------
% 1.41/0.54  % (1998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (1998)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (1998)Memory used [KB]: 6140
% 1.41/0.54  % (1998)Time elapsed: 0.104 s
% 1.41/0.54  % (1998)------------------------------
% 1.41/0.54  % (1998)------------------------------
% 1.41/0.54  % (2001)Refutation not found, incomplete strategy% (2001)------------------------------
% 1.41/0.54  % (2001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (2001)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (2001)Memory used [KB]: 10618
% 1.41/0.54  % (2001)Time elapsed: 0.069 s
% 1.41/0.54  % (2001)------------------------------
% 1.41/0.54  % (2001)------------------------------
% 1.41/0.54  % (2011)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.41/0.54  % (2009)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.41/0.55  % (2003)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.41/0.55  % (2006)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.41/0.55  % (2010)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.41/0.55  % (2000)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.41/0.55  % (1996)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.49/0.56  % (2012)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.49/0.56  % (2004)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.49/0.56  % SZS output start Proof for theBenchmark
% 1.49/0.56  fof(f294,plain,(
% 1.49/0.56    $false),
% 1.49/0.56    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f68,f81,f100,f116,f122,f130,f138,f148,f188,f272,f278,f284])).
% 1.49/0.56  fof(f284,plain,(
% 1.49/0.56    ~spl1_37 | spl1_2 | ~spl1_5 | ~spl1_6 | ~spl1_16),
% 1.49/0.56    inference(avatar_split_clause,[],[f283,f126,f65,f59,f44,f275])).
% 1.49/0.56  fof(f275,plain,(
% 1.49/0.56    spl1_37 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_37])])).
% 1.49/0.56  fof(f44,plain,(
% 1.49/0.56    spl1_2 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.49/0.56  fof(f59,plain,(
% 1.49/0.56    spl1_5 <=> v1_relat_1(sK0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.49/0.56  fof(f65,plain,(
% 1.49/0.56    spl1_6 <=> v1_relat_1(k2_funct_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 1.49/0.56  fof(f126,plain,(
% 1.49/0.56    spl1_16 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 1.49/0.56  fof(f283,plain,(
% 1.49/0.56    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | (spl1_2 | ~spl1_5 | ~spl1_6 | ~spl1_16)),
% 1.49/0.56    inference(forward_demodulation,[],[f279,f128])).
% 1.49/0.56  fof(f128,plain,(
% 1.49/0.56    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_16),
% 1.49/0.56    inference(avatar_component_clause,[],[f126])).
% 1.49/0.56  fof(f279,plain,(
% 1.49/0.56    ~r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | (spl1_2 | ~spl1_5 | ~spl1_6)),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f61,f67,f46,f33])).
% 1.49/0.56  fof(f33,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f17])).
% 1.49/0.56  fof(f17,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(flattening,[],[f16])).
% 1.49/0.56  fof(f16,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f4])).
% 1.49/0.56  fof(f4,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 1.49/0.56  fof(f46,plain,(
% 1.49/0.56    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_2),
% 1.49/0.56    inference(avatar_component_clause,[],[f44])).
% 1.49/0.56  fof(f67,plain,(
% 1.49/0.56    v1_relat_1(k2_funct_1(sK0)) | ~spl1_6),
% 1.49/0.56    inference(avatar_component_clause,[],[f65])).
% 1.49/0.56  fof(f61,plain,(
% 1.49/0.56    v1_relat_1(sK0) | ~spl1_5),
% 1.49/0.56    inference(avatar_component_clause,[],[f59])).
% 1.49/0.56  fof(f278,plain,(
% 1.49/0.56    spl1_37 | ~spl1_19 | ~spl1_36),
% 1.49/0.56    inference(avatar_split_clause,[],[f273,f268,f145,f275])).
% 1.49/0.56  fof(f145,plain,(
% 1.49/0.56    spl1_19 <=> r1_tarski(k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 1.49/0.56  fof(f268,plain,(
% 1.49/0.56    spl1_36 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).
% 1.49/0.56  fof(f273,plain,(
% 1.49/0.56    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | (~spl1_19 | ~spl1_36)),
% 1.49/0.56    inference(backward_demodulation,[],[f147,f270])).
% 1.49/0.56  fof(f270,plain,(
% 1.49/0.56    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~spl1_36),
% 1.49/0.56    inference(avatar_component_clause,[],[f268])).
% 1.49/0.56  fof(f147,plain,(
% 1.49/0.56    r1_tarski(k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0)) | ~spl1_19),
% 1.49/0.56    inference(avatar_component_clause,[],[f145])).
% 1.49/0.56  fof(f272,plain,(
% 1.49/0.56    ~spl1_5 | ~spl1_4 | spl1_36 | ~spl1_3),
% 1.49/0.56    inference(avatar_split_clause,[],[f266,f49,f268,f54,f59])).
% 1.49/0.56  fof(f54,plain,(
% 1.49/0.56    spl1_4 <=> v1_funct_1(sK0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.49/0.56  fof(f49,plain,(
% 1.49/0.56    spl1_3 <=> v2_funct_1(sK0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.49/0.56  fof(f266,plain,(
% 1.49/0.56    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 1.49/0.56    inference(resolution,[],[f30,f51])).
% 1.49/0.56  fof(f51,plain,(
% 1.49/0.56    v2_funct_1(sK0) | ~spl1_3),
% 1.49/0.56    inference(avatar_component_clause,[],[f49])).
% 1.49/0.56  fof(f30,plain,(
% 1.49/0.56    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f13])).
% 1.49/0.56  fof(f13,plain,(
% 1.49/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(flattening,[],[f12])).
% 1.49/0.56  fof(f12,plain,(
% 1.49/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,axiom,(
% 1.49/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.49/0.56  fof(f188,plain,(
% 1.49/0.56    ~spl1_6 | ~spl1_5 | spl1_1 | ~spl1_17),
% 1.49/0.56    inference(avatar_split_clause,[],[f187,f132,f40,f59,f65])).
% 1.49/0.56  fof(f40,plain,(
% 1.49/0.56    spl1_1 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.49/0.56  fof(f132,plain,(
% 1.49/0.56    spl1_17 <=> k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 1.49/0.56  fof(f187,plain,(
% 1.49/0.56    ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | (spl1_1 | ~spl1_17)),
% 1.49/0.56    inference(trivial_inequality_removal,[],[f186])).
% 1.49/0.56  fof(f186,plain,(
% 1.49/0.56    k2_relat_1(sK0) != k2_relat_1(sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | (spl1_1 | ~spl1_17)),
% 1.49/0.56    inference(forward_demodulation,[],[f165,f134])).
% 1.49/0.56  fof(f134,plain,(
% 1.49/0.56    k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) | ~spl1_17),
% 1.49/0.56    inference(avatar_component_clause,[],[f132])).
% 1.49/0.56  fof(f165,plain,(
% 1.49/0.56    k2_relat_1(sK0) != k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | spl1_1),
% 1.49/0.56    inference(superposition,[],[f42,f34])).
% 1.49/0.56  fof(f34,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f18])).
% 1.49/0.56  fof(f18,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f2])).
% 1.49/0.56  fof(f2,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.49/0.56  fof(f42,plain,(
% 1.49/0.56    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_1),
% 1.49/0.56    inference(avatar_component_clause,[],[f40])).
% 1.49/0.56  fof(f148,plain,(
% 1.49/0.56    spl1_19 | ~spl1_11 | ~spl1_16),
% 1.49/0.56    inference(avatar_split_clause,[],[f137,f126,f97,f145])).
% 1.49/0.56  fof(f97,plain,(
% 1.49/0.56    spl1_11 <=> r1_tarski(k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k2_relat_1(k2_funct_1(sK0)))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 1.49/0.56  fof(f137,plain,(
% 1.49/0.56    r1_tarski(k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0)) | (~spl1_11 | ~spl1_16)),
% 1.49/0.56    inference(backward_demodulation,[],[f99,f128])).
% 1.49/0.56  fof(f99,plain,(
% 1.49/0.56    r1_tarski(k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k2_relat_1(k2_funct_1(sK0))) | ~spl1_11),
% 1.49/0.56    inference(avatar_component_clause,[],[f97])).
% 1.49/0.56  fof(f138,plain,(
% 1.49/0.56    spl1_17 | ~spl1_15 | ~spl1_16),
% 1.49/0.56    inference(avatar_split_clause,[],[f135,f126,f118,f132])).
% 1.49/0.56  fof(f118,plain,(
% 1.49/0.56    spl1_15 <=> k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0)))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 1.49/0.56  fof(f135,plain,(
% 1.49/0.56    k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) | (~spl1_15 | ~spl1_16)),
% 1.49/0.56    inference(backward_demodulation,[],[f120,f128])).
% 1.49/0.56  fof(f120,plain,(
% 1.49/0.56    k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) | ~spl1_15),
% 1.49/0.56    inference(avatar_component_clause,[],[f118])).
% 1.49/0.56  fof(f130,plain,(
% 1.49/0.56    ~spl1_5 | ~spl1_4 | spl1_16 | ~spl1_3),
% 1.49/0.56    inference(avatar_split_clause,[],[f124,f49,f126,f54,f59])).
% 1.49/0.56  fof(f124,plain,(
% 1.49/0.56    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 1.49/0.56    inference(resolution,[],[f32,f51])).
% 1.49/0.56  fof(f32,plain,(
% 1.49/0.56    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f15])).
% 1.49/0.56  fof(f15,plain,(
% 1.49/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(flattening,[],[f14])).
% 1.49/0.56  fof(f14,plain,(
% 1.49/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f6])).
% 1.49/0.56  fof(f6,axiom,(
% 1.49/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.49/0.56  fof(f122,plain,(
% 1.49/0.56    spl1_15 | ~spl1_8 | ~spl1_14),
% 1.49/0.56    inference(avatar_split_clause,[],[f121,f113,f78,f118])).
% 1.49/0.56  fof(f78,plain,(
% 1.49/0.56    spl1_8 <=> k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) = k1_relat_1(k2_funct_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 1.49/0.56  fof(f113,plain,(
% 1.49/0.56    spl1_14 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 1.49/0.56  fof(f121,plain,(
% 1.49/0.56    k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) | (~spl1_8 | ~spl1_14)),
% 1.49/0.56    inference(backward_demodulation,[],[f80,f115])).
% 1.49/0.56  fof(f115,plain,(
% 1.49/0.56    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_14),
% 1.49/0.56    inference(avatar_component_clause,[],[f113])).
% 1.49/0.56  fof(f80,plain,(
% 1.49/0.56    k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_8),
% 1.49/0.56    inference(avatar_component_clause,[],[f78])).
% 1.49/0.56  fof(f116,plain,(
% 1.49/0.56    spl1_14 | ~spl1_3 | ~spl1_4 | ~spl1_5),
% 1.49/0.56    inference(avatar_split_clause,[],[f111,f59,f54,f49,f113])).
% 1.49/0.56  fof(f111,plain,(
% 1.49/0.56    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | (~spl1_3 | ~spl1_4 | ~spl1_5)),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f61,f56,f51,f31])).
% 1.49/0.56  fof(f31,plain,(
% 1.49/0.56    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f15])).
% 1.49/0.56  fof(f56,plain,(
% 1.49/0.56    v1_funct_1(sK0) | ~spl1_4),
% 1.49/0.56    inference(avatar_component_clause,[],[f54])).
% 1.49/0.56  fof(f100,plain,(
% 1.49/0.56    spl1_11 | ~spl1_5 | ~spl1_6),
% 1.49/0.56    inference(avatar_split_clause,[],[f89,f65,f59,f97])).
% 1.49/0.56  fof(f89,plain,(
% 1.49/0.56    r1_tarski(k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k2_relat_1(k2_funct_1(sK0))) | (~spl1_5 | ~spl1_6)),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f61,f67,f36])).
% 1.49/0.56  fof(f36,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f20])).
% 1.49/0.56  fof(f20,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f3])).
% 1.49/0.56  fof(f3,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.49/0.56  fof(f81,plain,(
% 1.49/0.56    spl1_8 | ~spl1_6),
% 1.49/0.56    inference(avatar_split_clause,[],[f76,f65,f78])).
% 1.49/0.56  fof(f76,plain,(
% 1.49/0.56    k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_6),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f67,f35])).
% 1.49/0.56  fof(f35,plain,(
% 1.49/0.56    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f19])).
% 1.49/0.56  fof(f19,plain,(
% 1.49/0.56    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f1])).
% 1.49/0.56  fof(f1,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.49/0.56  fof(f68,plain,(
% 1.49/0.56    spl1_6 | ~spl1_4 | ~spl1_5),
% 1.49/0.56    inference(avatar_split_clause,[],[f63,f59,f54,f65])).
% 1.49/0.56  fof(f63,plain,(
% 1.49/0.56    v1_relat_1(k2_funct_1(sK0)) | (~spl1_4 | ~spl1_5)),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f61,f56,f37])).
% 1.49/0.56  fof(f37,plain,(
% 1.49/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f22])).
% 1.49/0.56  fof(f22,plain,(
% 1.49/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(flattening,[],[f21])).
% 1.49/0.56  fof(f21,plain,(
% 1.49/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.49/0.56  fof(f62,plain,(
% 1.49/0.56    spl1_5),
% 1.49/0.56    inference(avatar_split_clause,[],[f25,f59])).
% 1.49/0.56  fof(f25,plain,(
% 1.49/0.56    v1_relat_1(sK0)),
% 1.49/0.56    inference(cnf_transformation,[],[f24])).
% 1.49/0.56  fof(f24,plain,(
% 1.49/0.56    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f23])).
% 1.49/0.56  fof(f23,plain,(
% 1.49/0.56    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f11,plain,(
% 1.49/0.56    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.49/0.56    inference(flattening,[],[f10])).
% 1.49/0.56  fof(f10,plain,(
% 1.49/0.56    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f9])).
% 1.49/0.56  fof(f9,negated_conjecture,(
% 1.49/0.56    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.49/0.56    inference(negated_conjecture,[],[f8])).
% 1.49/0.56  fof(f8,conjecture,(
% 1.49/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 1.49/0.56  fof(f57,plain,(
% 1.49/0.56    spl1_4),
% 1.49/0.56    inference(avatar_split_clause,[],[f26,f54])).
% 1.49/0.56  fof(f26,plain,(
% 1.49/0.56    v1_funct_1(sK0)),
% 1.49/0.56    inference(cnf_transformation,[],[f24])).
% 1.49/0.56  fof(f52,plain,(
% 1.49/0.56    spl1_3),
% 1.49/0.56    inference(avatar_split_clause,[],[f27,f49])).
% 1.49/0.56  fof(f27,plain,(
% 1.49/0.56    v2_funct_1(sK0)),
% 1.49/0.56    inference(cnf_transformation,[],[f24])).
% 1.49/0.56  fof(f47,plain,(
% 1.49/0.56    ~spl1_1 | ~spl1_2),
% 1.49/0.56    inference(avatar_split_clause,[],[f28,f44,f40])).
% 1.49/0.56  fof(f28,plain,(
% 1.49/0.56    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.49/0.56    inference(cnf_transformation,[],[f24])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (1997)------------------------------
% 1.49/0.56  % (1997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (1997)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (1997)Memory used [KB]: 10746
% 1.49/0.56  % (1997)Time elapsed: 0.105 s
% 1.49/0.56  % (1997)------------------------------
% 1.49/0.56  % (1997)------------------------------
% 1.49/0.56  % (1990)Success in time 0.198 s
%------------------------------------------------------------------------------

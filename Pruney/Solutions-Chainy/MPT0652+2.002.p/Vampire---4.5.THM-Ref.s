%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 144 expanded)
%              Number of leaves         :   20 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  221 ( 379 expanded)
%              Number of equality atoms :   62 ( 110 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f59,f66,f73,f80,f97,f103,f139,f145,f216,f220])).

fof(f220,plain,(
    spl1_23 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl1_23 ),
    inference(unit_resulting_resolution,[],[f34,f215])).

% (2748)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f215,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | spl1_23 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl1_23
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f216,plain,
    ( spl1_15
    | ~ spl1_23
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f211,f70,f63,f47,f213,f142])).

fof(f142,plain,
    ( spl1_15
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f47,plain,
    ( spl1_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f63,plain,
    ( spl1_6
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f70,plain,
    ( spl1_7
  <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f211,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f210,f72])).

fof(f72,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f70])).

% (2744)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f210,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f208,f65])).

fof(f65,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f208,plain,
    ( k1_relat_1(k4_relat_1(sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl1_3 ),
    inference(resolution,[],[f161,f49])).

fof(f49,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(k4_relat_1(X0)) = k1_relat_1(k5_relat_1(k4_relat_1(X0),sK0))
        | ~ r1_tarski(k2_relat_1(k4_relat_1(X0)),k1_relat_1(sK0)) )
    | ~ spl1_3 ),
    inference(resolution,[],[f147,f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f147,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK0))
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK0)) )
    | ~ spl1_3 ),
    inference(resolution,[],[f29,f49])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f145,plain,
    ( ~ spl1_15
    | spl1_5
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f140,f94,f56,f142])).

fof(f56,plain,
    ( spl1_5
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f94,plain,
    ( spl1_10
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f140,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl1_5
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f58,f96])).

fof(f96,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f58,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f139,plain,
    ( spl1_11
    | ~ spl1_3
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f138,f77,f70,f47,f100])).

fof(f100,plain,
    ( spl1_11
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f77,plain,
    ( spl1_8
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f138,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ spl1_3
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f137,f79])).

fof(f79,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f137,plain,
    ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f135,f72])).

fof(f135,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0)))
    | ~ spl1_3 ),
    inference(resolution,[],[f127,f49])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(k4_relat_1(X0),sK0)) = k9_relat_1(sK0,k2_relat_1(k4_relat_1(X0))) )
    | ~ spl1_3 ),
    inference(resolution,[],[f121,f24])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(X0,sK0)) = k9_relat_1(sK0,k2_relat_1(X0)) )
    | ~ spl1_3 ),
    inference(resolution,[],[f28,f49])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f103,plain,
    ( ~ spl1_11
    | spl1_4
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f98,f94,f52,f100])).

fof(f52,plain,
    ( spl1_4
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f98,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl1_4
    | ~ spl1_10 ),
    inference(backward_demodulation,[],[f54,f96])).

fof(f54,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f97,plain,
    ( spl1_10
    | ~ spl1_3
    | ~ spl1_2
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f92,f37,f42,f47,f94])).

fof(f42,plain,
    ( spl1_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f37,plain,
    ( spl1_1
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f92,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_1 ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f80,plain,
    ( spl1_8
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f74,f47,f77])).

fof(f74,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_3 ),
    inference(resolution,[],[f25,f49])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f73,plain,
    ( spl1_7
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f67,f47,f70])).

fof(f67,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_3 ),
    inference(resolution,[],[f27,f49])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f66,plain,
    ( spl1_6
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f60,f47,f63])).

fof(f60,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_3 ),
    inference(resolution,[],[f26,f49])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,
    ( ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f20,f56,f52])).

fof(f20,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f11])).

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

fof(f50,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f23,f37])).

fof(f23,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:10:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.48  % (2768)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.49  % (2759)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (2759)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f40,f45,f50,f59,f66,f73,f80,f97,f103,f139,f145,f216,f220])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    spl1_23),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f217])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    $false | spl1_23),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f34,f215])).
% 0.22/0.50  % (2748)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | spl1_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f213])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    spl1_23 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    spl1_15 | ~spl1_23 | ~spl1_3 | ~spl1_6 | ~spl1_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f211,f70,f63,f47,f213,f142])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    spl1_15 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    spl1_3 <=> v1_relat_1(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl1_6 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl1_7 <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | (~spl1_3 | ~spl1_6 | ~spl1_7)),
% 0.22/0.50    inference(forward_demodulation,[],[f210,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f70])).
% 0.22/0.50  % (2744)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) | (~spl1_3 | ~spl1_6)),
% 0.22/0.50    inference(forward_demodulation,[],[f208,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f63])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    k1_relat_1(k4_relat_1(sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) | ~spl1_3),
% 0.22/0.50    inference(resolution,[],[f161,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    v1_relat_1(sK0) | ~spl1_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f47])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k1_relat_1(k5_relat_1(k4_relat_1(X0),sK0)) | ~r1_tarski(k2_relat_1(k4_relat_1(X0)),k1_relat_1(sK0))) ) | ~spl1_3),
% 0.22/0.50    inference(resolution,[],[f147,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK0)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK0))) ) | ~spl1_3),
% 0.22/0.50    inference(resolution,[],[f29,f49])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ~spl1_15 | spl1_5 | ~spl1_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f140,f94,f56,f142])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl1_5 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    spl1_10 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | (spl1_5 | ~spl1_10)),
% 0.22/0.50    inference(forward_demodulation,[],[f58,f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f94])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f56])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    spl1_11 | ~spl1_3 | ~spl1_7 | ~spl1_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f138,f77,f70,f47,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    spl1_11 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl1_8 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | (~spl1_3 | ~spl1_7 | ~spl1_8)),
% 0.22/0.50    inference(forward_demodulation,[],[f137,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f77])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | (~spl1_3 | ~spl1_7)),
% 0.22/0.50    inference(forward_demodulation,[],[f135,f72])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0))) | ~spl1_3),
% 0.22/0.50    inference(resolution,[],[f127,f49])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k4_relat_1(X0),sK0)) = k9_relat_1(sK0,k2_relat_1(k4_relat_1(X0)))) ) | ~spl1_3),
% 0.22/0.50    inference(resolution,[],[f121,f24])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,sK0)) = k9_relat_1(sK0,k2_relat_1(X0))) ) | ~spl1_3),
% 0.22/0.50    inference(resolution,[],[f28,f49])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ~spl1_11 | spl1_4 | ~spl1_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f98,f94,f52,f100])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    spl1_4 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | (spl1_4 | ~spl1_10)),
% 0.22/0.50    inference(backward_demodulation,[],[f54,f96])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f52])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl1_10 | ~spl1_3 | ~spl1_2 | ~spl1_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f92,f37,f42,f47,f94])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    spl1_2 <=> v1_funct_1(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    spl1_1 <=> v2_funct_1(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_1),
% 0.22/0.50    inference(resolution,[],[f30,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    v2_funct_1(sK0) | ~spl1_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f37])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl1_8 | ~spl1_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f74,f47,f77])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_3),
% 0.22/0.50    inference(resolution,[],[f25,f49])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl1_7 | ~spl1_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f67,f47,f70])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_3),
% 0.22/0.50    inference(resolution,[],[f27,f49])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl1_6 | ~spl1_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f60,f47,f63])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_3),
% 0.22/0.50    inference(resolution,[],[f26,f49])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ~spl1_4 | ~spl1_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f20,f56,f52])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    spl1_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f21,f47])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    v1_relat_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    spl1_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f22,f42])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    v1_funct_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    spl1_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f37])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    v2_funct_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (2759)------------------------------
% 0.22/0.50  % (2759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (2759)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (2759)Memory used [KB]: 6268
% 0.22/0.50  % (2759)Time elapsed: 0.048 s
% 0.22/0.50  % (2759)------------------------------
% 0.22/0.50  % (2759)------------------------------
% 0.22/0.50  % (2739)Success in time 0.141 s
%------------------------------------------------------------------------------

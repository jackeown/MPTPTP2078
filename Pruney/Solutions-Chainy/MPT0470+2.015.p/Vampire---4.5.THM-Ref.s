%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 377 expanded)
%              Number of leaves         :   25 ( 114 expanded)
%              Depth                    :   16
%              Number of atoms          :  355 ( 860 expanded)
%              Number of equality atoms :   61 ( 186 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f810,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f74,f79,f124,f213,f240,f262,f266,f355,f359,f797,f809])).

fof(f809,plain,
    ( spl1_2
    | ~ spl1_3
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f808])).

fof(f808,plain,
    ( $false
    | spl1_2
    | ~ spl1_3
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f56,f280])).

fof(f280,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_3
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f278,f94])).

fof(f94,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(resolution,[],[f92,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f92,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f91,f68])).

fof(f68,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl1_3
  <=> v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f91,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f90,f30])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f90,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl1_3 ),
    inference(superposition,[],[f42,f89])).

fof(f89,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f88,f31])).

fof(f31,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f88,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f85,f64])).

fof(f64,plain,(
    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f60,f30])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f37,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f85,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))
    | ~ spl1_3 ),
    inference(resolution,[],[f38,f68])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f278,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0)
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(backward_demodulation,[],[f214,f267])).

fof(f267,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_12 ),
    inference(resolution,[],[f257,f35])).

fof(f257,plain,
    ( v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl1_12
  <=> v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f214,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_8 ),
    inference(resolution,[],[f203,f37])).

fof(f203,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl1_8
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f56,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f797,plain,
    ( spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_10
    | ~ spl1_16 ),
    inference(avatar_contradiction_clause,[],[f796])).

fof(f796,plain,
    ( $false
    | spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_10
    | ~ spl1_16 ),
    inference(subsumption_resolution,[],[f795,f52])).

fof(f52,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f795,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_10
    | ~ spl1_16 ),
    inference(forward_demodulation,[],[f794,f94])).

fof(f794,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_10
    | ~ spl1_16 ),
    inference(forward_demodulation,[],[f793,f373])).

fof(f373,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_10
    | ~ spl1_16 ),
    inference(forward_demodulation,[],[f371,f94])).

fof(f371,plain,
    ( k4_relat_1(k1_xboole_0) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl1_10
    | ~ spl1_16 ),
    inference(backward_demodulation,[],[f241,f360])).

fof(f360,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_16 ),
    inference(resolution,[],[f350,f35])).

fof(f350,plain,
    ( v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl1_16
  <=> v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f241,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | ~ spl1_10 ),
    inference(resolution,[],[f230,f37])).

fof(f230,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl1_10
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f793,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f787,f94])).

fof(f787,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0))
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(resolution,[],[f487,f73])).

fof(f73,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl1_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f487,plain,
    ( ! [X5] :
        ( ~ v1_relat_1(X5)
        | k4_relat_1(k5_relat_1(X5,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X5)) )
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f483,f59])).

fof(f59,plain,(
    sK0 = k4_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f37,f29])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f483,plain,
    ( ! [X5] :
        ( ~ v1_relat_1(X5)
        | k4_relat_1(k5_relat_1(X5,k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X5)) )
    | ~ spl1_6 ),
    inference(resolution,[],[f41,f114])).

fof(f114,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl1_6
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f359,plain,
    ( ~ spl1_10
    | spl1_17 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | ~ spl1_10
    | spl1_17 ),
    inference(subsumption_resolution,[],[f356,f230])).

fof(f356,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | spl1_17 ),
    inference(resolution,[],[f354,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f354,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | spl1_17 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl1_17
  <=> v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f355,plain,
    ( spl1_16
    | ~ spl1_17
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f346,f229,f113,f71,f352,f348])).

fof(f346,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_10 ),
    inference(subsumption_resolution,[],[f345,f30])).

fof(f345,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_10 ),
    inference(superposition,[],[f42,f248])).

fof(f248,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f243,f195])).

fof(f195,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(resolution,[],[f190,f114])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_4 ),
    inference(resolution,[],[f188,f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

% (28598)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f188,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f186,f73])).

fof(f186,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f40,f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f243,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))
    | ~ spl1_10 ),
    inference(resolution,[],[f230,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f266,plain,
    ( ~ spl1_8
    | spl1_13 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl1_8
    | spl1_13 ),
    inference(subsumption_resolution,[],[f263,f203])).

fof(f263,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_13 ),
    inference(resolution,[],[f261,f36])).

fof(f261,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | spl1_13 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl1_13
  <=> v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f262,plain,
    ( spl1_12
    | ~ spl1_13
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f253,f202,f71,f259,f255])).

fof(f253,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f252,f30])).

fof(f252,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(superposition,[],[f42,f221])).

fof(f221,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f216,f197])).

fof(f197,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_4 ),
    inference(resolution,[],[f190,f29])).

fof(f216,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_8 ),
    inference(resolution,[],[f203,f39])).

fof(f240,plain,
    ( ~ spl1_4
    | ~ spl1_6
    | spl1_10 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl1_4
    | ~ spl1_6
    | spl1_10 ),
    inference(subsumption_resolution,[],[f238,f73])).

fof(f238,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_6
    | spl1_10 ),
    inference(subsumption_resolution,[],[f236,f114])).

fof(f236,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_10 ),
    inference(resolution,[],[f231,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f231,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | spl1_10 ),
    inference(avatar_component_clause,[],[f229])).

fof(f213,plain,
    ( ~ spl1_4
    | spl1_8 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl1_4
    | spl1_8 ),
    inference(subsumption_resolution,[],[f211,f73])).

fof(f211,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_8 ),
    inference(subsumption_resolution,[],[f209,f29])).

fof(f209,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_8 ),
    inference(resolution,[],[f204,f43])).

fof(f204,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_8 ),
    inference(avatar_component_clause,[],[f202])).

fof(f124,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f123])).

% (28596)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (28595)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (28586)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f123,plain,
    ( $false
    | spl1_6 ),
    inference(subsumption_resolution,[],[f121,f29])).

fof(f121,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(resolution,[],[f115,f36])).

fof(f115,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f79,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f77,f30])).

fof(f77,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_3 ),
    inference(resolution,[],[f75,f34])).

fof(f75,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_3 ),
    inference(resolution,[],[f69,f36])).

fof(f69,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f74,plain,
    ( ~ spl1_3
    | spl1_4 ),
    inference(avatar_split_clause,[],[f65,f71,f67])).

fof(f65,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(superposition,[],[f36,f64])).

fof(f57,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f28,f54,f50])).

fof(f28,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:06:01 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.51  % (28602)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (28585)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (28584)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (28599)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (28600)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (28591)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (28593)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (28581)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (28603)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (28588)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (28583)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (28590)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (28579)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (28578)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (28597)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (28589)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (28582)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (28587)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (28580)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (28592)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (28594)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (28601)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (28600)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f810,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f57,f74,f79,f124,f213,f240,f262,f266,f355,f359,f797,f809])).
% 0.21/0.55  fof(f809,plain,(
% 0.21/0.55    spl1_2 | ~spl1_3 | ~spl1_8 | ~spl1_12),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f808])).
% 0.21/0.55  fof(f808,plain,(
% 0.21/0.55    $false | (spl1_2 | ~spl1_3 | ~spl1_8 | ~spl1_12)),
% 0.21/0.55    inference(subsumption_resolution,[],[f56,f280])).
% 0.21/0.55  fof(f280,plain,(
% 0.21/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl1_3 | ~spl1_8 | ~spl1_12)),
% 0.21/0.55    inference(forward_demodulation,[],[f278,f94])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl1_3),
% 0.21/0.55    inference(resolution,[],[f92,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl1_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f91,f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl1_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    spl1_3 <=> v1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl1_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f90,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    v1_xboole_0(k1_xboole_0)),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    v1_xboole_0(k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl1_3),
% 0.21/0.55    inference(superposition,[],[f42,f89])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) | ~spl1_3),
% 0.21/0.55    inference(forward_demodulation,[],[f88,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) | ~spl1_3),
% 0.21/0.55    inference(forward_demodulation,[],[f85,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0))),
% 0.21/0.55    inference(resolution,[],[f60,f30])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 0.21/0.55    inference(resolution,[],[f37,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0))) | ~spl1_3),
% 0.21/0.55    inference(resolution,[],[f38,f68])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.21/0.55  fof(f278,plain,(
% 0.21/0.55    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0) | (~spl1_8 | ~spl1_12)),
% 0.21/0.55    inference(backward_demodulation,[],[f214,f267])).
% 0.21/0.55  fof(f267,plain,(
% 0.21/0.55    k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_12),
% 0.21/0.55    inference(resolution,[],[f257,f35])).
% 0.21/0.55  fof(f257,plain,(
% 0.21/0.55    v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~spl1_12),
% 0.21/0.55    inference(avatar_component_clause,[],[f255])).
% 0.21/0.55  fof(f255,plain,(
% 0.21/0.55    spl1_12 <=> v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.55  fof(f214,plain,(
% 0.21/0.55    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~spl1_8),
% 0.21/0.55    inference(resolution,[],[f203,f37])).
% 0.21/0.55  fof(f203,plain,(
% 0.21/0.55    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f202])).
% 0.21/0.55  fof(f202,plain,(
% 0.21/0.55    spl1_8 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    spl1_2 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.55  fof(f797,plain,(
% 0.21/0.55    spl1_1 | ~spl1_3 | ~spl1_4 | ~spl1_6 | ~spl1_10 | ~spl1_16),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f796])).
% 0.21/0.55  fof(f796,plain,(
% 0.21/0.55    $false | (spl1_1 | ~spl1_3 | ~spl1_4 | ~spl1_6 | ~spl1_10 | ~spl1_16)),
% 0.21/0.55    inference(subsumption_resolution,[],[f795,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    spl1_1 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.55  fof(f795,plain,(
% 0.21/0.55    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_3 | ~spl1_4 | ~spl1_6 | ~spl1_10 | ~spl1_16)),
% 0.21/0.55    inference(forward_demodulation,[],[f794,f94])).
% 0.21/0.55  fof(f794,plain,(
% 0.21/0.55    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) | (~spl1_3 | ~spl1_4 | ~spl1_6 | ~spl1_10 | ~spl1_16)),
% 0.21/0.55    inference(forward_demodulation,[],[f793,f373])).
% 0.21/0.55  fof(f373,plain,(
% 0.21/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | (~spl1_3 | ~spl1_10 | ~spl1_16)),
% 0.21/0.55    inference(forward_demodulation,[],[f371,f94])).
% 0.21/0.55  fof(f371,plain,(
% 0.21/0.55    k4_relat_1(k1_xboole_0) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | (~spl1_10 | ~spl1_16)),
% 0.21/0.55    inference(backward_demodulation,[],[f241,f360])).
% 0.21/0.55  fof(f360,plain,(
% 0.21/0.55    k1_xboole_0 = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_16),
% 0.21/0.55    inference(resolution,[],[f350,f35])).
% 0.21/0.55  fof(f350,plain,(
% 0.21/0.55    v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | ~spl1_16),
% 0.21/0.55    inference(avatar_component_clause,[],[f348])).
% 0.21/0.55  fof(f348,plain,(
% 0.21/0.55    spl1_16 <=> v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.21/0.55  fof(f241,plain,(
% 0.21/0.55    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | ~spl1_10),
% 0.21/0.55    inference(resolution,[],[f230,f37])).
% 0.21/0.55  fof(f230,plain,(
% 0.21/0.55    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f229])).
% 0.21/0.55  fof(f229,plain,(
% 0.21/0.55    spl1_10 <=> v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.55  fof(f793,plain,(
% 0.21/0.55    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | (~spl1_3 | ~spl1_4 | ~spl1_6)),
% 0.21/0.55    inference(forward_demodulation,[],[f787,f94])).
% 0.21/0.55  fof(f787,plain,(
% 0.21/0.55    k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0)) | (~spl1_4 | ~spl1_6)),
% 0.21/0.55    inference(resolution,[],[f487,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    v1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    spl1_4 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.55  fof(f487,plain,(
% 0.21/0.55    ( ! [X5] : (~v1_relat_1(X5) | k4_relat_1(k5_relat_1(X5,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X5))) ) | ~spl1_6),
% 0.21/0.55    inference(forward_demodulation,[],[f483,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    sK0 = k4_relat_1(k4_relat_1(sK0))),
% 0.21/0.55    inference(resolution,[],[f37,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    v1_relat_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.55    inference(negated_conjecture,[],[f14])).
% 0.21/0.55  fof(f14,conjecture,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.55  fof(f483,plain,(
% 0.21/0.55    ( ! [X5] : (~v1_relat_1(X5) | k4_relat_1(k5_relat_1(X5,k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X5))) ) | ~spl1_6),
% 0.21/0.55    inference(resolution,[],[f41,f114])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    v1_relat_1(k4_relat_1(sK0)) | ~spl1_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f113])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    spl1_6 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.55  fof(f359,plain,(
% 0.21/0.55    ~spl1_10 | spl1_17),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f358])).
% 0.21/0.55  fof(f358,plain,(
% 0.21/0.55    $false | (~spl1_10 | spl1_17)),
% 0.21/0.55    inference(subsumption_resolution,[],[f356,f230])).
% 0.21/0.55  fof(f356,plain,(
% 0.21/0.55    ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | spl1_17),
% 0.21/0.55    inference(resolution,[],[f354,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.55  fof(f354,plain,(
% 0.21/0.55    ~v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | spl1_17),
% 0.21/0.55    inference(avatar_component_clause,[],[f352])).
% 0.21/0.55  fof(f352,plain,(
% 0.21/0.55    spl1_17 <=> v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.21/0.55  fof(f355,plain,(
% 0.21/0.55    spl1_16 | ~spl1_17 | ~spl1_4 | ~spl1_6 | ~spl1_10),
% 0.21/0.55    inference(avatar_split_clause,[],[f346,f229,f113,f71,f352,f348])).
% 0.21/0.55  fof(f346,plain,(
% 0.21/0.55    ~v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | (~spl1_4 | ~spl1_6 | ~spl1_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f345,f30])).
% 0.21/0.55  fof(f345,plain,(
% 0.21/0.55    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | (~spl1_4 | ~spl1_6 | ~spl1_10)),
% 0.21/0.55    inference(superposition,[],[f42,f248])).
% 0.21/0.55  fof(f248,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | (~spl1_4 | ~spl1_6 | ~spl1_10)),
% 0.21/0.55    inference(forward_demodulation,[],[f243,f195])).
% 0.21/0.55  fof(f195,plain,(
% 0.21/0.55    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | (~spl1_4 | ~spl1_6)),
% 0.21/0.55    inference(resolution,[],[f190,f114])).
% 0.21/0.55  fof(f190,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) ) | ~spl1_4),
% 0.21/0.55    inference(resolution,[],[f188,f139])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(resolution,[],[f46,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  % (28598)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 0.21/0.55    inference(subsumption_resolution,[],[f186,f73])).
% 0.21/0.55  fof(f186,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.55    inference(superposition,[],[f40,f31])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.21/0.55  fof(f243,plain,(
% 0.21/0.55    k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))) | ~spl1_10),
% 0.21/0.55    inference(resolution,[],[f230,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f266,plain,(
% 0.21/0.55    ~spl1_8 | spl1_13),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f265])).
% 0.21/0.55  fof(f265,plain,(
% 0.21/0.55    $false | (~spl1_8 | spl1_13)),
% 0.21/0.55    inference(subsumption_resolution,[],[f263,f203])).
% 0.21/0.55  fof(f263,plain,(
% 0.21/0.55    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_13),
% 0.21/0.55    inference(resolution,[],[f261,f36])).
% 0.21/0.55  fof(f261,plain,(
% 0.21/0.55    ~v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | spl1_13),
% 0.21/0.55    inference(avatar_component_clause,[],[f259])).
% 0.21/0.55  fof(f259,plain,(
% 0.21/0.55    spl1_13 <=> v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.21/0.55  fof(f262,plain,(
% 0.21/0.55    spl1_12 | ~spl1_13 | ~spl1_4 | ~spl1_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f253,f202,f71,f259,f255])).
% 0.21/0.55  fof(f253,plain,(
% 0.21/0.55    ~v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl1_4 | ~spl1_8)),
% 0.21/0.55    inference(subsumption_resolution,[],[f252,f30])).
% 0.21/0.55  fof(f252,plain,(
% 0.21/0.55    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | v1_xboole_0(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl1_4 | ~spl1_8)),
% 0.21/0.55    inference(superposition,[],[f42,f221])).
% 0.21/0.55  fof(f221,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl1_4 | ~spl1_8)),
% 0.21/0.55    inference(forward_demodulation,[],[f216,f197])).
% 0.21/0.55  fof(f197,plain,(
% 0.21/0.55    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_4),
% 0.21/0.55    inference(resolution,[],[f190,f29])).
% 0.21/0.55  fof(f216,plain,(
% 0.21/0.55    k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | ~spl1_8),
% 0.21/0.55    inference(resolution,[],[f203,f39])).
% 0.21/0.55  fof(f240,plain,(
% 0.21/0.55    ~spl1_4 | ~spl1_6 | spl1_10),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f239])).
% 0.21/0.55  fof(f239,plain,(
% 0.21/0.55    $false | (~spl1_4 | ~spl1_6 | spl1_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f238,f73])).
% 0.21/0.55  fof(f238,plain,(
% 0.21/0.55    ~v1_relat_1(k1_xboole_0) | (~spl1_6 | spl1_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f236,f114])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | spl1_10),
% 0.21/0.55    inference(resolution,[],[f231,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.55  fof(f231,plain,(
% 0.21/0.55    ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | spl1_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f229])).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    ~spl1_4 | spl1_8),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f212])).
% 0.21/0.55  fof(f212,plain,(
% 0.21/0.55    $false | (~spl1_4 | spl1_8)),
% 0.21/0.55    inference(subsumption_resolution,[],[f211,f73])).
% 0.21/0.55  fof(f211,plain,(
% 0.21/0.55    ~v1_relat_1(k1_xboole_0) | spl1_8),
% 0.21/0.55    inference(subsumption_resolution,[],[f209,f29])).
% 0.21/0.55  fof(f209,plain,(
% 0.21/0.55    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_8),
% 0.21/0.55    inference(resolution,[],[f204,f43])).
% 0.21/0.55  fof(f204,plain,(
% 0.21/0.55    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f202])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    spl1_6),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f123])).
% 1.46/0.56  % (28596)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.46/0.56  % (28595)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.46/0.56  % (28586)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.46/0.57  fof(f123,plain,(
% 1.46/0.57    $false | spl1_6),
% 1.46/0.57    inference(subsumption_resolution,[],[f121,f29])).
% 1.46/0.57  fof(f121,plain,(
% 1.46/0.57    ~v1_relat_1(sK0) | spl1_6),
% 1.46/0.57    inference(resolution,[],[f115,f36])).
% 1.46/0.57  fof(f115,plain,(
% 1.46/0.57    ~v1_relat_1(k4_relat_1(sK0)) | spl1_6),
% 1.46/0.57    inference(avatar_component_clause,[],[f113])).
% 1.46/0.57  fof(f79,plain,(
% 1.46/0.57    spl1_3),
% 1.46/0.57    inference(avatar_contradiction_clause,[],[f78])).
% 1.46/0.57  fof(f78,plain,(
% 1.46/0.57    $false | spl1_3),
% 1.46/0.57    inference(subsumption_resolution,[],[f77,f30])).
% 1.46/0.57  fof(f77,plain,(
% 1.46/0.57    ~v1_xboole_0(k1_xboole_0) | spl1_3),
% 1.46/0.57    inference(resolution,[],[f75,f34])).
% 1.46/0.57  fof(f75,plain,(
% 1.46/0.57    ~v1_relat_1(k1_xboole_0) | spl1_3),
% 1.46/0.57    inference(resolution,[],[f69,f36])).
% 1.46/0.57  fof(f69,plain,(
% 1.46/0.57    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl1_3),
% 1.46/0.57    inference(avatar_component_clause,[],[f67])).
% 1.46/0.57  fof(f74,plain,(
% 1.46/0.57    ~spl1_3 | spl1_4),
% 1.46/0.57    inference(avatar_split_clause,[],[f65,f71,f67])).
% 1.46/0.57  fof(f65,plain,(
% 1.46/0.57    v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.46/0.57    inference(superposition,[],[f36,f64])).
% 1.46/0.57  fof(f57,plain,(
% 1.46/0.57    ~spl1_1 | ~spl1_2),
% 1.46/0.57    inference(avatar_split_clause,[],[f28,f54,f50])).
% 1.46/0.57  fof(f28,plain,(
% 1.46/0.57    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.46/0.57    inference(cnf_transformation,[],[f16])).
% 1.46/0.57  % SZS output end Proof for theBenchmark
% 1.46/0.57  % (28600)------------------------------
% 1.46/0.57  % (28600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (28600)Termination reason: Refutation
% 1.46/0.57  
% 1.46/0.57  % (28600)Memory used [KB]: 11001
% 1.46/0.57  % (28600)Time elapsed: 0.141 s
% 1.46/0.57  % (28600)------------------------------
% 1.46/0.57  % (28600)------------------------------
% 1.56/0.57  % (28577)Success in time 0.203 s
%------------------------------------------------------------------------------

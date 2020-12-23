%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 187 expanded)
%              Number of leaves         :   29 (  90 expanded)
%              Depth                    :    8
%              Number of atoms          :  243 ( 400 expanded)
%              Number of equality atoms :   65 ( 134 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f40,f44,f48,f52,f56,f64,f69,f84,f99,f117,f121,f264,f407,f716,f1694,f1916,f2067,f2191,f2211])).

fof(f2211,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_83 ),
    inference(avatar_contradiction_clause,[],[f2210])).

fof(f2210,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_83 ),
    inference(subsumption_resolution,[],[f35,f2193])).

fof(f2193,plain,
    ( ! [X2,X3] : r1_xboole_0(k4_xboole_0(X2,X3),X3)
    | ~ spl2_4
    | ~ spl2_83 ),
    inference(resolution,[],[f2190,f47])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f2190,plain,
    ( ! [X12,X11] : r1_xboole_0(X11,k4_xboole_0(X12,X11))
    | ~ spl2_83 ),
    inference(avatar_component_clause,[],[f2189])).

% (29350)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f2189,plain,
    ( spl2_83
  <=> ! [X11,X12] : r1_xboole_0(X11,k4_xboole_0(X12,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).

fof(f35,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_1
  <=> r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f2191,plain,
    ( spl2_83
    | ~ spl2_5
    | ~ spl2_81 ),
    inference(avatar_split_clause,[],[f2121,f2065,f50,f2189])).

% (29348)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f50,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f2065,plain,
    ( spl2_81
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).

fof(f2121,plain,
    ( ! [X12,X11] : r1_xboole_0(X11,k4_xboole_0(X12,X11))
    | ~ spl2_5
    | ~ spl2_81 ),
    inference(trivial_inequality_removal,[],[f2101])).

fof(f2101,plain,
    ( ! [X12,X11] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(X11,k4_xboole_0(X12,X11)) )
    | ~ spl2_5
    | ~ spl2_81 ),
    inference(superposition,[],[f51,f2066])).

fof(f2066,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))
    | ~ spl2_81 ),
    inference(avatar_component_clause,[],[f2065])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f2067,plain,
    ( spl2_81
    | ~ spl2_23
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f1932,f1914,f262,f2065])).

fof(f262,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f1914,plain,
    ( spl2_76
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f1932,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))
    | ~ spl2_23
    | ~ spl2_76 ),
    inference(superposition,[],[f1915,f263])).

fof(f263,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f262])).

fof(f1915,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),X1)
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f1914])).

fof(f1916,plain,
    ( spl2_76
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_74 ),
    inference(avatar_split_clause,[],[f1879,f1692,f42,f38,f1914])).

fof(f38,plain,
    ( spl2_2
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f42,plain,
    ( spl2_3
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1692,plain,
    ( spl2_74
  <=> ! [X3,X2,X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f1879,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),X1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_74 ),
    inference(forward_demodulation,[],[f1829,f39])).

fof(f39,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f1829,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k1_xboole_0))
    | ~ spl2_3
    | ~ spl2_74 ),
    inference(superposition,[],[f1693,f43])).

fof(f43,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f1693,plain,
    ( ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X4)))
    | ~ spl2_74 ),
    inference(avatar_component_clause,[],[f1692])).

fof(f1694,plain,
    ( spl2_74
    | ~ spl2_34
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f909,f714,f405,f1692])).

fof(f405,plain,
    ( spl2_34
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f714,plain,
    ( spl2_46
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f909,plain,
    ( ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X4)))
    | ~ spl2_34
    | ~ spl2_46 ),
    inference(superposition,[],[f715,f406])).

fof(f406,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f405])).

fof(f715,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f714])).

fof(f716,plain,
    ( spl2_46
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f586,f262,f119,f115,f97,f82,f714])).

fof(f82,plain,
    ( spl2_10
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f97,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f115,plain,
    ( spl2_13
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f119,plain,
    ( spl2_14
  <=> ! [X3,X2] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f586,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_23 ),
    inference(backward_demodulation,[],[f120,f583])).

fof(f583,plain,
    ( ! [X25] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X25)
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f582,f83])).

fof(f83,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f582,plain,
    ( ! [X24,X25] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X24),X25))) = k4_xboole_0(k1_xboole_0,X25)
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f581,f116])).

fof(f116,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f581,plain,
    ( ! [X24,X25] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X24),X25))) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X25))
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f523,f98])).

fof(f98,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f523,plain,
    ( ! [X24,X25] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X24),X25))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X25)
    | ~ spl2_10
    | ~ spl2_23 ),
    inference(superposition,[],[f263,f83])).

fof(f120,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f407,plain,(
    spl2_34 ),
    inference(avatar_split_clause,[],[f30,f405])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f25,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f264,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f29,f262])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f23,f19,f19])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f121,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f101,f97,f42,f119])).

fof(f101,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(superposition,[],[f98,f43])).

fof(f117,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f100,f97,f38,f115])).

fof(f100,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(superposition,[],[f98,f39])).

fof(f99,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f24,f97])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f84,plain,
    ( spl2_10
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f78,f67,f54,f82])).

fof(f54,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f67,plain,
    ( spl2_8
  <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f78,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(resolution,[],[f55,f68])).

fof(f68,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f69,plain,
    ( spl2_8
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f65,f62,f46,f67])).

fof(f62,plain,
    ( spl2_7
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f65,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(resolution,[],[f63,f47])).

fof(f63,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f59,f50,f42,f38,f62])).

fof(f59,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f57,f43])).

fof(f57,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k4_xboole_0(X0,X0)
        | r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f51,f39])).

fof(f56,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f31,f42])).

% (29352)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f26,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13])).

% (29359)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f13,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (29354)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (29351)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (29358)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (29358)Refutation not found, incomplete strategy% (29358)------------------------------
% 0.20/0.49  % (29358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (29358)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (29358)Memory used [KB]: 10490
% 0.20/0.49  % (29358)Time elapsed: 0.056 s
% 0.20/0.49  % (29358)------------------------------
% 0.20/0.49  % (29358)------------------------------
% 0.20/0.49  % (29362)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (29361)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (29354)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f2212,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f36,f40,f44,f48,f52,f56,f64,f69,f84,f99,f117,f121,f264,f407,f716,f1694,f1916,f2067,f2191,f2211])).
% 0.20/0.49  fof(f2211,plain,(
% 0.20/0.49    spl2_1 | ~spl2_4 | ~spl2_83),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f2210])).
% 0.20/0.49  fof(f2210,plain,(
% 0.20/0.49    $false | (spl2_1 | ~spl2_4 | ~spl2_83)),
% 0.20/0.49    inference(subsumption_resolution,[],[f35,f2193])).
% 0.20/0.49  fof(f2193,plain,(
% 0.20/0.49    ( ! [X2,X3] : (r1_xboole_0(k4_xboole_0(X2,X3),X3)) ) | (~spl2_4 | ~spl2_83)),
% 0.20/0.49    inference(resolution,[],[f2190,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl2_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    spl2_4 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.49  fof(f2190,plain,(
% 0.20/0.49    ( ! [X12,X11] : (r1_xboole_0(X11,k4_xboole_0(X12,X11))) ) | ~spl2_83),
% 0.20/0.49    inference(avatar_component_clause,[],[f2189])).
% 0.20/0.49  % (29350)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  fof(f2189,plain,(
% 0.20/0.49    spl2_83 <=> ! [X11,X12] : r1_xboole_0(X11,k4_xboole_0(X12,X11))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) | spl2_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    spl2_1 <=> r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.49  fof(f2191,plain,(
% 0.20/0.49    spl2_83 | ~spl2_5 | ~spl2_81),
% 0.20/0.49    inference(avatar_split_clause,[],[f2121,f2065,f50,f2189])).
% 0.20/0.49  % (29348)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    spl2_5 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.49  fof(f2065,plain,(
% 0.20/0.49    spl2_81 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).
% 0.20/0.49  fof(f2121,plain,(
% 0.20/0.49    ( ! [X12,X11] : (r1_xboole_0(X11,k4_xboole_0(X12,X11))) ) | (~spl2_5 | ~spl2_81)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f2101])).
% 0.20/0.49  fof(f2101,plain,(
% 0.20/0.49    ( ! [X12,X11] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X11,k4_xboole_0(X12,X11))) ) | (~spl2_5 | ~spl2_81)),
% 0.20/0.49    inference(superposition,[],[f51,f2066])).
% 0.20/0.50  fof(f2066,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) ) | ~spl2_81),
% 0.20/0.50    inference(avatar_component_clause,[],[f2065])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) ) | ~spl2_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f50])).
% 0.20/0.50  fof(f2067,plain,(
% 0.20/0.50    spl2_81 | ~spl2_23 | ~spl2_76),
% 0.20/0.50    inference(avatar_split_clause,[],[f1932,f1914,f262,f2065])).
% 0.20/0.50  fof(f262,plain,(
% 0.20/0.50    spl2_23 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.20/0.50  fof(f1914,plain,(
% 0.20/0.50    spl2_76 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 0.20/0.50  fof(f1932,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) ) | (~spl2_23 | ~spl2_76)),
% 0.20/0.50    inference(superposition,[],[f1915,f263])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | ~spl2_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f262])).
% 0.20/0.50  fof(f1915,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),X1)) ) | ~spl2_76),
% 0.20/0.50    inference(avatar_component_clause,[],[f1914])).
% 0.20/0.50  fof(f1916,plain,(
% 0.20/0.50    spl2_76 | ~spl2_2 | ~spl2_3 | ~spl2_74),
% 0.20/0.50    inference(avatar_split_clause,[],[f1879,f1692,f42,f38,f1914])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    spl2_2 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    spl2_3 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.50  fof(f1692,plain,(
% 0.20/0.50    spl2_74 <=> ! [X3,X2,X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X4)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 0.20/0.50  fof(f1879,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),X1)) ) | (~spl2_2 | ~spl2_3 | ~spl2_74)),
% 0.20/0.50    inference(forward_demodulation,[],[f1829,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f38])).
% 0.20/0.50  fof(f1829,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k1_xboole_0))) ) | (~spl2_3 | ~spl2_74)),
% 0.20/0.50    inference(superposition,[],[f1693,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f42])).
% 0.20/0.50  fof(f1693,plain,(
% 0.20/0.50    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X4)))) ) | ~spl2_74),
% 0.20/0.50    inference(avatar_component_clause,[],[f1692])).
% 0.20/0.50  fof(f1694,plain,(
% 0.20/0.50    spl2_74 | ~spl2_34 | ~spl2_46),
% 0.20/0.50    inference(avatar_split_clause,[],[f909,f714,f405,f1692])).
% 0.20/0.50  fof(f405,plain,(
% 0.20/0.50    spl2_34 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.50  fof(f714,plain,(
% 0.20/0.50    spl2_46 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.20/0.50  fof(f909,plain,(
% 0.20/0.50    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X4)))) ) | (~spl2_34 | ~spl2_46)),
% 0.20/0.50    inference(superposition,[],[f715,f406])).
% 0.20/0.50  fof(f406,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl2_34),
% 0.20/0.50    inference(avatar_component_clause,[],[f405])).
% 0.20/0.50  fof(f715,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) ) | ~spl2_46),
% 0.20/0.50    inference(avatar_component_clause,[],[f714])).
% 0.20/0.50  fof(f716,plain,(
% 0.20/0.50    spl2_46 | ~spl2_10 | ~spl2_12 | ~spl2_13 | ~spl2_14 | ~spl2_23),
% 0.20/0.50    inference(avatar_split_clause,[],[f586,f262,f119,f115,f97,f82,f714])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    spl2_10 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    spl2_12 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    spl2_13 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    spl2_14 <=> ! [X3,X2] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.50  fof(f586,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) ) | (~spl2_10 | ~spl2_12 | ~spl2_13 | ~spl2_14 | ~spl2_23)),
% 0.20/0.50    inference(backward_demodulation,[],[f120,f583])).
% 0.20/0.50  fof(f583,plain,(
% 0.20/0.50    ( ! [X25] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X25)) ) | (~spl2_10 | ~spl2_12 | ~spl2_13 | ~spl2_23)),
% 0.20/0.50    inference(forward_demodulation,[],[f582,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) ) | ~spl2_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f82])).
% 0.20/0.50  fof(f582,plain,(
% 0.20/0.50    ( ! [X24,X25] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X24),X25))) = k4_xboole_0(k1_xboole_0,X25)) ) | (~spl2_10 | ~spl2_12 | ~spl2_13 | ~spl2_23)),
% 0.20/0.50    inference(forward_demodulation,[],[f581,f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) ) | ~spl2_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f115])).
% 0.20/0.50  fof(f581,plain,(
% 0.20/0.50    ( ! [X24,X25] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X24),X25))) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X25))) ) | (~spl2_10 | ~spl2_12 | ~spl2_23)),
% 0.20/0.50    inference(forward_demodulation,[],[f523,f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f97])).
% 0.20/0.50  fof(f523,plain,(
% 0.20/0.50    ( ! [X24,X25] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X24),X25))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X25)) ) | (~spl2_10 | ~spl2_23)),
% 0.20/0.50    inference(superposition,[],[f263,f83])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) ) | ~spl2_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f119])).
% 0.20/0.50  fof(f407,plain,(
% 0.20/0.50    spl2_34),
% 0.20/0.50    inference(avatar_split_clause,[],[f30,f405])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f25,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.20/0.50  fof(f264,plain,(
% 0.20/0.50    spl2_23),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f262])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f23,f19,f19])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    spl2_14 | ~spl2_3 | ~spl2_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f101,f97,f42,f119])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) ) | (~spl2_3 | ~spl2_12)),
% 0.20/0.50    inference(superposition,[],[f98,f43])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    spl2_13 | ~spl2_2 | ~spl2_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f100,f97,f38,f115])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) ) | (~spl2_2 | ~spl2_12)),
% 0.20/0.50    inference(superposition,[],[f98,f39])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    spl2_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f24,f97])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl2_10 | ~spl2_6 | ~spl2_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f78,f67,f54,f82])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    spl2_6 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    spl2_8 <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) ) | (~spl2_6 | ~spl2_8)),
% 0.20/0.50    inference(resolution,[],[f55,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl2_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f67])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f54])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    spl2_8 | ~spl2_4 | ~spl2_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f65,f62,f46,f67])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    spl2_7 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | (~spl2_4 | ~spl2_7)),
% 0.20/0.50    inference(resolution,[],[f63,f47])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl2_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f62])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    spl2_7 | ~spl2_2 | ~spl2_3 | ~spl2_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f59,f50,f42,f38,f62])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f57,f43])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(X0,X0) | r1_xboole_0(X0,k1_xboole_0)) ) | (~spl2_2 | ~spl2_5)),
% 0.20/0.50    inference(superposition,[],[f51,f39])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    spl2_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f54])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f21,f19])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    spl2_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f27,f50])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f22,f19])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    spl2_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f20,f46])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    spl2_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f31,f42])).
% 0.20/0.50  % (29352)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.50    inference(backward_demodulation,[],[f26,f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f17,f19])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    spl2_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f18,f38])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ~spl2_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f16,f33])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13])).
% 0.20/0.50  % (29359)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1) => ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.50    inference(negated_conjecture,[],[f9])).
% 0.20/0.50  fof(f9,conjecture,(
% 0.20/0.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (29354)------------------------------
% 0.20/0.50  % (29354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29354)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (29354)Memory used [KB]: 7675
% 0.20/0.50  % (29354)Time elapsed: 0.069 s
% 0.20/0.50  % (29354)------------------------------
% 0.20/0.50  % (29354)------------------------------
% 0.20/0.50  % (29346)Success in time 0.146 s
%------------------------------------------------------------------------------

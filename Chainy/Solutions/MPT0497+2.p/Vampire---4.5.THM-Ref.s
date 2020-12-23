%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0497+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:33 EST 2020

% Result     : Theorem 6.31s
% Output     : Refutation 7.00s
% Verified   : 
% Statistics : Number of formulae       :  724 (2349 expanded)
%              Number of leaves         :  200 ( 873 expanded)
%              Depth                    :   12
%              Number of atoms          : 2536 (9181 expanded)
%              Number of equality atoms :  462 (1906 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5365,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1993,f1996,f2000,f2008,f2016,f2046,f2057,f2064,f2068,f2082,f2089,f2100,f2146,f2153,f2157,f2161,f2162,f2169,f2173,f2177,f2181,f2185,f2189,f2190,f2192,f2194,f2207,f2270,f2271,f2273,f2276,f2280,f2299,f2303,f2308,f2379,f2384,f2388,f2392,f2399,f2406,f2410,f2414,f2415,f2419,f2423,f2427,f2431,f2435,f2439,f2443,f2451,f2458,f2463,f2467,f2475,f2533,f2539,f2554,f2586,f2624,f2685,f2789,f3171,f3175,f3179,f3180,f3181,f3188,f3262,f3268,f3278,f3282,f3287,f3291,f3296,f3300,f3304,f3309,f3314,f3321,f3325,f3329,f3331,f3335,f3338,f3344,f3348,f3351,f3353,f3514,f3545,f3554,f3556,f3561,f3610,f3612,f3680,f3687,f3691,f3695,f3696,f3708,f3776,f3787,f3789,f3793,f3911,f3912,f3913,f3917,f4302,f5362,f5364])).

fof(f5364,plain,(
    spl80_69 ),
    inference(avatar_contradiction_clause,[],[f5363])).

fof(f5363,plain,
    ( $false
    | spl80_69 ),
    inference(global_subsumption,[],[f1280,f5358])).

fof(f5358,plain,
    ( ~ v1_relat_1(sK1)
    | spl80_69 ),
    inference(resolution,[],[f3274,f1360])).

fof(f1360,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f809])).

fof(f809,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f3274,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl80_69 ),
    inference(avatar_component_clause,[],[f3273])).

fof(f3273,plain,
    ( spl80_69
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_69])])).

fof(f1280,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1057])).

fof(f1057,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1055,f1056])).

fof(f1056,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1055,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1054])).

fof(f1054,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f746])).

fof(f746,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f740])).

fof(f740,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f739])).

fof(f739,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f5362,plain,(
    spl80_69 ),
    inference(avatar_contradiction_clause,[],[f5361])).

fof(f5361,plain,
    ( $false
    | spl80_69 ),
    inference(global_subsumption,[],[f1280,f5358])).

% (7617)Time limit reached!
% (7617)------------------------------
% (7617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7617)Termination reason: Time limit
% (7617)Termination phase: Saturation

% (7617)Memory used [KB]: 20084
% (7617)Time elapsed: 0.800 s
% (7617)------------------------------
% (7617)------------------------------
fof(f4302,plain,
    ( spl80_101
    | spl80_102
    | ~ spl80_11
    | ~ spl80_85 ),
    inference(avatar_split_clause,[],[f4232,f3543,f2062,f4300,f4297])).

fof(f4297,plain,
    ( spl80_101
  <=> ! [X13] : r2_hidden(X13,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_101])])).

fof(f4300,plain,
    ( spl80_102
  <=> ! [X12] :
        ( k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(X12))
        | ~ r2_hidden(X12,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_102])])).

fof(f2062,plain,
    ( spl80_11
  <=> k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_11])])).

fof(f3543,plain,
    ( spl80_85
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_85])])).

fof(f4232,plain,
    ( ! [X12,X13] :
        ( k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(X12))
        | r2_hidden(X13,k1_relat_1(sK1))
        | ~ r2_hidden(X12,k1_relat_1(sK1)) )
    | ~ spl80_11
    | ~ spl80_85 ),
    inference(superposition,[],[f3568,f1540])).

fof(f1540,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f889])).

fof(f889,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f888])).

fof(f888,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f418])).

fof(f418,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f3568,plain,
    ( ! [X21] : k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(X21,k1_relat_1(sK1)))
    | ~ spl80_11
    | ~ spl80_85 ),
    inference(backward_demodulation,[],[f2284,f3544])).

fof(f3544,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl80_85 ),
    inference(avatar_component_clause,[],[f3543])).

fof(f2284,plain,
    ( ! [X21] : k3_xboole_0(sK0,k3_xboole_0(X21,k1_relat_1(sK1))) = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl80_11 ),
    inference(forward_demodulation,[],[f2283,f1483])).

fof(f1483,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2283,plain,
    ( ! [X21] : k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k3_xboole_0(X21,k1_relat_1(sK1)))
    | ~ spl80_11 ),
    inference(forward_demodulation,[],[f2282,f1486])).

fof(f1486,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f2282,plain,
    ( ! [X21] : k3_xboole_0(sK0,k3_xboole_0(X21,k1_relat_1(sK1))) = k3_xboole_0(sK0,k3_xboole_0(X21,k1_xboole_0))
    | ~ spl80_11 ),
    inference(forward_demodulation,[],[f2237,f1472])).

fof(f1472,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f2237,plain,
    ( ! [X21] : k3_xboole_0(sK0,k3_xboole_0(X21,k1_relat_1(sK1))) = k3_xboole_0(k3_xboole_0(sK0,X21),k1_xboole_0)
    | ~ spl80_11 ),
    inference(superposition,[],[f1470,f2063])).

fof(f2063,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_11 ),
    inference(avatar_component_clause,[],[f2062])).

fof(f1470,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_xboole_1)).

fof(f3917,plain,
    ( spl80_100
    | ~ spl80_29
    | ~ spl80_11 ),
    inference(avatar_split_clause,[],[f3852,f2062,f2268,f3915])).

fof(f3915,plain,
    ( spl80_100
  <=> ! [X11] : r1_xboole_0(k4_xboole_0(sK0,X11),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_100])])).

fof(f2268,plain,
    ( spl80_29
  <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_29])])).

fof(f3852,plain,
    ( ! [X11] :
        ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK1))
        | r1_xboole_0(k4_xboole_0(sK0,X11),k1_relat_1(sK1)) )
    | ~ spl80_11 ),
    inference(superposition,[],[f1316,f2287])).

fof(f2287,plain,
    ( ! [X26] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK0,X26),k1_relat_1(sK1))
    | ~ spl80_11 ),
    inference(forward_demodulation,[],[f2245,f1615])).

fof(f1615,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f2245,plain,
    ( ! [X26] : k3_xboole_0(k4_xboole_0(sK0,X26),k1_relat_1(sK1)) = k4_xboole_0(k1_xboole_0,k3_xboole_0(X26,k1_relat_1(sK1)))
    | ~ spl80_11 ),
    inference(superposition,[],[f1572,f2063])).

fof(f1572,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

fof(f1316,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f783])).

fof(f783,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f143])).

fof(f143,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f3913,plain,
    ( spl80_99
    | ~ spl80_11 ),
    inference(avatar_split_clause,[],[f3836,f2062,f3909])).

fof(f3909,plain,
    ( spl80_99
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_99])])).

fof(f3836,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_relat_1(sK1))
    | ~ spl80_11 ),
    inference(superposition,[],[f2287,f1612])).

fof(f1612,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f3912,plain,
    ( spl80_98
    | spl80_99
    | ~ spl80_11 ),
    inference(avatar_split_clause,[],[f3834,f2062,f3909,f3906])).

fof(f3906,plain,
    ( spl80_98
  <=> ! [X0] : ~ r1_tarski(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_98])])).

fof(f3834,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_relat_1(sK1))
        | ~ r1_tarski(sK0,X1) )
    | ~ spl80_11 ),
    inference(superposition,[],[f2287,f1595])).

fof(f1595,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1154])).

fof(f1154,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f97])).

fof(f97,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f3911,plain,
    ( spl80_98
    | spl80_99
    | ~ spl80_11 ),
    inference(avatar_split_clause,[],[f3833,f2062,f3909,f3906])).

fof(f3833,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_relat_1(sK1))
        | ~ r1_tarski(sK0,X0) )
    | ~ spl80_11 ),
    inference(superposition,[],[f2287,f1597])).

fof(f1597,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1155])).

fof(f1155,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f3793,plain,
    ( spl80_97
    | ~ spl80_33 ),
    inference(avatar_split_clause,[],[f3760,f2306,f3791])).

fof(f3791,plain,
    ( spl80_97
  <=> r1_tarski(k1_zfmisc_1(sK0),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_97])])).

fof(f2306,plain,
    ( spl80_33
  <=> sK0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_33])])).

fof(f3760,plain,
    ( r1_tarski(k1_zfmisc_1(sK0),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_relat_1(sK1)))))
    | ~ spl80_33 ),
    inference(superposition,[],[f1606,f2307])).

fof(f2307,plain,
    ( sK0 = k4_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_33 ),
    inference(avatar_component_clause,[],[f2306])).

fof(f1606,plain,(
    ! [X0,X1] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))) ),
    inference(cnf_transformation,[],[f438])).

fof(f438,axiom,(
    ! [X0,X1] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_zfmisc_1)).

fof(f3789,plain,
    ( ~ spl80_10
    | spl80_9
    | ~ spl80_33 ),
    inference(avatar_split_clause,[],[f3788,f2306,f2052,f2055])).

fof(f2055,plain,
    ( spl80_10
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_10])])).

fof(f2052,plain,
    ( spl80_9
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_9])])).

fof(f3788,plain,
    ( k1_xboole_0 != sK0
    | spl80_9
    | ~ spl80_33 ),
    inference(global_subsumption,[],[f3785])).

fof(f3785,plain,
    ( k1_xboole_0 != sK0
    | spl80_9
    | ~ spl80_33 ),
    inference(global_subsumption,[],[f2053,f3754])).

fof(f3754,plain,
    ( k1_xboole_0 != sK0
    | r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl80_33 ),
    inference(superposition,[],[f1594,f2307])).

fof(f1594,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1154])).

fof(f2053,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | spl80_9 ),
    inference(avatar_component_clause,[],[f2052])).

fof(f3787,plain,
    ( ~ spl80_10
    | spl80_9
    | ~ spl80_33 ),
    inference(avatar_split_clause,[],[f3785,f2306,f2052,f2055])).

fof(f3776,plain,
    ( spl80_96
    | ~ spl80_33 ),
    inference(avatar_split_clause,[],[f3730,f2306,f3774])).

fof(f3774,plain,
    ( spl80_96
  <=> r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_96])])).

fof(f3730,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK1),sK0))
    | ~ spl80_33 ),
    inference(superposition,[],[f1334,f2307])).

fof(f1334,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f152])).

fof(f152,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f3708,plain,
    ( ~ spl80_95
    | ~ spl80_2
    | spl80_13
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3704,f2787,f2098,f1991,f3706])).

fof(f3706,plain,
    ( spl80_95
  <=> r2_hidden(sK17(k1_xboole_0,k1_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_95])])).

fof(f1991,plain,
    ( spl80_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_2])])).

fof(f2098,plain,
    ( spl80_13
  <=> k1_xboole_0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_13])])).

fof(f2787,plain,
    ( spl80_63
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_63])])).

fof(f3704,plain,
    ( ~ r2_hidden(sK17(k1_xboole_0,k1_relat_1(sK1)),sK0)
    | ~ spl80_2
    | spl80_13
    | ~ spl80_63 ),
    inference(global_subsumption,[],[f2099,f3644])).

fof(f3644,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ r2_hidden(sK17(k1_xboole_0,k1_relat_1(sK1)),sK0)
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(resolution,[],[f3265,f2349])).

fof(f2349,plain,
    ( ! [X51] :
        ( r2_hidden(sK17(X51,k1_relat_1(sK1)),X51)
        | k1_relat_1(sK1) = X51
        | ~ r2_hidden(sK17(X51,k1_relat_1(sK1)),sK0) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1429])).

fof(f1429,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK17(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK17(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1104])).

fof(f1104,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK17(X0,X1),X1)
          | ~ r2_hidden(sK17(X0,X1),X0) )
        & ( r2_hidden(sK17(X0,X1),X1)
          | r2_hidden(sK17(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f1102,f1103])).

fof(f1103,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK17(X0,X1),X1)
          | ~ r2_hidden(sK17(X0,X1),X0) )
        & ( r2_hidden(sK17(X0,X1),X1)
          | r2_hidden(sK17(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1102,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f839])).

fof(f839,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f2198,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl80_2 ),
    inference(resolution,[],[f1995,f1329])).

fof(f1329,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f1061])).

fof(f1061,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f789,f1060])).

fof(f1060,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f789,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f741])).

fof(f741,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1995,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl80_2 ),
    inference(avatar_component_clause,[],[f1991])).

fof(f3265,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(global_subsumption,[],[f2198,f3263,f3264])).

fof(f3264,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl80_63 ),
    inference(global_subsumption,[],[f1280,f3234])).

fof(f3234,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | r2_hidden(X1,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl80_63 ),
    inference(superposition,[],[f1348,f2788])).

fof(f2788,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl80_63 ),
    inference(avatar_component_clause,[],[f2787])).

fof(f1348,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1071])).

fof(f1071,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1070])).

fof(f1070,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f797])).

fof(f797,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f730])).

fof(f730,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f3263,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,sK0) )
    | ~ spl80_63 ),
    inference(global_subsumption,[],[f1280,f3233])).

fof(f3233,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl80_63 ),
    inference(superposition,[],[f1347,f2788])).

fof(f1347,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1071])).

fof(f2099,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | spl80_13 ),
    inference(avatar_component_clause,[],[f2098])).

fof(f3696,plain,
    ( spl80_94
    | spl80_93
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3625,f2787,f1991,f3689,f3693])).

fof(f3693,plain,
    ( spl80_94
  <=> ! [X20,X21] : k4_tarski(X20,X21) != sK43(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_94])])).

fof(f3689,plain,
    ( spl80_93
  <=> ! [X16,X18,X17] :
        ( k1_xboole_0 = X16
        | k4_tarski(X17,X18) != sK44(X16)
        | r2_hidden(k4_tarski(sK41(X16,k1_xboole_0),sK42(X16,k1_xboole_0)),X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_93])])).

fof(f3625,plain,
    ( ! [X26,X24,X23,X25,X22] :
        ( k1_xboole_0 = X22
        | r2_hidden(k4_tarski(sK41(X22,k1_xboole_0),sK42(X22,k1_xboole_0)),X22)
        | k4_tarski(X23,X24) != sK43(k1_xboole_0)
        | k4_tarski(X25,X26) != sK44(X22) )
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(resolution,[],[f3265,f1665])).

fof(f1665,plain,(
    ! [X6,X0,X8,X5,X1,X9] :
      ( r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X1)
      | X0 = X1
      | r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK43(X1)
      | k4_tarski(X8,X9) != sK44(X0) ) ),
    inference(cnf_transformation,[],[f1193])).

fof(f1193,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X0) ) )
      | ( ! [X5,X6] : k4_tarski(X5,X6) != sK43(X1)
        & r2_hidden(sK43(X1),X1) )
      | ( ! [X8,X9] : k4_tarski(X8,X9) != sK44(X0)
        & r2_hidden(sK44(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK41,sK42,sK43,sK44])],[f1189,f1192,f1191,f1190])).

fof(f1190,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1191,plain,(
    ! [X1] :
      ( ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
     => ( ! [X6,X5] : k4_tarski(X5,X6) != sK43(X1)
        & r2_hidden(sK43(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1192,plain,(
    ! [X0] :
      ( ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) )
     => ( ! [X9,X8] : k4_tarski(X8,X9) != sK44(X0)
        & r2_hidden(sK44(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1189,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(nnf_transformation,[],[f924])).

fof(f924,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X0)
        <~> r2_hidden(k4_tarski(X2,X3),X1) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(flattening,[],[f923])).

fof(f923,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X0)
        <~> r2_hidden(k4_tarski(X2,X3),X1) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(ennf_transformation,[],[f745])).

fof(f745,plain,(
    ! [X0,X1] :
      ( ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X0)
          <=> r2_hidden(k4_tarski(X2,X3),X1) )
        & ! [X4] :
            ~ ( ! [X5,X6] : k4_tarski(X5,X6) != X4
              & r2_hidden(X4,X1) )
        & ! [X7] :
            ~ ( ! [X8,X9] : k4_tarski(X8,X9) != X7
              & r2_hidden(X7,X0) ) )
     => X0 = X1 ) ),
    inference(rectify,[],[f299])).

fof(f299,axiom,(
    ! [X0,X1] :
      ( ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X0)
          <=> r2_hidden(k4_tarski(X2,X3),X1) )
        & ! [X2] :
            ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X2
              & r2_hidden(X2,X1) )
        & ! [X2] :
            ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X2
              & r2_hidden(X2,X0) ) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l131_zfmisc_1)).

fof(f3695,plain,
    ( spl80_94
    | spl80_92
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3624,f2787,f1991,f3685,f3693])).

fof(f3685,plain,
    ( spl80_92
  <=> ! [X15] :
        ( k1_xboole_0 = X15
        | r2_hidden(sK44(X15),X15)
        | r2_hidden(k4_tarski(sK41(X15,k1_xboole_0),sK42(X15,k1_xboole_0)),X15) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_92])])).

fof(f3624,plain,
    ( ! [X21,X19,X20] :
        ( k1_xboole_0 = X19
        | r2_hidden(k4_tarski(sK41(X19,k1_xboole_0),sK42(X19,k1_xboole_0)),X19)
        | k4_tarski(X20,X21) != sK43(k1_xboole_0)
        | r2_hidden(sK44(X19),X19) )
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(resolution,[],[f3265,f1664])).

fof(f1664,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X1)
      | X0 = X1
      | r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK43(X1)
      | r2_hidden(sK44(X0),X0) ) ),
    inference(cnf_transformation,[],[f1193])).

fof(f3691,plain,
    ( spl80_91
    | spl80_93
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3623,f2787,f1991,f3689,f3682])).

fof(f3682,plain,
    ( spl80_91
  <=> r2_hidden(sK43(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_91])])).

fof(f3623,plain,
    ( ! [X17,X18,X16] :
        ( k1_xboole_0 = X16
        | r2_hidden(k4_tarski(sK41(X16,k1_xboole_0),sK42(X16,k1_xboole_0)),X16)
        | r2_hidden(sK43(k1_xboole_0),k1_xboole_0)
        | k4_tarski(X17,X18) != sK44(X16) )
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(resolution,[],[f3265,f1663])).

fof(f1663,plain,(
    ! [X0,X8,X1,X9] :
      ( r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X1)
      | X0 = X1
      | r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X0)
      | r2_hidden(sK43(X1),X1)
      | k4_tarski(X8,X9) != sK44(X0) ) ),
    inference(cnf_transformation,[],[f1193])).

fof(f3687,plain,
    ( spl80_91
    | spl80_92
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3622,f2787,f1991,f3685,f3682])).

fof(f3622,plain,
    ( ! [X15] :
        ( k1_xboole_0 = X15
        | r2_hidden(k4_tarski(sK41(X15,k1_xboole_0),sK42(X15,k1_xboole_0)),X15)
        | r2_hidden(sK43(k1_xboole_0),k1_xboole_0)
        | r2_hidden(sK44(X15),X15) )
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(resolution,[],[f3265,f1662])).

fof(f1662,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X1)
      | X0 = X1
      | r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X0)
      | r2_hidden(sK43(X1),X1)
      | r2_hidden(sK44(X0),X0) ) ),
    inference(cnf_transformation,[],[f1193])).

fof(f3680,plain,
    ( spl80_89
    | spl80_90
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3621,f2787,f1991,f3678,f3675])).

fof(f3675,plain,
    ( spl80_89
  <=> ! [X11,X12] : ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X11,X12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_89])])).

fof(f3678,plain,
    ( spl80_90
  <=> ! [X13,X10,X14] :
        ( k1_xboole_0 = X10
        | ~ r1_tarski(X10,k2_zfmisc_1(X13,X14))
        | r2_hidden(k4_tarski(sK23(X10,k1_xboole_0),sK24(X10,k1_xboole_0)),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_90])])).

fof(f3621,plain,
    ( ! [X14,X12,X10,X13,X11] :
        ( k1_xboole_0 = X10
        | r2_hidden(k4_tarski(sK23(X10,k1_xboole_0),sK24(X10,k1_xboole_0)),X10)
        | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X11,X12))
        | ~ r1_tarski(X10,k2_zfmisc_1(X13,X14)) )
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(resolution,[],[f3265,f1616])).

fof(f1616,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k4_tarski(sK23(X0,X3),sK24(X0,X3)),X3)
      | X0 = X3
      | r2_hidden(k4_tarski(sK23(X0,X3),sK24(X0,X3)),X0)
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f1158])).

fof(f1158,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( X0 = X3
      | ( ( ~ r2_hidden(k4_tarski(sK23(X0,X3),sK24(X0,X3)),X3)
          | ~ r2_hidden(k4_tarski(sK23(X0,X3),sK24(X0,X3)),X0) )
        & ( r2_hidden(k4_tarski(sK23(X0,X3),sK24(X0,X3)),X3)
          | r2_hidden(k4_tarski(sK23(X0,X3),sK24(X0,X3)),X0) ) )
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23,sK24])],[f1156,f1157])).

fof(f1157,plain,(
    ! [X3,X0] :
      ( ? [X6,X7] :
          ( ( ~ r2_hidden(k4_tarski(X6,X7),X3)
            | ~ r2_hidden(k4_tarski(X6,X7),X0) )
          & ( r2_hidden(k4_tarski(X6,X7),X3)
            | r2_hidden(k4_tarski(X6,X7),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK23(X0,X3),sK24(X0,X3)),X3)
          | ~ r2_hidden(k4_tarski(sK23(X0,X3),sK24(X0,X3)),X0) )
        & ( r2_hidden(k4_tarski(sK23(X0,X3),sK24(X0,X3)),X3)
          | r2_hidden(k4_tarski(sK23(X0,X3),sK24(X0,X3)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1156,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( X0 = X3
      | ? [X6,X7] :
          ( ( ~ r2_hidden(k4_tarski(X6,X7),X3)
            | ~ r2_hidden(k4_tarski(X6,X7),X0) )
          & ( r2_hidden(k4_tarski(X6,X7),X3)
            | r2_hidden(k4_tarski(X6,X7),X0) ) )
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(nnf_transformation,[],[f914])).

fof(f914,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( X0 = X3
      | ? [X6,X7] :
          ( r2_hidden(k4_tarski(X6,X7),X0)
        <~> r2_hidden(k4_tarski(X6,X7),X3) )
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(flattening,[],[f913])).

fof(f913,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( X0 = X3
      | ? [X6,X7] :
          ( r2_hidden(k4_tarski(X6,X7),X0)
        <~> r2_hidden(k4_tarski(X6,X7),X3) )
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f298])).

fof(f298,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ! [X6,X7] :
            ( r2_hidden(k4_tarski(X6,X7),X0)
          <=> r2_hidden(k4_tarski(X6,X7),X3) )
        & r1_tarski(X3,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) )
     => X0 = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l130_zfmisc_1)).

fof(f3612,plain,
    ( ~ spl80_88
    | ~ spl80_11
    | spl80_28 ),
    inference(avatar_split_clause,[],[f3611,f2205,f2062,f3608])).

fof(f3608,plain,
    ( spl80_88
  <=> r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_88])])).

fof(f2205,plain,
    ( spl80_28
  <=> r1_tarski(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_28])])).

fof(f3611,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | ~ spl80_11
    | spl80_28 ),
    inference(global_subsumption,[],[f3599])).

fof(f3599,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | ~ spl80_11
    | spl80_28 ),
    inference(resolution,[],[f2230,f2206])).

fof(f2206,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | spl80_28 ),
    inference(avatar_component_clause,[],[f2205])).

fof(f2230,plain,
    ( ! [X14] :
        ( r1_tarski(X14,sK0)
        | ~ r1_tarski(X14,k1_xboole_0) )
    | ~ spl80_11 ),
    inference(superposition,[],[f1463,f2063])).

fof(f1463,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f858])).

fof(f858,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f74])).

fof(f74,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f3610,plain,
    ( ~ spl80_88
    | ~ spl80_11
    | spl80_28 ),
    inference(avatar_split_clause,[],[f3599,f2205,f2062,f3608])).

fof(f3561,plain,
    ( spl80_87
    | ~ spl80_83 ),
    inference(avatar_split_clause,[],[f3557,f3342,f3559])).

fof(f3559,plain,
    ( spl80_87
  <=> r1_tarski(k2_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_87])])).

fof(f3342,plain,
    ( spl80_83
  <=> sK0 = k2_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_83])])).

fof(f3557,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl80_83 ),
    inference(forward_demodulation,[],[f3493,f1397])).

fof(f1397,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f3493,plain,
    ( r1_tarski(k2_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl80_83 ),
    inference(superposition,[],[f1785,f3343])).

fof(f3343,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl80_83 ),
    inference(avatar_component_clause,[],[f3342])).

fof(f1785,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f435])).

fof(f435,axiom,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

fof(f3556,plain,
    ( spl80_84
    | ~ spl80_83 ),
    inference(avatar_split_clause,[],[f3555,f3342,f3512])).

fof(f3512,plain,
    ( spl80_84
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_84])])).

fof(f3555,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl80_83 ),
    inference(forward_demodulation,[],[f3489,f1615])).

fof(f3489,plain,
    ( k4_xboole_0(sK0,sK0) = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl80_83 ),
    inference(superposition,[],[f1610,f3343])).

fof(f1610,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f3554,plain,
    ( spl80_86
    | ~ spl80_83 ),
    inference(avatar_split_clause,[],[f3550,f3342,f3552])).

fof(f3552,plain,
    ( spl80_86
  <=> sK0 = k4_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_86])])).

fof(f3550,plain,
    ( sK0 = k4_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK0))
    | ~ spl80_83 ),
    inference(forward_demodulation,[],[f3549,f1394])).

fof(f1394,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f3549,plain,
    ( k2_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK0))
    | ~ spl80_83 ),
    inference(forward_demodulation,[],[f3548,f1608])).

fof(f1608,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f3548,plain,
    ( k4_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK0)) = k2_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK0))
    | ~ spl80_83 ),
    inference(forward_demodulation,[],[f3547,f1421])).

fof(f1421,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3547,plain,
    ( k4_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,sK0),sK0)
    | ~ spl80_83 ),
    inference(forward_demodulation,[],[f3488,f1614])).

fof(f1614,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f3488,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK0))
    | ~ spl80_83 ),
    inference(superposition,[],[f1605,f3343])).

fof(f1605,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f3545,plain,
    ( spl80_85
    | ~ spl80_83 ),
    inference(avatar_split_clause,[],[f3486,f3342,f3543])).

fof(f3486,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl80_83 ),
    inference(superposition,[],[f1482,f3343])).

fof(f1482,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f3514,plain,
    ( spl80_84
    | ~ spl80_30
    | ~ spl80_33
    | ~ spl80_83 ),
    inference(avatar_split_clause,[],[f3510,f3342,f2306,f2278,f3512])).

fof(f2278,plain,
    ( spl80_30
  <=> r1_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_30])])).

fof(f3510,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl80_30
    | ~ spl80_33
    | ~ spl80_83 ),
    inference(global_subsumption,[],[f3346,f3457])).

fof(f3457,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ r1_xboole_0(k1_xboole_0,sK0)
    | ~ spl80_83 ),
    inference(superposition,[],[f1321,f3343])).

fof(f1321,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f784])).

fof(f784,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f158])).

fof(f158,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f3346,plain,
    ( r1_xboole_0(k1_xboole_0,sK0)
    | ~ spl80_30
    | ~ spl80_33 ),
    inference(forward_demodulation,[],[f2279,f2307])).

fof(f2279,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl80_30 ),
    inference(avatar_component_clause,[],[f2278])).

fof(f3353,plain,
    ( spl80_83
    | ~ spl80_11
    | ~ spl80_33 ),
    inference(avatar_split_clause,[],[f3352,f2306,f2062,f3342])).

fof(f3352,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl80_11
    | ~ spl80_33 ),
    inference(forward_demodulation,[],[f2252,f2307])).

fof(f2252,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl80_11 ),
    inference(superposition,[],[f1607,f2063])).

fof(f1607,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f115])).

fof(f115,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f3351,plain,
    ( spl80_6
    | ~ spl80_11
    | ~ spl80_33 ),
    inference(avatar_split_clause,[],[f3350,f2306,f2062,f2014])).

fof(f2014,plain,
    ( spl80_6
  <=> r1_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_6])])).

fof(f3350,plain,
    ( r1_xboole_0(k1_xboole_0,sK0)
    | ~ spl80_11
    | ~ spl80_33 ),
    inference(forward_demodulation,[],[f2223,f2307])).

fof(f2223,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl80_11 ),
    inference(superposition,[],[f1333,f2063])).

fof(f1333,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f159])).

fof(f159,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_xboole_1)).

fof(f3348,plain,
    ( spl80_6
    | ~ spl80_30
    | ~ spl80_33 ),
    inference(avatar_split_clause,[],[f3346,f2306,f2278,f2014])).

fof(f3344,plain,
    ( spl80_83
    | ~ spl80_32
    | ~ spl80_33 ),
    inference(avatar_split_clause,[],[f3340,f2306,f2301,f3342])).

fof(f2301,plain,
    ( spl80_32
  <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_32])])).

fof(f3340,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl80_32
    | ~ spl80_33 ),
    inference(forward_demodulation,[],[f2302,f2307])).

fof(f2302,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl80_32 ),
    inference(avatar_component_clause,[],[f2301])).

fof(f3338,plain,
    ( ~ spl80_69
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3337,f2787,f1991,f3273])).

fof(f3337,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(global_subsumption,[],[f3334])).

fof(f3334,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(global_subsumption,[],[f3330])).

fof(f3330,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(global_subsumption,[],[f1282,f1995,f3259])).

fof(f3259,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl80_63 ),
    inference(trivial_inequality_removal,[],[f3254])).

fof(f3254,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl80_63 ),
    inference(superposition,[],[f1890,f2788])).

fof(f1890,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1051])).

fof(f1051,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1050])).

fof(f1050,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f714])).

fof(f714,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1282,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f1057])).

fof(f3335,plain,
    ( ~ spl80_69
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3334,f2787,f1991,f3273])).

fof(f3331,plain,
    ( ~ spl80_69
    | ~ spl80_2
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3330,f2787,f1991,f3273])).

fof(f3329,plain,
    ( ~ spl80_69
    | spl80_82
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3253,f2787,f3327,f3273])).

fof(f3327,plain,
    ( spl80_82
  <=> ! [X15] :
        ( r1_tarski(k1_relat_1(X15),k1_xboole_0)
        | ~ v1_relat_1(X15)
        | ~ r1_tarski(X15,k7_relat_1(sK1,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_82])])).

fof(f3253,plain,
    ( ! [X15] :
        ( r1_tarski(k1_relat_1(X15),k1_xboole_0)
        | ~ r1_tarski(X15,k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(X15) )
    | ~ spl80_63 ),
    inference(superposition,[],[f1883,f2788])).

fof(f1883,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1045])).

fof(f1045,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1044])).

fof(f1044,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f684])).

fof(f684,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f3325,plain,
    ( ~ spl80_69
    | spl80_81
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3251,f2787,f3323,f3273])).

fof(f3323,plain,
    ( spl80_81
  <=> ! [X13] :
        ( ~ r1_xboole_0(k2_relat_1(X13),k1_xboole_0)
        | ~ v1_relat_1(X13)
        | k1_xboole_0 = k5_relat_1(X13,k7_relat_1(sK1,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_81])])).

fof(f3251,plain,
    ( ! [X13] :
        ( ~ r1_xboole_0(k2_relat_1(X13),k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(X13,k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(X13) )
    | ~ spl80_63 ),
    inference(superposition,[],[f1882,f2788])).

fof(f1882,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
      | k1_xboole_0 = k5_relat_1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1043])).

fof(f1043,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1042])).

fof(f1042,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f717])).

fof(f717,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
           => k1_xboole_0 = k5_relat_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

fof(f3321,plain,
    ( ~ spl80_69
    | spl80_79
    | spl80_80
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3250,f2787,f3319,f3316,f3273])).

fof(f3316,plain,
    ( spl80_79
  <=> ! [X12] : ~ r2_hidden(X12,k2_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_79])])).

fof(f3319,plain,
    ( spl80_80
  <=> r2_hidden(sK79(k7_relat_1(sK1,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_80])])).

fof(f3250,plain,
    ( ! [X12] :
        ( r2_hidden(sK79(k7_relat_1(sK1,sK0)),k1_xboole_0)
        | ~ r2_hidden(X12,k2_relat_1(k7_relat_1(sK1,sK0)))
        | ~ v1_relat_1(k7_relat_1(sK1,sK0)) )
    | ~ spl80_63 ),
    inference(superposition,[],[f1877,f2788])).

fof(f1877,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK79(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1278])).

fof(f1278,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK79(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK79])],[f1034,f1277])).

fof(f1277,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK79(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f1034,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1033])).

fof(f1033,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f678])).

fof(f678,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f3314,plain,
    ( ~ spl80_69
    | spl80_78
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3310,f2787,f3312,f3273])).

fof(f3312,plain,
    ( spl80_78
  <=> k7_relat_1(sK1,sK0) = k5_relat_1(k1_xboole_0,k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_78])])).

fof(f3310,plain,
    ( k7_relat_1(sK1,sK0) = k5_relat_1(k1_xboole_0,k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl80_63 ),
    inference(forward_demodulation,[],[f3249,f1759])).

fof(f1759,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f728])).

fof(f728,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f3249,plain,
    ( k7_relat_1(sK1,sK0) = k5_relat_1(k6_relat_1(k1_xboole_0),k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl80_63 ),
    inference(superposition,[],[f1754,f2788])).

fof(f1754,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f977])).

fof(f977,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f725])).

fof(f725,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f3309,plain,
    ( ~ spl80_69
    | spl80_77
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3305,f2787,f3307,f3273])).

fof(f3307,plain,
    ( spl80_77
  <=> ! [X9,X11,X10] :
        ( k1_xboole_0 != k5_relat_1(X9,X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X10)
        | ~ r1_tarski(k2_relat_1(X9),X11)
        | k7_relat_1(sK1,sK0) = X9
        | k6_relat_1(X11) != k5_relat_1(X10,k7_relat_1(sK1,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_77])])).

% (7604)Time limit reached!
% (7604)------------------------------
% (7604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f3305,plain,
    ( ! [X10,X11,X9] :
        ( k1_xboole_0 != k5_relat_1(X9,X10)
        | k6_relat_1(X11) != k5_relat_1(X10,k7_relat_1(sK1,sK0))
        | k7_relat_1(sK1,sK0) = X9
        | ~ r1_tarski(k2_relat_1(X9),X11)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9) )
    | ~ spl80_63 ),
    inference(forward_demodulation,[],[f3248,f1759])).

fof(f3248,plain,
    ( ! [X10,X11,X9] :
        ( k6_relat_1(k1_xboole_0) != k5_relat_1(X9,X10)
        | k6_relat_1(X11) != k5_relat_1(X10,k7_relat_1(sK1,sK0))
        | k7_relat_1(sK1,sK0) = X9
        | ~ r1_tarski(k2_relat_1(X9),X11)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9) )
    | ~ spl80_63 ),
    inference(superposition,[],[f1741,f2788])).

fof(f1741,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k6_relat_1(X0) != k5_relat_1(X2,X3)
      | X1 = X3
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f968])).

fof(f968,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | ~ r1_tarski(k2_relat_1(X1),X0)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f967])).

fof(f967,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | ~ r1_tarski(k2_relat_1(X1),X0)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f729])).

fof(f729,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & r1_tarski(k2_relat_1(X1),X0) )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_relat_1)).

fof(f3304,plain,
    ( ~ spl80_69
    | spl80_76
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3247,f2787,f3302,f3273])).

fof(f3302,plain,
    ( spl80_76
  <=> ! [X8] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK1,sK0),X8)),k1_xboole_0)
        | ~ v1_relat_1(X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_76])])).

fof(f3247,plain,
    ( ! [X8] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK1,sK0),X8)),k1_xboole_0)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0)) )
    | ~ spl80_63 ),
    inference(superposition,[],[f1732,f2788])).

fof(f1732,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f963])).

fof(f963,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f698])).

fof(f698,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f3300,plain,
    ( ~ spl80_69
    | spl80_75
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3246,f2787,f3298,f3273])).

fof(f3298,plain,
    ( spl80_75
  <=> ! [X7] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X7)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_75])])).

fof(f3246,plain,
    ( ! [X7] :
        ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X7)),k1_xboole_0)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0)) )
    | ~ spl80_63 ),
    inference(superposition,[],[f1357,f2788])).

fof(f1357,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f806])).

fof(f806,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f733])).

fof(f733,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f3296,plain,
    ( ~ spl80_69
    | spl80_74
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3292,f2787,f3294,f3273])).

fof(f3294,plain,
    ( spl80_74
  <=> ! [X6] :
        ( k1_relat_1(k2_xboole_0(X6,k7_relat_1(sK1,sK0))) = k1_relat_1(X6)
        | ~ v1_relat_1(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_74])])).

fof(f3292,plain,
    ( ! [X6] :
        ( k1_relat_1(k2_xboole_0(X6,k7_relat_1(sK1,sK0))) = k1_relat_1(X6)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(X6) )
    | ~ spl80_63 ),
    inference(forward_demodulation,[],[f3245,f1394])).

fof(f3245,plain,
    ( ! [X6] :
        ( k1_relat_1(k2_xboole_0(X6,k7_relat_1(sK1,sK0))) = k2_xboole_0(k1_relat_1(X6),k1_xboole_0)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(X6) )
    | ~ spl80_63 ),
    inference(superposition,[],[f1346,f2788])).

fof(f1346,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f796])).

fof(f796,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f674])).

fof(f674,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(f3291,plain,
    ( ~ spl80_69
    | spl80_73
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3244,f2787,f3289,f3273])).

fof(f3289,plain,
    ( spl80_73
  <=> ! [X5] :
        ( k1_relat_1(k2_xboole_0(k7_relat_1(sK1,sK0),X5)) = k2_xboole_0(k1_xboole_0,k1_relat_1(X5))
        | ~ v1_relat_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_73])])).

fof(f3244,plain,
    ( ! [X5] :
        ( k1_relat_1(k2_xboole_0(k7_relat_1(sK1,sK0),X5)) = k2_xboole_0(k1_xboole_0,k1_relat_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0)) )
    | ~ spl80_63 ),
    inference(superposition,[],[f1346,f2788])).

fof(f3287,plain,
    ( ~ spl80_69
    | spl80_72
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3283,f2787,f3285,f3273])).

fof(f3285,plain,
    ( spl80_72
  <=> ! [X4] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(X4,k7_relat_1(sK1,sK0))),k3_xboole_0(k1_xboole_0,k1_relat_1(X4)))
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_72])])).

fof(f3283,plain,
    ( ! [X4] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(X4,k7_relat_1(sK1,sK0))),k3_xboole_0(k1_xboole_0,k1_relat_1(X4)))
        | ~ v1_relat_1(k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(X4) )
    | ~ spl80_63 ),
    inference(forward_demodulation,[],[f3243,f1483])).

fof(f3243,plain,
    ( ! [X4] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(X4,k7_relat_1(sK1,sK0))),k3_xboole_0(k1_relat_1(X4),k1_xboole_0))
        | ~ v1_relat_1(k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(X4) )
    | ~ spl80_63 ),
    inference(superposition,[],[f1345,f2788])).

fof(f1345,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f795])).

fof(f795,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f675])).

fof(f675,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f3282,plain,
    ( ~ spl80_69
    | spl80_71
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3242,f2787,f3280,f3273])).

fof(f3280,plain,
    ( spl80_71
  <=> ! [X3] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(k7_relat_1(sK1,sK0),X3)),k3_xboole_0(k1_xboole_0,k1_relat_1(X3)))
        | ~ v1_relat_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_71])])).

fof(f3242,plain,
    ( ! [X3] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(k7_relat_1(sK1,sK0),X3)),k3_xboole_0(k1_xboole_0,k1_relat_1(X3)))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0)) )
    | ~ spl80_63 ),
    inference(superposition,[],[f1345,f2788])).

fof(f3278,plain,
    ( spl80_68
    | ~ spl80_69
    | ~ spl80_70
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3240,f2787,f3276,f3273,f3270])).

fof(f3270,plain,
    ( spl80_68
  <=> v1_xboole_0(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_68])])).

fof(f3276,plain,
    ( spl80_70
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_70])])).

fof(f3240,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | v1_xboole_0(k7_relat_1(sK1,sK0))
    | ~ spl80_63 ),
    inference(superposition,[],[f1343,f2788])).

fof(f1343,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f793])).

fof(f793,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f792])).

fof(f792,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f670])).

fof(f670,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f3268,plain,
    ( spl80_11
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3267,f2787,f2062])).

fof(f3267,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_63 ),
    inference(global_subsumption,[],[f3261])).

fof(f3261,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_63 ),
    inference(global_subsumption,[],[f1280,f3260])).

fof(f3260,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl80_63 ),
    inference(forward_demodulation,[],[f3228,f1483])).

fof(f3228,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl80_63 ),
    inference(superposition,[],[f2788,f1355])).

fof(f1355,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f804])).

fof(f804,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f734])).

fof(f734,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f3262,plain,
    ( spl80_11
    | ~ spl80_63 ),
    inference(avatar_split_clause,[],[f3261,f2787,f2062])).

fof(f3188,plain,
    ( ~ spl80_67
    | ~ spl80_16 ),
    inference(avatar_split_clause,[],[f3184,f2148,f3186])).

fof(f3186,plain,
    ( spl80_67
  <=> r2_hidden(sK0,sK43(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_67])])).

fof(f2148,plain,
    ( spl80_16
  <=> r2_hidden(sK43(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_16])])).

fof(f3184,plain,
    ( ~ r2_hidden(sK0,sK43(sK0))
    | ~ spl80_16 ),
    inference(resolution,[],[f2149,f1431])).

fof(f1431,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f840])).

fof(f840,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f2149,plain,
    ( r2_hidden(sK43(sK0),sK0)
    | ~ spl80_16 ),
    inference(avatar_component_clause,[],[f2148])).

fof(f3181,plain,
    ( spl80_19
    | spl80_66
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f3149,f1991,f3177,f2159])).

fof(f2159,plain,
    ( spl80_19
  <=> ! [X18,X17] : sK43(sK0) != k4_tarski(X17,X18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_19])])).

fof(f3177,plain,
    ( spl80_66
  <=> ! [X27,X29,X26,X28] :
        ( ~ r2_hidden(k4_tarski(sK41(X26,sK0),sK42(X26,sK0)),X27)
        | k4_tarski(X28,X29) != sK44(X26)
        | r2_hidden(k4_tarski(sK41(X26,sK0),sK42(X26,sK0)),X26)
        | sK0 = X26
        | ~ v1_relat_1(X27)
        | ~ r1_tarski(X27,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_66])])).

fof(f3149,plain,
    ( ! [X39,X37,X35,X38,X36,X34] :
        ( ~ r2_hidden(k4_tarski(sK41(X34,sK0),sK42(X34,sK0)),X35)
        | ~ r1_tarski(X35,k1_relat_1(sK1))
        | ~ v1_relat_1(X35)
        | sK0 = X34
        | r2_hidden(k4_tarski(sK41(X34,sK0),sK42(X34,sK0)),X34)
        | sK43(sK0) != k4_tarski(X36,X37)
        | k4_tarski(X38,X39) != sK44(X34) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2339,f1665])).

fof(f2339,plain,
    ( ! [X39,X41,X40] :
        ( ~ r2_hidden(k4_tarski(X39,X40),sK0)
        | ~ r2_hidden(k4_tarski(X39,X40),X41)
        | ~ r1_tarski(X41,k1_relat_1(sK1))
        | ~ v1_relat_1(X41) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1676])).

fof(f1676,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1202])).

fof(f1202,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK48(X0,X1),sK49(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK48(X0,X1),sK49(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK48,sK49])],[f1200,f1201])).

fof(f1201,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK48(X0,X1),sK49(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK48(X0,X1),sK49(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1200,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1199])).

fof(f1199,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f926])).

fof(f926,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f644])).

fof(f644,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f3180,plain,
    ( spl80_19
    | spl80_65
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f3148,f1991,f3173,f2159])).

fof(f3173,plain,
    ( spl80_65
  <=> ! [X25,X24] :
        ( ~ r2_hidden(k4_tarski(sK41(X24,sK0),sK42(X24,sK0)),X25)
        | r2_hidden(sK44(X24),X24)
        | r2_hidden(k4_tarski(sK41(X24,sK0),sK42(X24,sK0)),X24)
        | sK0 = X24
        | ~ v1_relat_1(X25)
        | ~ r1_tarski(X25,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_65])])).

fof(f3148,plain,
    ( ! [X30,X33,X31,X32] :
        ( ~ r2_hidden(k4_tarski(sK41(X30,sK0),sK42(X30,sK0)),X31)
        | ~ r1_tarski(X31,k1_relat_1(sK1))
        | ~ v1_relat_1(X31)
        | sK0 = X30
        | r2_hidden(k4_tarski(sK41(X30,sK0),sK42(X30,sK0)),X30)
        | sK43(sK0) != k4_tarski(X32,X33)
        | r2_hidden(sK44(X30),X30) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2339,f1664])).

fof(f3179,plain,
    ( spl80_16
    | spl80_66
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f3147,f1991,f3177,f2148])).

fof(f3147,plain,
    ( ! [X28,X26,X29,X27] :
        ( ~ r2_hidden(k4_tarski(sK41(X26,sK0),sK42(X26,sK0)),X27)
        | ~ r1_tarski(X27,k1_relat_1(sK1))
        | ~ v1_relat_1(X27)
        | sK0 = X26
        | r2_hidden(k4_tarski(sK41(X26,sK0),sK42(X26,sK0)),X26)
        | r2_hidden(sK43(sK0),sK0)
        | k4_tarski(X28,X29) != sK44(X26) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2339,f1663])).

fof(f3175,plain,
    ( spl80_16
    | spl80_65
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f3146,f1991,f3173,f2148])).

fof(f3146,plain,
    ( ! [X24,X25] :
        ( ~ r2_hidden(k4_tarski(sK41(X24,sK0),sK42(X24,sK0)),X25)
        | ~ r1_tarski(X25,k1_relat_1(sK1))
        | ~ v1_relat_1(X25)
        | sK0 = X24
        | r2_hidden(k4_tarski(sK41(X24,sK0),sK42(X24,sK0)),X24)
        | r2_hidden(sK43(sK0),sK0)
        | r2_hidden(sK44(X24),X24) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2339,f1662])).

fof(f3171,plain,
    ( spl80_14
    | spl80_64
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f3145,f1991,f3169,f2141])).

fof(f2141,plain,
    ( spl80_14
  <=> ! [X9,X8] : ~ r1_tarski(sK0,k2_zfmisc_1(X8,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_14])])).

fof(f3169,plain,
    ( spl80_64
  <=> ! [X18,X22,X19,X23] :
        ( ~ r2_hidden(k4_tarski(sK23(X18,sK0),sK24(X18,sK0)),X19)
        | ~ r1_tarski(X18,k2_zfmisc_1(X22,X23))
        | r2_hidden(k4_tarski(sK23(X18,sK0),sK24(X18,sK0)),X18)
        | sK0 = X18
        | ~ v1_relat_1(X19)
        | ~ r1_tarski(X19,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_64])])).

fof(f3145,plain,
    ( ! [X23,X21,X19,X22,X20,X18] :
        ( ~ r2_hidden(k4_tarski(sK23(X18,sK0),sK24(X18,sK0)),X19)
        | ~ r1_tarski(X19,k1_relat_1(sK1))
        | ~ v1_relat_1(X19)
        | sK0 = X18
        | r2_hidden(k4_tarski(sK23(X18,sK0),sK24(X18,sK0)),X18)
        | ~ r1_tarski(sK0,k2_zfmisc_1(X20,X21))
        | ~ r1_tarski(X18,k2_zfmisc_1(X22,X23)) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2339,f1616])).

fof(f2789,plain,
    ( spl80_63
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2785,f1991,f2787])).

fof(f2785,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl80_2 ),
    inference(global_subsumption,[],[f1280,f2780])).

fof(f2780,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl80_2 ),
    inference(resolution,[],[f2527,f1358])).

fof(f1358,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f807])).

fof(f807,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f731])).

fof(f731,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f2527,plain,
    ( ! [X17] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X17)),sK0)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X17)) )
    | ~ spl80_2 ),
    inference(global_subsumption,[],[f1280,f2517])).

fof(f2517,plain,
    ( ! [X17] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X17)),sK0)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X17))
        | ~ v1_relat_1(sK1) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2199,f1357])).

fof(f2199,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k1_relat_1(sK1))
        | ~ r1_tarski(X2,sK0)
        | k1_xboole_0 = X2 )
    | ~ spl80_2 ),
    inference(resolution,[],[f1995,f1299])).

fof(f1299,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f767])).

fof(f767,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f766])).

fof(f766,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f133])).

fof(f133,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f2685,plain,
    ( spl80_62
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2681,f1991,f2683])).

fof(f2683,plain,
    ( spl80_62
  <=> v1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_62])])).

fof(f2681,plain,
    ( v1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl80_2 ),
    inference(global_subsumption,[],[f1280,f2676])).

fof(f2676,plain,
    ( v1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl80_2 ),
    inference(resolution,[],[f2500,f1358])).

fof(f2500,plain,
    ( ! [X17] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X17)),sK0)
        | v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X17))) )
    | ~ spl80_2 ),
    inference(global_subsumption,[],[f1280,f2490])).

fof(f2490,plain,
    ( ! [X17] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X17)),sK0)
        | v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X17)))
        | ~ v1_relat_1(sK1) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2197,f1357])).

fof(f2197,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | ~ r1_tarski(X0,sK0)
        | v1_xboole_0(X0) )
    | ~ spl80_2 ),
    inference(resolution,[],[f1995,f1690])).

fof(f1690,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f932])).

fof(f932,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f931])).

fof(f931,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f134])).

fof(f134,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f2624,plain,(
    spl80_60 ),
    inference(avatar_contradiction_clause,[],[f2617])).

fof(f2617,plain,
    ( $false
    | spl80_60 ),
    inference(resolution,[],[f2553,f1338])).

fof(f1338,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f2553,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),k1_xboole_0)
    | spl80_60 ),
    inference(avatar_component_clause,[],[f2552])).

fof(f2552,plain,
    ( spl80_60
  <=> r1_xboole_0(k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_60])])).

fof(f2586,plain,
    ( ~ spl80_61
    | spl80_9 ),
    inference(avatar_split_clause,[],[f2565,f2052,f2584])).

fof(f2584,plain,
    ( spl80_61
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_61])])).

fof(f2565,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl80_9 ),
    inference(resolution,[],[f2101,f1396])).

fof(f1396,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2101,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | ~ r1_tarski(sK0,X0) )
    | spl80_9 ),
    inference(resolution,[],[f2053,f1432])).

fof(f1432,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f842])).

fof(f842,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f841])).

fof(f841,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f2554,plain,
    ( ~ spl80_60
    | spl80_29 ),
    inference(avatar_split_clause,[],[f2545,f2268,f2552])).

fof(f2545,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),k1_xboole_0)
    | spl80_29 ),
    inference(resolution,[],[f2269,f1322])).

fof(f1322,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f785])).

fof(f785,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f2269,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK1))
    | spl80_29 ),
    inference(avatar_component_clause,[],[f2268])).

fof(f2539,plain,
    ( ~ spl80_59
    | spl80_27 ),
    inference(avatar_split_clause,[],[f2534,f2202,f2537])).

fof(f2537,plain,
    ( spl80_59
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_59])])).

fof(f2202,plain,
    ( spl80_27
  <=> v1_xboole_0(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_27])])).

fof(f2534,plain,
    ( ~ v1_xboole_0(sK1)
    | spl80_27 ),
    inference(resolution,[],[f2532,f1344])).

fof(f1344,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f794])).

fof(f794,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f2532,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | spl80_27 ),
    inference(avatar_component_clause,[],[f2202])).

fof(f2533,plain,
    ( ~ spl80_27
    | spl80_34 ),
    inference(avatar_split_clause,[],[f2530,f2374,f2202])).

fof(f2374,plain,
    ( spl80_34
  <=> v1_relat_1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_34])])).

fof(f2530,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | spl80_34 ),
    inference(resolution,[],[f2375,f1709])).

fof(f1709,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f945])).

fof(f945,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f2375,plain,
    ( ~ v1_relat_1(k1_relat_1(sK1))
    | spl80_34 ),
    inference(avatar_component_clause,[],[f2374])).

fof(f2475,plain,
    ( ~ spl80_57
    | spl80_58
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2468,f1991,f2473,f2470])).

fof(f2470,plain,
    ( spl80_57
  <=> r2_hidden(sK79(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_57])])).

fof(f2473,plain,
    ( spl80_58
  <=> ! [X91] : ~ r2_hidden(X91,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_58])])).

fof(f2468,plain,
    ( ! [X91] :
        ( ~ r2_hidden(X91,k2_relat_1(sK1))
        | ~ r2_hidden(sK79(sK1),sK0) )
    | ~ spl80_2 ),
    inference(global_subsumption,[],[f1280,f2371])).

fof(f2371,plain,
    ( ! [X91] :
        ( ~ r2_hidden(sK79(sK1),sK0)
        | ~ r2_hidden(X91,k2_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1877])).

fof(f2467,plain,
    ( spl80_27
    | ~ spl80_56
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2365,f1991,f2465,f2202])).

fof(f2465,plain,
    ( spl80_56
  <=> r2_hidden(sK58(k1_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_56])])).

fof(f2365,plain,
    ( ~ r2_hidden(sK58(k1_relat_1(sK1)),sK0)
    | v1_xboole_0(k1_relat_1(sK1))
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1705])).

fof(f1705,plain,(
    ! [X0] :
      ( r2_hidden(sK58(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1221])).

fof(f1221,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK58(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK58])],[f1219,f1220])).

fof(f1220,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK58(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1219,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f1218])).

fof(f1218,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2463,plain,
    ( spl80_34
    | ~ spl80_55
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2364,f1991,f2461,f2374])).

fof(f2461,plain,
    ( spl80_55
  <=> r2_hidden(sK45(k1_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_55])])).

fof(f2364,plain,
    ( ~ r2_hidden(sK45(k1_relat_1(sK1)),sK0)
    | v1_relat_1(k1_relat_1(sK1))
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1674])).

fof(f1674,plain,(
    ! [X0] :
      ( r2_hidden(sK45(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1198])).

fof(f1198,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK45(X0)
          & r2_hidden(sK45(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK46(X4),sK47(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK45,sK46,sK47])],[f1195,f1197,f1196])).

fof(f1196,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK45(X0)
        & r2_hidden(sK45(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1197,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK46(X4),sK47(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f1195,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f1194])).

fof(f1194,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f925])).

fof(f925,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f642])).

fof(f642,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f2458,plain,
    ( spl80_53
    | ~ spl80_54
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2347,f1991,f2456,f2453])).

fof(f2453,plain,
    ( spl80_53
  <=> ! [X49] : ~ r2_hidden(X49,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_53])])).

fof(f2456,plain,
    ( spl80_54
  <=> r2_hidden(sK15(k1_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_54])])).

fof(f2347,plain,
    ( ! [X49] :
        ( ~ r2_hidden(sK15(k1_relat_1(sK1)),sK0)
        | ~ r2_hidden(X49,k1_relat_1(sK1)) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1424])).

fof(f1424,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK15(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1097])).

fof(f1097,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK15(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK15(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f837,f1096])).

fof(f1096,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK15(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK15(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f837,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f433])).

fof(f433,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f2451,plain,
    ( ~ spl80_52
    | ~ spl80_2
    | spl80_13 ),
    inference(avatar_split_clause,[],[f2447,f2098,f1991,f2449])).

fof(f2449,plain,
    ( spl80_52
  <=> r2_hidden(sK12(k1_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_52])])).

fof(f2447,plain,
    ( ~ r2_hidden(sK12(k1_relat_1(sK1)),sK0)
    | ~ spl80_2
    | spl80_13 ),
    inference(global_subsumption,[],[f2099,f2345])).

fof(f2345,plain,
    ( ~ r2_hidden(sK12(k1_relat_1(sK1)),sK0)
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1391])).

fof(f1391,plain,(
    ! [X0] :
      ( r2_hidden(sK12(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1088])).

fof(f1088,plain,(
    ! [X0] :
      ( r2_hidden(sK12(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f820,f1087])).

fof(f1087,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK12(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f820,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f2443,plain,
    ( ~ spl80_34
    | spl80_51
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2338,f1991,f2441,f2374])).

fof(f2441,plain,
    ( spl80_51
  <=> ! [X38,X37] :
        ( ~ r2_hidden(k4_tarski(sK7(X37,X38,k1_relat_1(sK1)),sK8(X37,X38,k1_relat_1(sK1))),sK0)
        | ~ v1_relat_1(X37)
        | k1_relat_1(sK1) = k7_relat_1(X37,X38)
        | r2_hidden(k4_tarski(sK7(X37,X38,k1_relat_1(sK1)),sK8(X37,X38,k1_relat_1(sK1))),X37) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_51])])).

fof(f2338,plain,
    ( ! [X37,X38] :
        ( ~ r2_hidden(k4_tarski(sK7(X37,X38,k1_relat_1(sK1)),sK8(X37,X38,k1_relat_1(sK1))),sK0)
        | r2_hidden(k4_tarski(sK7(X37,X38,k1_relat_1(sK1)),sK8(X37,X38,k1_relat_1(sK1))),X37)
        | k1_relat_1(sK1) = k7_relat_1(X37,X38)
        | ~ v1_relat_1(k1_relat_1(sK1))
        | ~ v1_relat_1(X37) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1365])).

fof(f1365,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1076])).

fof(f1076,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK7(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
                    & r2_hidden(sK7(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f1074,f1075])).

fof(f1075,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
            & r2_hidden(sK7(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1074,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1073])).

fof(f1073,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1072])).

% (7619)Time limit reached!
% (7619)------------------------------
% (7619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7619)Termination reason: Time limit
% (7619)Termination phase: Saturation

% (7619)Memory used [KB]: 15863
% (7619)Time elapsed: 0.800 s
% (7619)------------------------------
% (7619)------------------------------
fof(f1072,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f810])).

fof(f810,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f641])).

fof(f641,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f2439,plain,
    ( ~ spl80_34
    | spl80_50
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2337,f1991,f2437,f2374])).

fof(f2437,plain,
    ( spl80_50
  <=> ! [X36,X35] :
        ( ~ r2_hidden(k4_tarski(sK7(X35,X36,k1_relat_1(sK1)),sK8(X35,X36,k1_relat_1(sK1))),sK0)
        | ~ v1_relat_1(X35)
        | k1_relat_1(sK1) = k7_relat_1(X35,X36)
        | r2_hidden(sK7(X35,X36,k1_relat_1(sK1)),X36) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_50])])).

fof(f2337,plain,
    ( ! [X35,X36] :
        ( ~ r2_hidden(k4_tarski(sK7(X35,X36,k1_relat_1(sK1)),sK8(X35,X36,k1_relat_1(sK1))),sK0)
        | r2_hidden(sK7(X35,X36,k1_relat_1(sK1)),X36)
        | k1_relat_1(sK1) = k7_relat_1(X35,X36)
        | ~ v1_relat_1(k1_relat_1(sK1))
        | ~ v1_relat_1(X35) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1364])).

fof(f1364,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1076])).

fof(f2435,plain,
    ( ~ spl80_34
    | spl80_49
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2336,f1991,f2433,f2374])).

fof(f2433,plain,
    ( spl80_49
  <=> ! [X34] :
        ( ~ r2_hidden(k4_tarski(sK64(X34,k1_relat_1(sK1)),sK65(X34,k1_relat_1(sK1))),sK0)
        | k1_relat_1(sK1) = k6_relat_1(X34)
        | sK64(X34,k1_relat_1(sK1)) = sK65(X34,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_49])])).

fof(f2336,plain,
    ( ! [X34] :
        ( ~ r2_hidden(k4_tarski(sK64(X34,k1_relat_1(sK1)),sK65(X34,k1_relat_1(sK1))),sK0)
        | sK64(X34,k1_relat_1(sK1)) = sK65(X34,k1_relat_1(sK1))
        | k1_relat_1(sK1) = k6_relat_1(X34)
        | ~ v1_relat_1(k1_relat_1(sK1)) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1746])).

fof(f1746,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK64(X0,X1),sK65(X0,X1)),X1)
      | sK64(X0,X1) = sK65(X0,X1)
      | k6_relat_1(X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1238])).

fof(f1238,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK64(X0,X1) != sK65(X0,X1)
              | ~ r2_hidden(sK64(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK64(X0,X1),sK65(X0,X1)),X1) )
            & ( ( sK64(X0,X1) = sK65(X0,X1)
                & r2_hidden(sK64(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK64(X0,X1),sK65(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK64,sK65])],[f1236,f1237])).

fof(f1237,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK64(X0,X1) != sK65(X0,X1)
          | ~ r2_hidden(sK64(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK64(X0,X1),sK65(X0,X1)),X1) )
        & ( ( sK64(X0,X1) = sK65(X0,X1)
            & r2_hidden(sK64(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK64(X0,X1),sK65(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1236,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f1235])).

fof(f1235,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1234])).

fof(f1234,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f969])).

fof(f969,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f640])).

fof(f640,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f2431,plain,
    ( ~ spl80_34
    | spl80_48
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2335,f1991,f2429,f2374])).

fof(f2429,plain,
    ( spl80_48
  <=> ! [X33] :
        ( ~ r2_hidden(k4_tarski(sK64(X33,k1_relat_1(sK1)),sK65(X33,k1_relat_1(sK1))),sK0)
        | k1_relat_1(sK1) = k6_relat_1(X33)
        | r2_hidden(sK64(X33,k1_relat_1(sK1)),X33) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_48])])).

fof(f2335,plain,
    ( ! [X33] :
        ( ~ r2_hidden(k4_tarski(sK64(X33,k1_relat_1(sK1)),sK65(X33,k1_relat_1(sK1))),sK0)
        | r2_hidden(sK64(X33,k1_relat_1(sK1)),X33)
        | k1_relat_1(sK1) = k6_relat_1(X33)
        | ~ v1_relat_1(k1_relat_1(sK1)) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1745])).

fof(f1745,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK64(X0,X1),sK65(X0,X1)),X1)
      | r2_hidden(sK64(X0,X1),X0)
      | k6_relat_1(X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1238])).

fof(f2427,plain,
    ( ~ spl80_34
    | spl80_47
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2334,f1991,f2425,f2374])).

fof(f2425,plain,
    ( spl80_47
  <=> ! [X32,X31,X30] :
        ( ~ r2_hidden(k4_tarski(sK63(X30,k1_relat_1(sK1),X31,X32),X32),sK0)
        | ~ v1_relat_1(X30)
        | ~ v1_relat_1(k5_relat_1(X30,k1_relat_1(sK1)))
        | ~ r2_hidden(k4_tarski(X31,X32),k5_relat_1(X30,k1_relat_1(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_47])])).

fof(f2334,plain,
    ( ! [X30,X31,X32] :
        ( ~ r2_hidden(k4_tarski(sK63(X30,k1_relat_1(sK1),X31,X32),X32),sK0)
        | ~ r2_hidden(k4_tarski(X31,X32),k5_relat_1(X30,k1_relat_1(sK1)))
        | ~ v1_relat_1(k5_relat_1(X30,k1_relat_1(sK1)))
        | ~ v1_relat_1(k1_relat_1(sK1))
        | ~ v1_relat_1(X30) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1955])).

fof(f1955,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK63(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1722])).

fof(f1722,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK63(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1229])).

fof(f1229,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK61(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK60(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK60(X0,X1,X2),sK61(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK62(X0,X1,X2),sK61(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK60(X0,X1,X2),sK62(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK60(X0,X1,X2),sK61(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK63(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK63(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK60,sK61,sK62,sK63])],[f1225,f1228,f1227,f1226])).

fof(f1226,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK61(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK60(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK60(X0,X1,X2),sK61(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK61(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK60(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK60(X0,X1,X2),sK61(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1227,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK61(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK60(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK62(X0,X1,X2),sK61(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK60(X0,X1,X2),sK62(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1228,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK63(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK63(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1225,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1224])).

fof(f1224,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f955])).

fof(f955,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f649])).

fof(f649,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f2423,plain,
    ( ~ spl80_34
    | spl80_46
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2333,f1991,f2421,f2374])).

fof(f2421,plain,
    ( spl80_46
  <=> ! [X29,X28] :
        ( ~ r2_hidden(k4_tarski(sK62(X28,k1_relat_1(sK1),X29),sK61(X28,k1_relat_1(sK1),X29)),sK0)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X29)
        | r2_hidden(k4_tarski(sK60(X28,k1_relat_1(sK1),X29),sK61(X28,k1_relat_1(sK1),X29)),X29)
        | k5_relat_1(X28,k1_relat_1(sK1)) = X29 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_46])])).

fof(f2333,plain,
    ( ! [X28,X29] :
        ( ~ r2_hidden(k4_tarski(sK62(X28,k1_relat_1(sK1),X29),sK61(X28,k1_relat_1(sK1),X29)),sK0)
        | k5_relat_1(X28,k1_relat_1(sK1)) = X29
        | r2_hidden(k4_tarski(sK60(X28,k1_relat_1(sK1),X29),sK61(X28,k1_relat_1(sK1),X29)),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(k1_relat_1(sK1))
        | ~ v1_relat_1(X28) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1725])).

fof(f1725,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK62(X0,X1,X2),sK61(X0,X1,X2)),X1)
      | k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK60(X0,X1,X2),sK61(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1229])).

fof(f2419,plain,
    ( ~ spl80_34
    | spl80_45
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2332,f1991,f2417,f2374])).

fof(f2417,plain,
    ( spl80_45
  <=> ! [X27] :
        ( ~ r2_hidden(k4_tarski(sK50(X27,k1_relat_1(sK1)),sK51(X27,k1_relat_1(sK1))),sK0)
        | ~ v1_relat_1(X27)
        | r2_hidden(k4_tarski(sK50(X27,k1_relat_1(sK1)),sK51(X27,k1_relat_1(sK1))),X27)
        | k1_relat_1(sK1) = X27 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_45])])).

fof(f2332,plain,
    ( ! [X27] :
        ( ~ r2_hidden(k4_tarski(sK50(X27,k1_relat_1(sK1)),sK51(X27,k1_relat_1(sK1))),sK0)
        | k1_relat_1(sK1) = X27
        | r2_hidden(k4_tarski(sK50(X27,k1_relat_1(sK1)),sK51(X27,k1_relat_1(sK1))),X27)
        | ~ v1_relat_1(k1_relat_1(sK1))
        | ~ v1_relat_1(X27) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1681])).

fof(f1681,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK50(X0,X1),sK51(X0,X1)),X1)
      | X0 = X1
      | r2_hidden(k4_tarski(sK50(X0,X1),sK51(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1206])).

fof(f1206,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK50(X0,X1),sK51(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK50(X0,X1),sK51(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK50(X0,X1),sK51(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK50(X0,X1),sK51(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK50,sK51])],[f1204,f1205])).

fof(f1205,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK50(X0,X1),sK51(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK50(X0,X1),sK51(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK50(X0,X1),sK51(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK50(X0,X1),sK51(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1204,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1203])).

fof(f1203,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f927])).

fof(f927,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f643])).

fof(f643,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).

fof(f2415,plain,
    ( spl80_44
    | spl80_43
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2331,f1991,f2408,f2412])).

fof(f2412,plain,
    ( spl80_44
  <=> ! [X20,X21] : k4_tarski(X20,X21) != sK43(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_44])])).

fof(f2408,plain,
    ( spl80_43
  <=> ! [X16,X18,X17] :
        ( ~ r2_hidden(k4_tarski(sK41(X16,k1_relat_1(sK1)),sK42(X16,k1_relat_1(sK1))),sK0)
        | k4_tarski(X17,X18) != sK44(X16)
        | r2_hidden(k4_tarski(sK41(X16,k1_relat_1(sK1)),sK42(X16,k1_relat_1(sK1))),X16)
        | k1_relat_1(sK1) = X16 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_43])])).

fof(f2331,plain,
    ( ! [X26,X24,X23,X25,X22] :
        ( ~ r2_hidden(k4_tarski(sK41(X22,k1_relat_1(sK1)),sK42(X22,k1_relat_1(sK1))),sK0)
        | k1_relat_1(sK1) = X22
        | r2_hidden(k4_tarski(sK41(X22,k1_relat_1(sK1)),sK42(X22,k1_relat_1(sK1))),X22)
        | sK43(k1_relat_1(sK1)) != k4_tarski(X23,X24)
        | k4_tarski(X25,X26) != sK44(X22) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1665])).

fof(f2414,plain,
    ( spl80_44
    | spl80_42
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2330,f1991,f2404,f2412])).

fof(f2404,plain,
    ( spl80_42
  <=> ! [X15] :
        ( ~ r2_hidden(k4_tarski(sK41(X15,k1_relat_1(sK1)),sK42(X15,k1_relat_1(sK1))),sK0)
        | r2_hidden(sK44(X15),X15)
        | r2_hidden(k4_tarski(sK41(X15,k1_relat_1(sK1)),sK42(X15,k1_relat_1(sK1))),X15)
        | k1_relat_1(sK1) = X15 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_42])])).

fof(f2330,plain,
    ( ! [X21,X19,X20] :
        ( ~ r2_hidden(k4_tarski(sK41(X19,k1_relat_1(sK1)),sK42(X19,k1_relat_1(sK1))),sK0)
        | k1_relat_1(sK1) = X19
        | r2_hidden(k4_tarski(sK41(X19,k1_relat_1(sK1)),sK42(X19,k1_relat_1(sK1))),X19)
        | k4_tarski(X20,X21) != sK43(k1_relat_1(sK1))
        | r2_hidden(sK44(X19),X19) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1664])).

fof(f2410,plain,
    ( spl80_41
    | spl80_43
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2329,f1991,f2408,f2401])).

fof(f2401,plain,
    ( spl80_41
  <=> r2_hidden(sK43(k1_relat_1(sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_41])])).

fof(f2329,plain,
    ( ! [X17,X18,X16] :
        ( ~ r2_hidden(k4_tarski(sK41(X16,k1_relat_1(sK1)),sK42(X16,k1_relat_1(sK1))),sK0)
        | k1_relat_1(sK1) = X16
        | r2_hidden(k4_tarski(sK41(X16,k1_relat_1(sK1)),sK42(X16,k1_relat_1(sK1))),X16)
        | r2_hidden(sK43(k1_relat_1(sK1)),k1_relat_1(sK1))
        | k4_tarski(X17,X18) != sK44(X16) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1663])).

fof(f2406,plain,
    ( spl80_41
    | spl80_42
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2328,f1991,f2404,f2401])).

fof(f2328,plain,
    ( ! [X15] :
        ( ~ r2_hidden(k4_tarski(sK41(X15,k1_relat_1(sK1)),sK42(X15,k1_relat_1(sK1))),sK0)
        | k1_relat_1(sK1) = X15
        | r2_hidden(k4_tarski(sK41(X15,k1_relat_1(sK1)),sK42(X15,k1_relat_1(sK1))),X15)
        | r2_hidden(sK43(k1_relat_1(sK1)),k1_relat_1(sK1))
        | r2_hidden(sK44(X15),X15) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1662])).

fof(f2399,plain,
    ( spl80_39
    | spl80_40
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2327,f1991,f2397,f2394])).

fof(f2394,plain,
    ( spl80_39
  <=> ! [X11,X12] : ~ r1_tarski(k1_relat_1(sK1),k2_zfmisc_1(X11,X12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_39])])).

fof(f2397,plain,
    ( spl80_40
  <=> ! [X13,X10,X14] :
        ( ~ r2_hidden(k4_tarski(sK23(X10,k1_relat_1(sK1)),sK24(X10,k1_relat_1(sK1))),sK0)
        | ~ r1_tarski(X10,k2_zfmisc_1(X13,X14))
        | r2_hidden(k4_tarski(sK23(X10,k1_relat_1(sK1)),sK24(X10,k1_relat_1(sK1))),X10)
        | k1_relat_1(sK1) = X10 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_40])])).

fof(f2327,plain,
    ( ! [X14,X12,X10,X13,X11] :
        ( ~ r2_hidden(k4_tarski(sK23(X10,k1_relat_1(sK1)),sK24(X10,k1_relat_1(sK1))),sK0)
        | k1_relat_1(sK1) = X10
        | r2_hidden(k4_tarski(sK23(X10,k1_relat_1(sK1)),sK24(X10,k1_relat_1(sK1))),X10)
        | ~ r1_tarski(k1_relat_1(sK1),k2_zfmisc_1(X11,X12))
        | ~ r1_tarski(X10,k2_zfmisc_1(X13,X14)) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1616])).

fof(f2392,plain,
    ( ~ spl80_34
    | spl80_38
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2326,f1991,f2390,f2374])).

fof(f2390,plain,
    ( spl80_38
  <=> ! [X9,X7,X8] :
        ( ~ r2_hidden(k4_tarski(X7,sK63(k1_relat_1(sK1),X8,X7,X9)),sK0)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(k5_relat_1(k1_relat_1(sK1),X8))
        | ~ r2_hidden(k4_tarski(X7,X9),k5_relat_1(k1_relat_1(sK1),X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_38])])).

fof(f2326,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_hidden(k4_tarski(X7,sK63(k1_relat_1(sK1),X8,X7,X9)),sK0)
        | ~ r2_hidden(k4_tarski(X7,X9),k5_relat_1(k1_relat_1(sK1),X8))
        | ~ v1_relat_1(k5_relat_1(k1_relat_1(sK1),X8))
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(k1_relat_1(sK1)) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1956])).

fof(f1956,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK63(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1721])).

fof(f1721,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK63(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1229])).

fof(f2388,plain,
    ( ~ spl80_34
    | spl80_37
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2322,f1991,f2386,f2374])).

fof(f2386,plain,
    ( spl80_37
  <=> ! [X3,X2] :
        ( ~ r2_hidden(k4_tarski(sK60(k1_relat_1(sK1),X2,X3),sK62(k1_relat_1(sK1),X2,X3)),sK0)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK60(k1_relat_1(sK1),X2,X3),sK61(k1_relat_1(sK1),X2,X3)),X3)
        | k5_relat_1(k1_relat_1(sK1),X2) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_37])])).

fof(f2322,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(sK60(k1_relat_1(sK1),X2,X3),sK62(k1_relat_1(sK1),X2,X3)),sK0)
        | k5_relat_1(k1_relat_1(sK1),X2) = X3
        | r2_hidden(k4_tarski(sK60(k1_relat_1(sK1),X2,X3),sK61(k1_relat_1(sK1),X2,X3)),X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k1_relat_1(sK1)) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1724])).

fof(f1724,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK60(X0,X1,X2),sK62(X0,X1,X2)),X0)
      | k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK60(X0,X1,X2),sK61(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1229])).

fof(f2384,plain,
    ( ~ spl80_34
    | ~ spl80_36
    | ~ spl80_2
    | spl80_13 ),
    inference(avatar_split_clause,[],[f2380,f2098,f1991,f2382,f2374])).

fof(f2382,plain,
    ( spl80_36
  <=> r2_hidden(k4_tarski(sK52(k1_relat_1(sK1)),sK53(k1_relat_1(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_36])])).

fof(f2380,plain,
    ( ~ r2_hidden(k4_tarski(sK52(k1_relat_1(sK1)),sK53(k1_relat_1(sK1))),sK0)
    | ~ v1_relat_1(k1_relat_1(sK1))
    | ~ spl80_2
    | spl80_13 ),
    inference(global_subsumption,[],[f2099,f2321])).

fof(f2321,plain,
    ( ~ r2_hidden(k4_tarski(sK52(k1_relat_1(sK1)),sK53(k1_relat_1(sK1))),sK0)
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(k1_relat_1(sK1))
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1683])).

fof(f1683,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK52(X0),sK53(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1208])).

fof(f1208,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK52(X0),sK53(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK52,sK53])],[f929,f1207])).

fof(f1207,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK52(X0),sK53(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f929,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f928])).

fof(f928,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f710])).

fof(f710,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f2379,plain,
    ( ~ spl80_34
    | spl80_35
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2320,f1991,f2377,f2374])).

fof(f2377,plain,
    ( spl80_35
  <=> ! [X1] :
        ( ~ r2_hidden(k4_tarski(sK48(k1_relat_1(sK1),X1),sK49(k1_relat_1(sK1),X1)),sK0)
        | r1_tarski(k1_relat_1(sK1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_35])])).

fof(f2320,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(sK48(k1_relat_1(sK1),X1),sK49(k1_relat_1(sK1),X1)),sK0)
        | r1_tarski(k1_relat_1(sK1),X1)
        | ~ v1_relat_1(k1_relat_1(sK1)) )
    | ~ spl80_2 ),
    inference(resolution,[],[f2198,f1677])).

fof(f1677,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK48(X0,X1),sK49(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1202])).

fof(f2308,plain,
    ( spl80_33
    | ~ spl80_11 ),
    inference(avatar_split_clause,[],[f2304,f2062,f2306])).

fof(f2304,plain,
    ( sK0 = k4_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_11 ),
    inference(forward_demodulation,[],[f2253,f1614])).

fof(f2253,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_11 ),
    inference(superposition,[],[f1611,f2063])).

% (7604)Termination reason: Time limit
% (7604)Termination phase: Saturation

% (7604)Memory used [KB]: 12281
% (7604)Time elapsed: 0.815 s
% (7604)------------------------------
% (7604)------------------------------
fof(f1611,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f2303,plain,
    ( spl80_32
    | ~ spl80_11 ),
    inference(avatar_split_clause,[],[f2252,f2062,f2301])).

fof(f2299,plain,
    ( spl80_31
    | ~ spl80_11 ),
    inference(avatar_split_clause,[],[f2295,f2062,f2297])).

fof(f2297,plain,
    ( spl80_31
  <=> k2_xboole_0(k4_xboole_0(sK0,k1_relat_1(sK1)),k4_xboole_0(k1_relat_1(sK1),sK0)) = k2_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_31])])).

fof(f2295,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k1_relat_1(sK1)),k4_xboole_0(k1_relat_1(sK1),sK0)) = k2_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_11 ),
    inference(forward_demodulation,[],[f2251,f1614])).

fof(f2251,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k1_relat_1(sK1)),k4_xboole_0(k1_relat_1(sK1),sK0)) = k4_xboole_0(k2_xboole_0(sK0,k1_relat_1(sK1)),k1_xboole_0)
    | ~ spl80_11 ),
    inference(superposition,[],[f1605,f2063])).

fof(f2280,plain,
    ( spl80_30
    | ~ spl80_11 ),
    inference(avatar_split_clause,[],[f2223,f2062,f2278])).

fof(f2276,plain,
    ( spl80_4
    | ~ spl80_11 ),
    inference(avatar_split_clause,[],[f2275,f2062,f2006])).

fof(f2006,plain,
    ( spl80_4
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_4])])).

fof(f2275,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_11 ),
    inference(forward_demodulation,[],[f2222,f1614])).

fof(f2222,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl80_11 ),
    inference(superposition,[],[f1332,f2063])).

fof(f1332,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f162])).

fof(f162,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f2273,plain,
    ( spl80_4
    | ~ spl80_11 ),
    inference(avatar_split_clause,[],[f2272,f2062,f2006])).

fof(f2272,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_11 ),
    inference(global_subsumption,[],[f2265])).

fof(f2265,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_11 ),
    inference(trivial_inequality_removal,[],[f2219])).

fof(f2219,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_11 ),
    inference(superposition,[],[f1318,f2063])).

fof(f1318,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1058])).

fof(f1058,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f2271,plain,
    ( spl80_4
    | ~ spl80_11 ),
    inference(avatar_split_clause,[],[f2265,f2062,f2006])).

fof(f2270,plain,
    ( spl80_4
    | ~ spl80_29
    | ~ spl80_11 ),
    inference(avatar_split_clause,[],[f2218,f2062,f2268,f2006])).

fof(f2218,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK1))
    | r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_11 ),
    inference(superposition,[],[f1316,f2063])).

fof(f2207,plain,
    ( spl80_27
    | ~ spl80_28
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f2196,f1991,f2205,f2202])).

fof(f2196,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | v1_xboole_0(k1_relat_1(sK1))
    | ~ spl80_2 ),
    inference(resolution,[],[f1995,f1694])).

fof(f1694,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f938])).

fof(f938,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f937])).

fof(f937,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f135])).

fof(f135,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f2194,plain,
    ( spl80_1
    | ~ spl80_2
    | spl80_4 ),
    inference(avatar_contradiction_clause,[],[f2193])).

fof(f2193,plain,
    ( $false
    | spl80_1
    | ~ spl80_2
    | spl80_4 ),
    inference(global_subsumption,[],[f2090,f1995])).

fof(f2090,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl80_4 ),
    inference(resolution,[],[f2007,f1322])).

fof(f2007,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl80_4 ),
    inference(avatar_component_clause,[],[f2006])).

fof(f2192,plain,
    ( ~ spl80_2
    | spl80_4 ),
    inference(avatar_contradiction_clause,[],[f2191])).

fof(f2191,plain,
    ( $false
    | ~ spl80_2
    | spl80_4 ),
    inference(global_subsumption,[],[f2090,f1995])).

fof(f2190,plain,
    ( ~ spl80_2
    | spl80_4 ),
    inference(avatar_split_clause,[],[f2090,f2006,f1991])).

fof(f2189,plain,
    ( ~ spl80_20
    | spl80_26
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2122,f1988,f2187,f2164])).

fof(f2164,plain,
    ( spl80_20
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_20])])).

fof(f2187,plain,
    ( spl80_26
  <=> ! [X40,X38,X39] :
        ( ~ r2_hidden(k4_tarski(sK60(X38,X39,sK0),sK61(X38,X39,sK0)),k1_xboole_0)
        | ~ v1_relat_1(X38)
        | ~ v1_relat_1(X39)
        | sK0 = k5_relat_1(X38,X39)
        | ~ r2_hidden(k4_tarski(sK60(X38,X39,sK0),X40),X38)
        | ~ r2_hidden(k4_tarski(X40,sK61(X38,X39,sK0)),X39) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_26])])).

fof(f1988,plain,
    ( spl80_1
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_1])])).

fof(f2122,plain,
    ( ! [X39,X38,X40] :
        ( ~ r2_hidden(k4_tarski(sK60(X38,X39,sK0),sK61(X38,X39,sK0)),k1_xboole_0)
        | ~ r2_hidden(k4_tarski(X40,sK61(X38,X39,sK0)),X39)
        | ~ r2_hidden(k4_tarski(sK60(X38,X39,sK0),X40),X38)
        | sK0 = k5_relat_1(X38,X39)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X39)
        | ~ v1_relat_1(X38) )
    | ~ spl80_1 ),
    inference(resolution,[],[f2034,f1726])).

fof(f1726,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(sK60(X0,X1,X2),sK61(X0,X1,X2)),X2)
      | ~ r2_hidden(k4_tarski(X5,sK61(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK60(X0,X1,X2),X5),X0)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1229])).

fof(f2034,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl80_1 ),
    inference(global_subsumption,[],[f1280,f2033])).

fof(f2033,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl80_1 ),
    inference(forward_demodulation,[],[f2017,f1894])).

fof(f1894,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f711])).

fof(f711,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f2017,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
        | r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl80_1 ),
    inference(superposition,[],[f1347,f1994])).

fof(f1994,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl80_1 ),
    inference(avatar_component_clause,[],[f1988])).

fof(f2185,plain,
    ( ~ spl80_20
    | spl80_25
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2121,f1988,f2183,f2164])).

fof(f2183,plain,
    ( spl80_25
  <=> ! [X36,X37] :
        ( ~ r2_hidden(k4_tarski(sK7(X36,X37,sK0),sK8(X36,X37,sK0)),k1_xboole_0)
        | ~ v1_relat_1(X36)
        | sK0 = k7_relat_1(X36,X37)
        | ~ r2_hidden(sK7(X36,X37,sK0),X37)
        | ~ r2_hidden(k4_tarski(sK7(X36,X37,sK0),sK8(X36,X37,sK0)),X36) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_25])])).

fof(f2121,plain,
    ( ! [X37,X36] :
        ( ~ r2_hidden(k4_tarski(sK7(X36,X37,sK0),sK8(X36,X37,sK0)),k1_xboole_0)
        | ~ r2_hidden(k4_tarski(sK7(X36,X37,sK0),sK8(X36,X37,sK0)),X36)
        | ~ r2_hidden(sK7(X36,X37,sK0),X37)
        | sK0 = k7_relat_1(X36,X37)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X36) )
    | ~ spl80_1 ),
    inference(resolution,[],[f2034,f1366])).

fof(f1366,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
      | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X1)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1076])).

fof(f2181,plain,
    ( ~ spl80_20
    | spl80_24
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2118,f1988,f2179,f2164])).

fof(f2179,plain,
    ( spl80_24
  <=> ! [X31,X30] :
        ( ~ r2_hidden(k4_tarski(X30,X31),k1_xboole_0)
        | r2_hidden(X30,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_24])])).

fof(f2118,plain,
    ( ! [X30,X31] :
        ( ~ r2_hidden(k4_tarski(X30,X31),k1_xboole_0)
        | r2_hidden(X30,k1_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl80_1 ),
    inference(resolution,[],[f2034,f1870])).

fof(f1870,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1030])).

fof(f1030,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1029])).

fof(f1029,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f679])).

fof(f679,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f2177,plain,
    ( ~ spl80_20
    | spl80_23
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2116,f1988,f2175,f2164])).

fof(f2175,plain,
    ( spl80_23
  <=> ! [X27] :
        ( ~ r2_hidden(k4_tarski(sK66(X27,sK0),sK66(X27,sK0)),k1_xboole_0)
        | r1_tarski(k6_relat_1(X27),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_23])])).

fof(f2116,plain,
    ( ! [X27] :
        ( ~ r2_hidden(k4_tarski(sK66(X27,sK0),sK66(X27,sK0)),k1_xboole_0)
        | r1_tarski(k6_relat_1(X27),sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl80_1 ),
    inference(resolution,[],[f2034,f1749])).

fof(f1749,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK66(X0,X1),sK66(X0,X1)),X1)
      | r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1240])).

fof(f1240,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ( ~ r2_hidden(k4_tarski(sK66(X0,X1),sK66(X0,X1)),X1)
        & r2_hidden(sK66(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK66])],[f971,f1239])).

fof(f1239,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(k4_tarski(sK66(X0,X1),sK66(X0,X1)),X1)
        & r2_hidden(sK66(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f971,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f970])).

fof(f970,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f720])).

fof(f720,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

fof(f2173,plain,
    ( ~ spl80_20
    | spl80_22
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2115,f1988,f2171,f2164])).

fof(f2171,plain,
    ( spl80_22
  <=> ! [X26] :
        ( ~ r2_hidden(k4_tarski(sK64(X26,sK0),sK65(X26,sK0)),k1_xboole_0)
        | sK0 = k6_relat_1(X26)
        | ~ r2_hidden(sK64(X26,sK0),X26)
        | sK64(X26,sK0) != sK65(X26,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_22])])).

fof(f2115,plain,
    ( ! [X26] :
        ( ~ r2_hidden(k4_tarski(sK64(X26,sK0),sK65(X26,sK0)),k1_xboole_0)
        | sK64(X26,sK0) != sK65(X26,sK0)
        | ~ r2_hidden(sK64(X26,sK0),X26)
        | sK0 = k6_relat_1(X26)
        | ~ v1_relat_1(sK0) )
    | ~ spl80_1 ),
    inference(resolution,[],[f2034,f1747])).

fof(f1747,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK64(X0,X1),sK65(X0,X1)),X1)
      | sK64(X0,X1) != sK65(X0,X1)
      | ~ r2_hidden(sK64(X0,X1),X0)
      | k6_relat_1(X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1238])).

fof(f2169,plain,
    ( ~ spl80_20
    | spl80_21
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2114,f1988,f2167,f2164])).

fof(f2167,plain,
    ( spl80_21
  <=> ! [X25] :
        ( ~ r2_hidden(k4_tarski(sK50(X25,sK0),sK51(X25,sK0)),k1_xboole_0)
        | ~ v1_relat_1(X25)
        | ~ r2_hidden(k4_tarski(sK50(X25,sK0),sK51(X25,sK0)),X25)
        | sK0 = X25 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_21])])).

fof(f2114,plain,
    ( ! [X25] :
        ( ~ r2_hidden(k4_tarski(sK50(X25,sK0),sK51(X25,sK0)),k1_xboole_0)
        | sK0 = X25
        | ~ r2_hidden(k4_tarski(sK50(X25,sK0),sK51(X25,sK0)),X25)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X25) )
    | ~ spl80_1 ),
    inference(resolution,[],[f2034,f1682])).

fof(f1682,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK50(X0,X1),sK51(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK50(X0,X1),sK51(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1206])).

fof(f2162,plain,
    ( spl80_19
    | spl80_18
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2112,f1988,f2155,f2159])).

fof(f2155,plain,
    ( spl80_18
  <=> ! [X13,X15,X14] :
        ( ~ r2_hidden(k4_tarski(sK41(X13,sK0),sK42(X13,sK0)),k1_xboole_0)
        | k4_tarski(X14,X15) != sK44(X13)
        | ~ r2_hidden(k4_tarski(sK41(X13,sK0),sK42(X13,sK0)),X13)
        | sK0 = X13 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_18])])).

fof(f2112,plain,
    ( ! [X23,X21,X19,X22,X20] :
        ( ~ r2_hidden(k4_tarski(sK41(X19,sK0),sK42(X19,sK0)),k1_xboole_0)
        | sK0 = X19
        | ~ r2_hidden(k4_tarski(sK41(X19,sK0),sK42(X19,sK0)),X19)
        | sK43(sK0) != k4_tarski(X20,X21)
        | k4_tarski(X22,X23) != sK44(X19) )
    | ~ spl80_1 ),
    inference(resolution,[],[f2034,f1669])).

fof(f1669,plain,(
    ! [X6,X0,X8,X5,X1,X9] :
      ( ~ r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK43(X1)
      | k4_tarski(X8,X9) != sK44(X0) ) ),
    inference(cnf_transformation,[],[f1193])).

fof(f2161,plain,
    ( spl80_19
    | spl80_17
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2111,f1988,f2151,f2159])).

fof(f2151,plain,
    ( spl80_17
  <=> ! [X12] :
        ( ~ r2_hidden(k4_tarski(sK41(X12,sK0),sK42(X12,sK0)),k1_xboole_0)
        | r2_hidden(sK44(X12),X12)
        | ~ r2_hidden(k4_tarski(sK41(X12,sK0),sK42(X12,sK0)),X12)
        | sK0 = X12 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_17])])).

fof(f2111,plain,
    ( ! [X17,X18,X16] :
        ( ~ r2_hidden(k4_tarski(sK41(X16,sK0),sK42(X16,sK0)),k1_xboole_0)
        | sK0 = X16
        | ~ r2_hidden(k4_tarski(sK41(X16,sK0),sK42(X16,sK0)),X16)
        | sK43(sK0) != k4_tarski(X17,X18)
        | r2_hidden(sK44(X16),X16) )
    | ~ spl80_1 ),
    inference(resolution,[],[f2034,f1668])).

fof(f1668,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK43(X1)
      | r2_hidden(sK44(X0),X0) ) ),
    inference(cnf_transformation,[],[f1193])).

fof(f2157,plain,
    ( spl80_16
    | spl80_18
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2110,f1988,f2155,f2148])).

fof(f2110,plain,
    ( ! [X14,X15,X13] :
        ( ~ r2_hidden(k4_tarski(sK41(X13,sK0),sK42(X13,sK0)),k1_xboole_0)
        | sK0 = X13
        | ~ r2_hidden(k4_tarski(sK41(X13,sK0),sK42(X13,sK0)),X13)
        | r2_hidden(sK43(sK0),sK0)
        | k4_tarski(X14,X15) != sK44(X13) )
    | ~ spl80_1 ),
    inference(resolution,[],[f2034,f1667])).

fof(f1667,plain,(
    ! [X0,X8,X1,X9] :
      ( ~ r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X0)
      | r2_hidden(sK43(X1),X1)
      | k4_tarski(X8,X9) != sK44(X0) ) ),
    inference(cnf_transformation,[],[f1193])).

fof(f2153,plain,
    ( spl80_16
    | spl80_17
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2109,f1988,f2151,f2148])).

fof(f2109,plain,
    ( ! [X12] :
        ( ~ r2_hidden(k4_tarski(sK41(X12,sK0),sK42(X12,sK0)),k1_xboole_0)
        | sK0 = X12
        | ~ r2_hidden(k4_tarski(sK41(X12,sK0),sK42(X12,sK0)),X12)
        | r2_hidden(sK43(sK0),sK0)
        | r2_hidden(sK44(X12),X12) )
    | ~ spl80_1 ),
    inference(resolution,[],[f2034,f1666])).

fof(f1666,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK41(X0,X1),sK42(X0,X1)),X0)
      | r2_hidden(sK43(X1),X1)
      | r2_hidden(sK44(X0),X0) ) ),
    inference(cnf_transformation,[],[f1193])).

fof(f2146,plain,
    ( spl80_14
    | spl80_15
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2108,f1988,f2144,f2141])).

fof(f2144,plain,
    ( spl80_15
  <=> ! [X11,X7,X10] :
        ( ~ r2_hidden(k4_tarski(sK23(X7,sK0),sK24(X7,sK0)),k1_xboole_0)
        | ~ r1_tarski(X7,k2_zfmisc_1(X10,X11))
        | ~ r2_hidden(k4_tarski(sK23(X7,sK0),sK24(X7,sK0)),X7)
        | sK0 = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_15])])).

fof(f2108,plain,
    ( ! [X10,X8,X7,X11,X9] :
        ( ~ r2_hidden(k4_tarski(sK23(X7,sK0),sK24(X7,sK0)),k1_xboole_0)
        | sK0 = X7
        | ~ r2_hidden(k4_tarski(sK23(X7,sK0),sK24(X7,sK0)),X7)
        | ~ r1_tarski(sK0,k2_zfmisc_1(X8,X9))
        | ~ r1_tarski(X7,k2_zfmisc_1(X10,X11)) )
    | ~ spl80_1 ),
    inference(resolution,[],[f2034,f1617])).

fof(f1617,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK23(X0,X3),sK24(X0,X3)),X3)
      | X0 = X3
      | ~ r2_hidden(k4_tarski(sK23(X0,X3),sK24(X0,X3)),X0)
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f1158])).

fof(f2100,plain,
    ( ~ spl80_13
    | spl80_5 ),
    inference(avatar_split_clause,[],[f2096,f2011,f2098])).

fof(f2011,plain,
    ( spl80_5
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_5])])).

fof(f2096,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | spl80_5 ),
    inference(global_subsumption,[],[f1280,f2095])).

fof(f2095,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl80_5 ),
    inference(trivial_inequality_removal,[],[f2094])).

fof(f2094,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl80_5 ),
    inference(superposition,[],[f2012,f1888])).

fof(f1888,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1279])).

fof(f1279,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1049])).

fof(f1049,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f715])).

fof(f715,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f2012,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | spl80_5 ),
    inference(avatar_component_clause,[],[f2011])).

fof(f2089,plain,(
    spl80_12 ),
    inference(avatar_contradiction_clause,[],[f2083])).

fof(f2083,plain,
    ( $false
    | spl80_12 ),
    inference(resolution,[],[f2081,f1338])).

fof(f2081,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | spl80_12 ),
    inference(avatar_component_clause,[],[f2080])).

fof(f2080,plain,
    ( spl80_12
  <=> r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_12])])).

fof(f2082,plain,
    ( ~ spl80_12
    | spl80_6 ),
    inference(avatar_split_clause,[],[f2074,f2014,f2080])).

fof(f2074,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | spl80_6 ),
    inference(resolution,[],[f2015,f1322])).

fof(f2015,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl80_6 ),
    inference(avatar_component_clause,[],[f2014])).

fof(f2068,plain,
    ( spl80_7
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2067,f1988,f2041])).

fof(f2041,plain,
    ( spl80_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_7])])).

fof(f2067,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl80_1 ),
    inference(global_subsumption,[],[f1280,f2029])).

fof(f2029,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ spl80_1 ),
    inference(superposition,[],[f1360,f1994])).

fof(f2064,plain,
    ( spl80_11
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2060,f1988,f2062])).

fof(f2060,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl80_1 ),
    inference(global_subsumption,[],[f1280,f2059])).

fof(f2059,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl80_1 ),
    inference(forward_demodulation,[],[f2058,f1894])).

fof(f2058,plain,
    ( k1_relat_1(k1_xboole_0) = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl80_1 ),
    inference(forward_demodulation,[],[f2025,f1483])).

fof(f2025,plain,
    ( k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl80_1 ),
    inference(superposition,[],[f1355,f1994])).

fof(f2057,plain,
    ( ~ spl80_9
    | spl80_10
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2050,f1988,f2055,f2052])).

fof(f2050,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl80_1 ),
    inference(global_subsumption,[],[f1280,f2049])).

fof(f2049,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl80_1 ),
    inference(forward_demodulation,[],[f2024,f1894])).

fof(f2024,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl80_1 ),
    inference(superposition,[],[f1354,f1994])).

fof(f1354,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f803])).

fof(f803,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f802])).

fof(f802,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f735])).

fof(f735,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f2046,plain,
    ( spl80_7
    | ~ spl80_8
    | ~ spl80_1 ),
    inference(avatar_split_clause,[],[f2039,f1988,f2044,f2041])).

fof(f2044,plain,
    ( spl80_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_8])])).

fof(f2039,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_relat_1(k1_xboole_0)
    | ~ spl80_1 ),
    inference(global_subsumption,[],[f1280,f2021])).

fof(f2021,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl80_1 ),
    inference(superposition,[],[f1351,f1994])).

fof(f1351,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f799])).

fof(f799,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f798])).

fof(f798,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f663])).

fof(f663,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

fof(f2016,plain,
    ( ~ spl80_5
    | ~ spl80_6
    | spl80_2 ),
    inference(avatar_split_clause,[],[f2009,f1991,f2014,f2011])).

fof(f2009,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | k1_xboole_0 != k2_relat_1(sK1)
    | spl80_2 ),
    inference(global_subsumption,[],[f1280,f2004])).

fof(f2004,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | k1_xboole_0 != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl80_2 ),
    inference(superposition,[],[f1992,f1889])).

fof(f1889,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1279])).

fof(f1992,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl80_2 ),
    inference(avatar_component_clause,[],[f1991])).

fof(f2008,plain,
    ( ~ spl80_4
    | spl80_2 ),
    inference(avatar_split_clause,[],[f2001,f1991,f2006])).

fof(f2001,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl80_2 ),
    inference(resolution,[],[f1992,f1322])).

fof(f2000,plain,(
    spl80_3 ),
    inference(avatar_split_clause,[],[f1280,f1998])).

fof(f1998,plain,
    ( spl80_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl80_3])])).

fof(f1996,plain,
    ( spl80_1
    | spl80_2 ),
    inference(avatar_split_clause,[],[f1281,f1991,f1988])).

fof(f1281,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f1057])).

fof(f1993,plain,
    ( ~ spl80_1
    | ~ spl80_2 ),
    inference(avatar_split_clause,[],[f1282,f1991,f1988])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:45 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 155 expanded)
%              Number of leaves         :   21 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  194 ( 394 expanded)
%              Number of equality atoms :   90 ( 208 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f70,f77,f2487,f2516,f2563,f2630,f3172,f3187,f4189,f4220,f4253])).

fof(f4253,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,sK2)
    | k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4220,plain,
    ( spl4_26
    | spl4_45
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f4214,f4186,f4218,f2628])).

fof(f2628,plain,
    ( spl4_26
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f4218,plain,
    ( spl4_45
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f4186,plain,
    ( spl4_44
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f4214,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | ~ spl4_44 ),
    inference(trivial_inequality_removal,[],[f4194])).

fof(f4194,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | ~ spl4_44 ),
    inference(superposition,[],[f33,f4187])).

fof(f4187,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f4186])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f4189,plain,
    ( spl4_44
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f4167,f2512,f75,f4186])).

fof(f75,plain,
    ( spl4_6
  <=> k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f2512,plain,
    ( spl4_12
  <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f4167,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(superposition,[],[f76,f2558])).

fof(f2558,plain,
    ( ! [X1] : k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,X1))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f2537,f1264])).

fof(f1264,plain,(
    ! [X4,X2] : k2_zfmisc_1(X2,X4) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(X2,X4)) ),
    inference(forward_demodulation,[],[f1240,f45])).

fof(f45,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1240,plain,(
    ! [X4,X2] : k2_zfmisc_1(X2,X4) = k2_xboole_0(k2_zfmisc_1(k1_xboole_0,X4),k2_zfmisc_1(X2,X4)) ),
    inference(superposition,[],[f578,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f578,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X1,X0) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X2),X0),k2_zfmisc_1(X1,X0)) ),
    inference(forward_demodulation,[],[f577,f28])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f577,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X2),X0),k2_zfmisc_1(X1,X0)) = k4_xboole_0(k2_zfmisc_1(X1,X0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f550,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f550,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,k1_xboole_0)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X2),X0),k2_zfmisc_1(X1,X0)) ),
    inference(superposition,[],[f42,f28])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

fof(f2537,plain,
    ( ! [X1] : k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,X1)))
    | ~ spl4_12 ),
    inference(superposition,[],[f42,f2513])).

fof(f2513,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f2512])).

fof(f76,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f3187,plain,(
    spl4_34 ),
    inference(avatar_contradiction_clause,[],[f3186])).

fof(f3186,plain,
    ( $false
    | spl4_34 ),
    inference(trivial_inequality_removal,[],[f3185])).

fof(f3185,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_34 ),
    inference(superposition,[],[f3171,f44])).

fof(f3171,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl4_34 ),
    inference(avatar_component_clause,[],[f3170])).

fof(f3170,plain,
    ( spl4_34
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f3172,plain,
    ( ~ spl4_34
    | spl4_3
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f3160,f2560,f54,f3170])).

fof(f54,plain,
    ( spl4_3
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f2560,plain,
    ( spl4_14
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f3160,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl4_3
    | ~ spl4_14 ),
    inference(superposition,[],[f55,f2561])).

fof(f2561,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f2560])).

fof(f55,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f2630,plain,
    ( ~ spl4_26
    | spl4_2 ),
    inference(avatar_split_clause,[],[f2626,f50,f2628])).

fof(f50,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f2626,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK3)
    | spl4_2 ),
    inference(resolution,[],[f51,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f51,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f2563,plain,
    ( spl4_14
    | spl4_5
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f2557,f2512,f68,f2560])).

fof(f68,plain,
    ( spl4_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f2557,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1
    | ~ spl4_12 ),
    inference(trivial_inequality_removal,[],[f2538])).

fof(f2538,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1
    | ~ spl4_12 ),
    inference(superposition,[],[f33,f2513])).

fof(f2516,plain,
    ( spl4_12
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f2500,f2485,f2512])).

fof(f2485,plain,
    ( spl4_11
  <=> k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f2500,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl4_11 ),
    inference(superposition,[],[f28,f2486])).

fof(f2486,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f2485])).

fof(f2487,plain,
    ( spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f2432,f75,f2485])).

fof(f2432,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k1_xboole_0)
    | ~ spl4_6 ),
    inference(superposition,[],[f563,f76])).

fof(f563,plain,(
    ! [X14,X17,X15,X16] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,X15),X16),k4_xboole_0(k2_zfmisc_1(X14,X16),k2_zfmisc_1(X15,X17))) ),
    inference(superposition,[],[f29,f42])).

fof(f77,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f71,f58,f75])).

fof(f58,plain,
    ( spl4_4
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f71,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_4 ),
    inference(resolution,[],[f37,f59])).

fof(f59,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,
    ( ~ spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f65,f47,f68])).

fof(f47,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f65,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK2)
    | spl4_1 ),
    inference(resolution,[],[f36,f48])).

fof(f48,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f60,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f56,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f26,f50,f47])).

fof(f26,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:29:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (28249)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (28240)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (28241)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (28251)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (28248)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (28242)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (28237)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (28236)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (28236)Refutation not found, incomplete strategy% (28236)------------------------------
% 0.21/0.49  % (28236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28236)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (28236)Memory used [KB]: 10618
% 0.21/0.49  % (28236)Time elapsed: 0.083 s
% 0.21/0.49  % (28236)------------------------------
% 0.21/0.49  % (28236)------------------------------
% 0.21/0.50  % (28244)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (28255)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (28252)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (28254)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (28238)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (28235)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (28239)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (28253)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (28256)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (28246)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (28243)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (28247)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (28245)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (28256)Refutation not found, incomplete strategy% (28256)------------------------------
% 0.21/0.52  % (28256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28256)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28256)Memory used [KB]: 10490
% 0.21/0.52  % (28256)Time elapsed: 0.121 s
% 0.21/0.52  % (28256)------------------------------
% 0.21/0.52  % (28256)------------------------------
% 1.85/0.62  % (28241)Refutation found. Thanks to Tanya!
% 1.85/0.62  % SZS status Theorem for theBenchmark
% 2.16/0.63  % SZS output start Proof for theBenchmark
% 2.16/0.63  fof(f4254,plain,(
% 2.16/0.63    $false),
% 2.16/0.63    inference(avatar_sat_refutation,[],[f52,f56,f60,f70,f77,f2487,f2516,f2563,f2630,f3172,f3187,f4189,f4220,f4253])).
% 2.16/0.63  fof(f4253,plain,(
% 2.16/0.63    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,sK2) | k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 2.16/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.16/0.63  fof(f4220,plain,(
% 2.16/0.63    spl4_26 | spl4_45 | ~spl4_44),
% 2.16/0.63    inference(avatar_split_clause,[],[f4214,f4186,f4218,f2628])).
% 2.16/0.63  fof(f2628,plain,(
% 2.16/0.63    spl4_26 <=> k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 2.16/0.63  fof(f4218,plain,(
% 2.16/0.63    spl4_45 <=> k1_xboole_0 = sK0),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 2.16/0.63  fof(f4186,plain,(
% 2.16/0.63    spl4_44 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 2.16/0.63  fof(f4214,plain,(
% 2.16/0.63    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3) | ~spl4_44),
% 2.16/0.63    inference(trivial_inequality_removal,[],[f4194])).
% 2.16/0.63  fof(f4194,plain,(
% 2.16/0.63    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3) | ~spl4_44),
% 2.16/0.63    inference(superposition,[],[f33,f4187])).
% 2.16/0.63  fof(f4187,plain,(
% 2.16/0.63    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) | ~spl4_44),
% 2.16/0.63    inference(avatar_component_clause,[],[f4186])).
% 2.16/0.63  fof(f33,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 2.16/0.63    inference(cnf_transformation,[],[f22])).
% 2.16/0.63  fof(f22,plain,(
% 2.16/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.16/0.63    inference(flattening,[],[f21])).
% 2.16/0.63  fof(f21,plain,(
% 2.16/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.16/0.63    inference(nnf_transformation,[],[f6])).
% 2.16/0.63  fof(f6,axiom,(
% 2.16/0.63    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.16/0.63  fof(f4189,plain,(
% 2.16/0.63    spl4_44 | ~spl4_6 | ~spl4_12),
% 2.16/0.63    inference(avatar_split_clause,[],[f4167,f2512,f75,f4186])).
% 2.16/0.63  fof(f75,plain,(
% 2.16/0.63    spl4_6 <=> k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.16/0.63  fof(f2512,plain,(
% 2.16/0.63    spl4_12 <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.16/0.63  fof(f4167,plain,(
% 2.16/0.63    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) | (~spl4_6 | ~spl4_12)),
% 2.16/0.63    inference(superposition,[],[f76,f2558])).
% 2.16/0.63  fof(f2558,plain,(
% 2.16/0.63    ( ! [X1] : (k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,X1))) ) | ~spl4_12),
% 2.16/0.63    inference(forward_demodulation,[],[f2537,f1264])).
% 2.16/0.63  fof(f1264,plain,(
% 2.16/0.63    ( ! [X4,X2] : (k2_zfmisc_1(X2,X4) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(X2,X4))) )),
% 2.16/0.63    inference(forward_demodulation,[],[f1240,f45])).
% 2.16/0.63  fof(f45,plain,(
% 2.16/0.63    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.16/0.63    inference(equality_resolution,[],[f34])).
% 2.16/0.63  fof(f34,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.16/0.63    inference(cnf_transformation,[],[f22])).
% 2.16/0.63  fof(f1240,plain,(
% 2.16/0.63    ( ! [X4,X2] : (k2_zfmisc_1(X2,X4) = k2_xboole_0(k2_zfmisc_1(k1_xboole_0,X4),k2_zfmisc_1(X2,X4))) )),
% 2.16/0.63    inference(superposition,[],[f578,f29])).
% 2.16/0.63  fof(f29,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f5])).
% 2.16/0.63  fof(f5,axiom,(
% 2.16/0.63    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.16/0.63  fof(f578,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(X1,X0) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X2),X0),k2_zfmisc_1(X1,X0))) )),
% 2.16/0.63    inference(forward_demodulation,[],[f577,f28])).
% 2.16/0.63  fof(f28,plain,(
% 2.16/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/0.63    inference(cnf_transformation,[],[f4])).
% 2.16/0.63  fof(f4,axiom,(
% 2.16/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.16/0.63  fof(f577,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X2),X0),k2_zfmisc_1(X1,X0)) = k4_xboole_0(k2_zfmisc_1(X1,X0),k1_xboole_0)) )),
% 2.16/0.63    inference(forward_demodulation,[],[f550,f44])).
% 2.16/0.63  fof(f44,plain,(
% 2.16/0.63    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.16/0.63    inference(equality_resolution,[],[f35])).
% 2.16/0.63  fof(f35,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.16/0.63    inference(cnf_transformation,[],[f22])).
% 2.16/0.63  fof(f550,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,k1_xboole_0)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X2),X0),k2_zfmisc_1(X1,X0))) )),
% 2.16/0.63    inference(superposition,[],[f42,f28])).
% 2.16/0.63  fof(f42,plain,(
% 2.16/0.63    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f10])).
% 2.16/0.63  fof(f10,axiom,(
% 2.16/0.63    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).
% 2.16/0.63  fof(f2537,plain,(
% 2.16/0.63    ( ! [X1] : (k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,X1)))) ) | ~spl4_12),
% 2.16/0.63    inference(superposition,[],[f42,f2513])).
% 2.16/0.63  fof(f2513,plain,(
% 2.16/0.63    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) | ~spl4_12),
% 2.16/0.63    inference(avatar_component_clause,[],[f2512])).
% 2.16/0.63  fof(f76,plain,(
% 2.16/0.63    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_6),
% 2.16/0.63    inference(avatar_component_clause,[],[f75])).
% 2.16/0.63  fof(f3187,plain,(
% 2.16/0.63    spl4_34),
% 2.16/0.63    inference(avatar_contradiction_clause,[],[f3186])).
% 2.16/0.63  fof(f3186,plain,(
% 2.16/0.63    $false | spl4_34),
% 2.16/0.63    inference(trivial_inequality_removal,[],[f3185])).
% 2.16/0.63  fof(f3185,plain,(
% 2.16/0.63    k1_xboole_0 != k1_xboole_0 | spl4_34),
% 2.16/0.63    inference(superposition,[],[f3171,f44])).
% 2.16/0.63  fof(f3171,plain,(
% 2.16/0.63    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl4_34),
% 2.16/0.63    inference(avatar_component_clause,[],[f3170])).
% 2.16/0.63  fof(f3170,plain,(
% 2.16/0.63    spl4_34 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 2.16/0.63  fof(f3172,plain,(
% 2.16/0.63    ~spl4_34 | spl4_3 | ~spl4_14),
% 2.16/0.63    inference(avatar_split_clause,[],[f3160,f2560,f54,f3170])).
% 2.16/0.63  fof(f54,plain,(
% 2.16/0.63    spl4_3 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.16/0.63  fof(f2560,plain,(
% 2.16/0.63    spl4_14 <=> k1_xboole_0 = sK1),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.16/0.63  fof(f3160,plain,(
% 2.16/0.63    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl4_3 | ~spl4_14)),
% 2.16/0.63    inference(superposition,[],[f55,f2561])).
% 2.16/0.63  fof(f2561,plain,(
% 2.16/0.63    k1_xboole_0 = sK1 | ~spl4_14),
% 2.16/0.63    inference(avatar_component_clause,[],[f2560])).
% 2.16/0.63  fof(f55,plain,(
% 2.16/0.63    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl4_3),
% 2.16/0.63    inference(avatar_component_clause,[],[f54])).
% 2.16/0.63  fof(f2630,plain,(
% 2.16/0.63    ~spl4_26 | spl4_2),
% 2.16/0.63    inference(avatar_split_clause,[],[f2626,f50,f2628])).
% 2.16/0.63  fof(f50,plain,(
% 2.16/0.63    spl4_2 <=> r1_tarski(sK1,sK3)),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.16/0.63  fof(f2626,plain,(
% 2.16/0.63    k1_xboole_0 != k4_xboole_0(sK1,sK3) | spl4_2),
% 2.16/0.63    inference(resolution,[],[f51,f36])).
% 2.16/0.63  fof(f36,plain,(
% 2.16/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.16/0.63    inference(cnf_transformation,[],[f23])).
% 2.16/0.63  fof(f23,plain,(
% 2.16/0.63    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.16/0.63    inference(nnf_transformation,[],[f1])).
% 2.16/0.63  fof(f1,axiom,(
% 2.16/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.16/0.63  fof(f51,plain,(
% 2.16/0.63    ~r1_tarski(sK1,sK3) | spl4_2),
% 2.16/0.63    inference(avatar_component_clause,[],[f50])).
% 2.16/0.63  fof(f2563,plain,(
% 2.16/0.63    spl4_14 | spl4_5 | ~spl4_12),
% 2.16/0.63    inference(avatar_split_clause,[],[f2557,f2512,f68,f2560])).
% 2.16/0.63  fof(f68,plain,(
% 2.16/0.63    spl4_5 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.16/0.63  fof(f2557,plain,(
% 2.16/0.63    k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1 | ~spl4_12),
% 2.16/0.63    inference(trivial_inequality_removal,[],[f2538])).
% 2.16/0.63  fof(f2538,plain,(
% 2.16/0.63    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1 | ~spl4_12),
% 2.16/0.63    inference(superposition,[],[f33,f2513])).
% 2.16/0.63  fof(f2516,plain,(
% 2.16/0.63    spl4_12 | ~spl4_11),
% 2.16/0.63    inference(avatar_split_clause,[],[f2500,f2485,f2512])).
% 2.16/0.63  fof(f2485,plain,(
% 2.16/0.63    spl4_11 <=> k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k1_xboole_0)),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.16/0.63  fof(f2500,plain,(
% 2.16/0.63    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) | ~spl4_11),
% 2.16/0.63    inference(superposition,[],[f28,f2486])).
% 2.16/0.63  fof(f2486,plain,(
% 2.16/0.63    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k1_xboole_0) | ~spl4_11),
% 2.16/0.63    inference(avatar_component_clause,[],[f2485])).
% 2.16/0.63  fof(f2487,plain,(
% 2.16/0.63    spl4_11 | ~spl4_6),
% 2.16/0.63    inference(avatar_split_clause,[],[f2432,f75,f2485])).
% 2.16/0.63  fof(f2432,plain,(
% 2.16/0.63    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k1_xboole_0) | ~spl4_6),
% 2.16/0.63    inference(superposition,[],[f563,f76])).
% 2.16/0.63  fof(f563,plain,(
% 2.16/0.63    ( ! [X14,X17,X15,X16] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X14,X15),X16),k4_xboole_0(k2_zfmisc_1(X14,X16),k2_zfmisc_1(X15,X17)))) )),
% 2.16/0.63    inference(superposition,[],[f29,f42])).
% 2.16/0.63  fof(f77,plain,(
% 2.16/0.63    spl4_6 | ~spl4_4),
% 2.16/0.63    inference(avatar_split_clause,[],[f71,f58,f75])).
% 2.16/0.63  fof(f58,plain,(
% 2.16/0.63    spl4_4 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.16/0.63  fof(f71,plain,(
% 2.16/0.63    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_4),
% 2.16/0.63    inference(resolution,[],[f37,f59])).
% 2.16/0.63  fof(f59,plain,(
% 2.16/0.63    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_4),
% 2.16/0.63    inference(avatar_component_clause,[],[f58])).
% 2.16/0.63  fof(f37,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.16/0.63    inference(cnf_transformation,[],[f23])).
% 2.16/0.63  fof(f70,plain,(
% 2.16/0.63    ~spl4_5 | spl4_1),
% 2.16/0.63    inference(avatar_split_clause,[],[f65,f47,f68])).
% 2.16/0.63  fof(f47,plain,(
% 2.16/0.63    spl4_1 <=> r1_tarski(sK0,sK2)),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.16/0.63  fof(f65,plain,(
% 2.16/0.63    k1_xboole_0 != k4_xboole_0(sK0,sK2) | spl4_1),
% 2.16/0.63    inference(resolution,[],[f36,f48])).
% 2.16/0.63  fof(f48,plain,(
% 2.16/0.63    ~r1_tarski(sK0,sK2) | spl4_1),
% 2.16/0.63    inference(avatar_component_clause,[],[f47])).
% 2.16/0.63  fof(f60,plain,(
% 2.16/0.63    spl4_4),
% 2.16/0.63    inference(avatar_split_clause,[],[f24,f58])).
% 2.16/0.63  fof(f24,plain,(
% 2.16/0.63    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.16/0.63    inference(cnf_transformation,[],[f20])).
% 2.16/0.63  fof(f20,plain,(
% 2.16/0.63    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.16/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f19])).
% 2.16/0.63  fof(f19,plain,(
% 2.16/0.63    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 2.16/0.63    introduced(choice_axiom,[])).
% 2.16/0.63  fof(f15,plain,(
% 2.16/0.63    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.16/0.63    inference(flattening,[],[f14])).
% 2.16/0.63  fof(f14,plain,(
% 2.16/0.63    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.16/0.63    inference(ennf_transformation,[],[f13])).
% 2.16/0.63  fof(f13,negated_conjecture,(
% 2.16/0.63    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.16/0.63    inference(negated_conjecture,[],[f12])).
% 2.16/0.63  fof(f12,conjecture,(
% 2.16/0.63    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 2.16/0.63  fof(f56,plain,(
% 2.16/0.63    ~spl4_3),
% 2.16/0.63    inference(avatar_split_clause,[],[f25,f54])).
% 2.16/0.63  fof(f25,plain,(
% 2.16/0.63    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 2.16/0.63    inference(cnf_transformation,[],[f20])).
% 2.16/0.63  fof(f52,plain,(
% 2.16/0.63    ~spl4_1 | ~spl4_2),
% 2.16/0.63    inference(avatar_split_clause,[],[f26,f50,f47])).
% 2.16/0.63  fof(f26,plain,(
% 2.16/0.63    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 2.16/0.63    inference(cnf_transformation,[],[f20])).
% 2.16/0.63  % SZS output end Proof for theBenchmark
% 2.16/0.63  % (28241)------------------------------
% 2.16/0.63  % (28241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.63  % (28241)Termination reason: Refutation
% 2.16/0.63  
% 2.16/0.63  % (28241)Memory used [KB]: 13048
% 2.16/0.63  % (28241)Time elapsed: 0.192 s
% 2.16/0.63  % (28241)------------------------------
% 2.16/0.63  % (28241)------------------------------
% 2.16/0.64  % (28230)Success in time 0.281 s
%------------------------------------------------------------------------------

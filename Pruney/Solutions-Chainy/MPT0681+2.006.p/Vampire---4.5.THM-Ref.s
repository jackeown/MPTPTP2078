%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 106 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  160 ( 358 expanded)
%              Number of equality atoms :   32 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f863,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f807,f809,f811,f836,f838,f862])).

fof(f862,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f861])).

fof(f861,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f860,f22])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_xboole_0(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_xboole_0(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

fof(f860,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(trivial_inequality_removal,[],[f859])).

fof(f859,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(superposition,[],[f806,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f50,f28])).

fof(f28,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f50,plain,(
    ! [X0] :
      ( k2_relat_1(k1_xboole_0) = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k2_relat_1(k1_xboole_0) = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f33,f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f806,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f804])).

fof(f804,plain,
    ( spl3_10
  <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f838,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f837])).

fof(f837,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f790,f24])).

fof(f24,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f790,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f788])).

fof(f788,plain,
    ( spl3_6
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f836,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f835])).

fof(f835,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f802,f25])).

fof(f25,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f802,plain,
    ( ~ v2_funct_1(sK2)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f800])).

fof(f800,plain,
    ( spl3_9
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f811,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f810])).

fof(f810,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f798,f23])).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f798,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f796])).

fof(f796,plain,
    ( spl3_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f809,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f808])).

fof(f808,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f794,f22])).

fof(f794,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f792])).

fof(f792,plain,
    ( spl3_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f807,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f763,f804,f800,f796,f792,f788])).

fof(f763,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f377,f26])).

fof(f26,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f377,plain,(
    ! [X4,X2,X3] :
      ( r1_xboole_0(k9_relat_1(X4,X2),k9_relat_1(X4,X3))
      | k1_xboole_0 != k9_relat_1(X4,k1_xboole_0)
      | ~ v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f97,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f97,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 != k9_relat_1(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))
      | r1_xboole_0(k9_relat_1(X3,X4),k9_relat_1(X3,X5))
      | ~ v2_funct_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f40,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f38,f32,f32])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f32])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 21:02:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (28370)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.44  % (28370)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f863,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f807,f809,f811,f836,f838,f862])).
% 0.22/0.44  fof(f862,plain,(
% 0.22/0.44    spl3_10),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f861])).
% 0.22/0.44  fof(f861,plain,(
% 0.22/0.44    $false | spl3_10),
% 0.22/0.44    inference(resolution,[],[f860,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    v1_relat_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.44    inference(flattening,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.44    inference(ennf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.44    inference(negated_conjecture,[],[f10])).
% 0.22/0.44  fof(f10,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).
% 0.22/0.44  fof(f860,plain,(
% 0.22/0.44    ~v1_relat_1(sK2) | spl3_10),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f859])).
% 0.22/0.44  fof(f859,plain,(
% 0.22/0.44    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | spl3_10),
% 0.22/0.44    inference(superposition,[],[f806,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f50,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(duplicate_literal_removal,[],[f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(superposition,[],[f33,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.44  fof(f806,plain,(
% 0.22/0.44    k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) | spl3_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f804])).
% 0.22/0.44  fof(f804,plain,(
% 0.22/0.44    spl3_10 <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.44  fof(f838,plain,(
% 0.22/0.44    spl3_6),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f837])).
% 0.22/0.44  fof(f837,plain,(
% 0.22/0.44    $false | spl3_6),
% 0.22/0.44    inference(resolution,[],[f790,f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    r1_xboole_0(sK0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f790,plain,(
% 0.22/0.44    ~r1_xboole_0(sK0,sK1) | spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f788])).
% 0.22/0.44  fof(f788,plain,(
% 0.22/0.44    spl3_6 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f836,plain,(
% 0.22/0.44    spl3_9),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f835])).
% 0.22/0.44  fof(f835,plain,(
% 0.22/0.44    $false | spl3_9),
% 0.22/0.44    inference(resolution,[],[f802,f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    v2_funct_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f802,plain,(
% 0.22/0.44    ~v2_funct_1(sK2) | spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f800])).
% 0.22/0.44  fof(f800,plain,(
% 0.22/0.44    spl3_9 <=> v2_funct_1(sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f811,plain,(
% 0.22/0.44    spl3_8),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f810])).
% 0.22/0.44  fof(f810,plain,(
% 0.22/0.44    $false | spl3_8),
% 0.22/0.44    inference(resolution,[],[f798,f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    v1_funct_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f798,plain,(
% 0.22/0.44    ~v1_funct_1(sK2) | spl3_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f796])).
% 0.22/0.44  fof(f796,plain,(
% 0.22/0.44    spl3_8 <=> v1_funct_1(sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.44  fof(f809,plain,(
% 0.22/0.44    spl3_7),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f808])).
% 0.22/0.44  fof(f808,plain,(
% 0.22/0.44    $false | spl3_7),
% 0.22/0.44    inference(resolution,[],[f794,f22])).
% 0.22/0.44  fof(f794,plain,(
% 0.22/0.44    ~v1_relat_1(sK2) | spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f792])).
% 0.22/0.44  fof(f792,plain,(
% 0.22/0.44    spl3_7 <=> v1_relat_1(sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f807,plain,(
% 0.22/0.44    ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f763,f804,f800,f796,f792,f788])).
% 0.22/0.44  fof(f763,plain,(
% 0.22/0.44    k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r1_xboole_0(sK0,sK1)),
% 0.22/0.44    inference(resolution,[],[f377,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f377,plain,(
% 0.22/0.44    ( ! [X4,X2,X3] : (r1_xboole_0(k9_relat_1(X4,X2),k9_relat_1(X4,X3)) | k1_xboole_0 != k9_relat_1(X4,k1_xboole_0) | ~v2_funct_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~r1_xboole_0(X2,X3)) )),
% 0.22/0.44    inference(superposition,[],[f97,f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f36,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(nnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.44  fof(f97,plain,(
% 0.22/0.44    ( ! [X4,X5,X3] : (k1_xboole_0 != k9_relat_1(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5))) | r1_xboole_0(k9_relat_1(X3,X4),k9_relat_1(X3,X5)) | ~v2_funct_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.22/0.44    inference(superposition,[],[f40,f42])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f38,f32,f32])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(flattening,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f37,f32])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (28370)------------------------------
% 0.22/0.44  % (28370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (28370)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (28370)Memory used [KB]: 6524
% 0.22/0.44  % (28370)Time elapsed: 0.020 s
% 0.22/0.44  % (28370)------------------------------
% 0.22/0.44  % (28370)------------------------------
% 0.22/0.45  % (28365)Success in time 0.083 s
%------------------------------------------------------------------------------

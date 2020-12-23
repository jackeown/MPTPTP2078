%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 102 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 219 expanded)
%              Number of equality atoms :   45 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f64,f76,f89,f90])).

fof(f90,plain,
    ( ~ spl3_2
    | spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl3_2
    | spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f52,f82])).

fof(f82,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f81,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_5
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f81,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f80,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f29,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f80,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f77,f47])).

fof(f47,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f77,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k2_relat_1(k1_xboole_0),X0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f63,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f63,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f52,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_3
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f89,plain,
    ( ~ spl3_2
    | spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl3_2
    | spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_2
    | spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f52,f82])).

fof(f76,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f69,f61,f45,f40,f73])).

fof(f40,plain,
    ( spl3_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f69,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f68,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f68,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f66,f47])).

fof(f66,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f63,f32])).

fof(f32,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f64,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f57,f61])).

fof(f57,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f56,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f56,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f54,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f54,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f53,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f26,f50])).

fof(f26,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f20])).

fof(f20,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(f48,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f45])).

fof(f28,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f43,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f40])).

fof(f27,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (26176)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (26176)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f43,f48,f53,f64,f76,f89,f90])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    ~spl3_2 | spl3_3 | ~spl3_4 | ~spl3_5),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f84])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    $false | (~spl3_2 | spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f52,f82])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl3_2 | ~spl3_4 | ~spl3_5)),
% 0.20/0.46    inference(forward_demodulation,[],[f81,f75])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f73])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    spl3_5 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)) ) | (~spl3_2 | ~spl3_4)),
% 0.20/0.46    inference(forward_demodulation,[],[f80,f58])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f29,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ) | (~spl3_2 | ~spl3_4)),
% 0.20/0.46    inference(forward_demodulation,[],[f77,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl3_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k2_relat_1(k1_xboole_0),X0))) ) | ~spl3_4),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f63,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    v1_relat_1(k1_xboole_0) | ~spl3_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f61])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    spl3_4 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    spl3_3 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    ~spl3_2 | spl3_3 | ~spl3_4 | ~spl3_5),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f88])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    $false | (~spl3_2 | spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f86])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    k1_xboole_0 != k1_xboole_0 | (~spl3_2 | spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.20/0.46    inference(superposition,[],[f52,f82])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    spl3_5 | ~spl3_1 | ~spl3_2 | ~spl3_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f69,f61,f45,f40,f73])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    spl3_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.20/0.46    inference(forward_demodulation,[],[f68,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f40])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl3_2 | ~spl3_4)),
% 0.20/0.46    inference(forward_demodulation,[],[f66,f47])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) | ~spl3_4),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f63,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    spl3_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f57,f61])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    v1_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f56,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.20/0.46    inference(unused_predicate_definition_removal,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f54,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f30,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(rectify,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ~spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f50])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,negated_conjecture,(
% 0.20/0.46    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.20/0.46    inference(negated_conjecture,[],[f10])).
% 0.20/0.46  fof(f10,conjecture,(
% 0.20/0.46    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f28,f45])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f40])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (26176)------------------------------
% 0.20/0.46  % (26176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (26176)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (26176)Memory used [KB]: 1663
% 0.20/0.46  % (26176)Time elapsed: 0.058 s
% 0.20/0.46  % (26176)------------------------------
% 0.20/0.46  % (26176)------------------------------
% 0.20/0.46  % (26168)Success in time 0.11 s
%------------------------------------------------------------------------------

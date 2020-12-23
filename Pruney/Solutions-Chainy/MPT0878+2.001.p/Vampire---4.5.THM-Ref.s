%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  99 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  143 ( 258 expanded)
%              Number of equality atoms :   89 ( 179 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f54,f67,f90,f96,f104,f105,f119,f134])).

fof(f134,plain,
    ( ~ spl2_6
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl2_6
    | spl2_7 ),
    inference(unit_resulting_resolution,[],[f65,f65,f62,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f62,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_6
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f65,plain,
    ( k1_xboole_0 != sK0
    | spl2_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl2_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f119,plain,
    ( spl2_3
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f44,f44,f49,f18])).

fof(f49,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_4
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f44,plain,
    ( k1_xboole_0 != sK1
    | spl2_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f105,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK0)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f104,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl2_9 ),
    inference(unit_resulting_resolution,[],[f26,f95])).

fof(f95,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_9
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f26,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f96,plain,
    ( ~ spl2_9
    | spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f91,f64,f60,f93])).

fof(f91,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | spl2_6
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f61,f66])).

fof(f66,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f61,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f90,plain,
    ( ~ spl2_3
    | spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f89,f64,f28,f43])).

fof(f28,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f89,plain,
    ( k1_xboole_0 != sK1
    | spl2_1
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f30,f66])).

fof(f30,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f67,plain,
    ( spl2_1
    | spl2_6
    | spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f58,f33,f64,f60,f28])).

fof(f33,plain,
    ( spl2_2
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f58,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | sK0 = sK1
    | ~ spl2_2 ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,
    ( ! [X4,X5] :
        ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) != k2_zfmisc_1(X4,X5)
        | k1_xboole_0 = X5
        | k1_xboole_0 = X4
        | sK1 = X5 )
    | ~ spl2_2 ),
    inference(superposition,[],[f23,f35])).

fof(f35,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f54,plain,
    ( spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f41,f33,f51,f47,f43])).

fof(f51,plain,
    ( spl2_5
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f41,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(superposition,[],[f18,f35])).

fof(f36,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f33])).

fof(f24,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(definition_unfolding,[],[f15,f21,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f15,plain,(
    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK0 != sK1
    & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) )
   => ( sK0 != sK1
      & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

fof(f31,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f16,f28])).

fof(f16,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (1054)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.48  % (1054)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f31,f36,f54,f67,f90,f96,f104,f105,f119,f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ~spl2_6 | spl2_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    $false | (~spl2_6 | spl2_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f65,f65,f62,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | ~spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl2_6 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | spl2_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl2_7 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl2_3 | ~spl2_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    $false | (spl2_3 | ~spl2_4)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f44,f44,f49,f18])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | ~spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl2_4 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl2_3 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK0) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl2_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    $false | spl2_9),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f26,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | spl2_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl2_9 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ~spl2_9 | spl2_6 | ~spl2_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f91,f64,f60,f93])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (spl2_6 | ~spl2_7)),
% 0.21/0.49    inference(forward_demodulation,[],[f61,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~spl2_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f64])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    k1_xboole_0 != k2_zfmisc_1(sK0,sK0) | spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~spl2_3 | spl2_1 | ~spl2_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f89,f64,f28,f43])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    spl2_1 <=> sK0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | (spl2_1 | ~spl2_7)),
% 0.21/0.49    inference(backward_demodulation,[],[f30,f66])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    sK0 != sK1 | spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f28])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl2_1 | spl2_6 | spl2_7 | ~spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f33,f64,f60,f28])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    spl2_2 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | sK0 = sK1 | ~spl2_2),
% 0.21/0.49    inference(equality_resolution,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = X5 | k1_xboole_0 = X4 | sK1 = X5) ) | ~spl2_2),
% 0.21/0.49    inference(superposition,[],[f23,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | ~spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f33])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X3) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl2_3 | spl2_4 | ~spl2_5 | ~spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f33,f51,f47,f43])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl2_5 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | k1_xboole_0 = sK1 | ~spl2_2),
% 0.21/0.49    inference(superposition,[],[f18,f35])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f33])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.21/0.49    inference(definition_unfolding,[],[f15,f21,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    sK0 != sK1 & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1] : (X0 != X1 & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)) => (sK0 != sK1 & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1] : (X0 != X1 & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ~spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f28])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    sK0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (1054)------------------------------
% 0.21/0.49  % (1054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1054)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (1054)Memory used [KB]: 10746
% 0.21/0.49  % (1054)Time elapsed: 0.098 s
% 0.21/0.49  % (1054)------------------------------
% 0.21/0.49  % (1054)------------------------------
% 0.21/0.49  % (1035)Success in time 0.132 s
%------------------------------------------------------------------------------

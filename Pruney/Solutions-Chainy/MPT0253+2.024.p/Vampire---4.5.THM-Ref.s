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
% DateTime   : Thu Dec  3 12:39:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 126 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  242 ( 393 expanded)
%              Number of equality atoms :   46 (  83 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f261,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f49,f53,f57,f61,f65,f73,f86,f101,f170,f191,f222,f260])).

fof(f260,plain,
    ( ~ spl4_3
    | spl4_15
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl4_3
    | spl4_15
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f253,f98])).

fof(f98,plain,
    ( sK1 != k2_xboole_0(sK1,k2_tarski(sK0,sK2))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_15
  <=> sK1 = k2_xboole_0(sK1,k2_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f253,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tarski(sK0,sK2))
    | ~ spl4_3
    | ~ spl4_30 ),
    inference(resolution,[],[f221,f44])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | sK1 = k2_xboole_0(sK1,k2_tarski(X0,sK2)) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl4_30
  <=> ! [X0] :
        ( sK1 = k2_xboole_0(sK1,k2_tarski(X0,sK2))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f222,plain,
    ( spl4_30
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f218,f189,f55,f37,f220])).

fof(f37,plain,
    ( spl4_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f55,plain,
    ( spl4_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f189,plain,
    ( spl4_29
  <=> ! [X9,X8,X10] :
        ( k2_xboole_0(k2_tarski(X8,X9),X10) = X10
        | ~ r2_hidden(X9,X10)
        | ~ r2_hidden(X8,X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f218,plain,
    ( ! [X0] :
        ( sK1 = k2_xboole_0(sK1,k2_tarski(X0,sK2))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f210,f56])).

fof(f56,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f210,plain,
    ( ! [X0] :
        ( sK1 = k2_xboole_0(k2_tarski(X0,sK2),sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_2
    | ~ spl4_29 ),
    inference(resolution,[],[f190,f39])).

fof(f39,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f190,plain,
    ( ! [X10,X8,X9] :
        ( ~ r2_hidden(X9,X10)
        | k2_xboole_0(k2_tarski(X8,X9),X10) = X10
        | ~ r2_hidden(X8,X10) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f189])).

fof(f191,plain,
    ( spl4_29
    | ~ spl4_10
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f175,f168,f71,f189])).

fof(f71,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f168,plain,
    ( spl4_25
  <=> ! [X9,X8] :
        ( k2_xboole_0(X8,X9) = X9
        | ~ r1_tarski(X8,X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f175,plain,
    ( ! [X10,X8,X9] :
        ( k2_xboole_0(k2_tarski(X8,X9),X10) = X10
        | ~ r2_hidden(X9,X10)
        | ~ r2_hidden(X8,X10) )
    | ~ spl4_10
    | ~ spl4_25 ),
    inference(resolution,[],[f169,f72])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f169,plain,
    ( ! [X8,X9] :
        ( ~ r1_tarski(X8,X9)
        | k2_xboole_0(X8,X9) = X9 )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f168])).

fof(f170,plain,
    ( spl4_25
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f166,f84,f63,f59,f168])).

fof(f59,plain,
    ( spl4_7
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(X0,X2) = X1
        | ~ r1_tarski(X1,sK3(X0,X1,X2))
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f63,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(X0,X2) = X1
        | r1_tarski(X2,sK3(X0,X1,X2))
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f84,plain,
    ( spl4_13
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f166,plain,
    ( ! [X8,X9] :
        ( k2_xboole_0(X8,X9) = X9
        | ~ r1_tarski(X8,X9) )
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f157,f85])).

fof(f85,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f157,plain,
    ( ! [X8,X9] :
        ( k2_xboole_0(X8,X9) = X9
        | ~ r1_tarski(X9,X9)
        | ~ r1_tarski(X8,X9) )
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( ! [X8,X9] :
        ( k2_xboole_0(X8,X9) = X9
        | ~ r1_tarski(X9,X9)
        | ~ r1_tarski(X8,X9)
        | k2_xboole_0(X8,X9) = X9
        | ~ r1_tarski(X9,X9)
        | ~ r1_tarski(X8,X9) )
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(resolution,[],[f64,f60])).

fof(f60,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,sK3(X0,X1,X2))
        | k2_xboole_0(X0,X2) = X1
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X2,sK3(X0,X1,X2))
        | k2_xboole_0(X0,X2) = X1
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f101,plain,
    ( ~ spl4_15
    | spl4_1
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f90,f55,f32,f96])).

fof(f32,plain,
    ( spl4_1
  <=> sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f90,plain,
    ( sK1 != k2_xboole_0(sK1,k2_tarski(sK0,sK2))
    | spl4_1
    | ~ spl4_6 ),
    inference(superposition,[],[f34,f56])).

fof(f34,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f86,plain,
    ( spl4_13
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f82,f51,f47,f84])).

fof(f47,plain,
    ( spl4_4
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f51,plain,
    ( spl4_5
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f82,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f52,f48])).

fof(f48,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f52,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f73,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f65,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X2,sK3(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK3(X0,X1,X2))
        & r1_tarski(X2,sK3(X0,X1,X2))
        & r1_tarski(X0,sK3(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK3(X0,X1,X2))
        & r1_tarski(X2,sK3(X0,X1,X2))
        & r1_tarski(X0,sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f61,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X1,sK3(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f53,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f49,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f45,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f42])).

fof(f19,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f40,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f20,f37])).

fof(f20,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f32])).

fof(f21,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:07:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (27091)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.42  % (27092)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.42  % (27091)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f261,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f35,f40,f45,f49,f53,f57,f61,f65,f73,f86,f101,f170,f191,f222,f260])).
% 0.21/0.42  fof(f260,plain,(
% 0.21/0.42    ~spl4_3 | spl4_15 | ~spl4_30),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f259])).
% 0.21/0.42  fof(f259,plain,(
% 0.21/0.42    $false | (~spl4_3 | spl4_15 | ~spl4_30)),
% 0.21/0.42    inference(subsumption_resolution,[],[f253,f98])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    sK1 != k2_xboole_0(sK1,k2_tarski(sK0,sK2)) | spl4_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f96])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    spl4_15 <=> sK1 = k2_xboole_0(sK1,k2_tarski(sK0,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.42  fof(f253,plain,(
% 0.21/0.42    sK1 = k2_xboole_0(sK1,k2_tarski(sK0,sK2)) | (~spl4_3 | ~spl4_30)),
% 0.21/0.42    inference(resolution,[],[f221,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    r2_hidden(sK0,sK1) | ~spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl4_3 <=> r2_hidden(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f221,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,sK1) | sK1 = k2_xboole_0(sK1,k2_tarski(X0,sK2))) ) | ~spl4_30),
% 0.21/0.42    inference(avatar_component_clause,[],[f220])).
% 0.21/0.42  fof(f220,plain,(
% 0.21/0.42    spl4_30 <=> ! [X0] : (sK1 = k2_xboole_0(sK1,k2_tarski(X0,sK2)) | ~r2_hidden(X0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.42  fof(f222,plain,(
% 0.21/0.42    spl4_30 | ~spl4_2 | ~spl4_6 | ~spl4_29),
% 0.21/0.42    inference(avatar_split_clause,[],[f218,f189,f55,f37,f220])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl4_2 <=> r2_hidden(sK2,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl4_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f189,plain,(
% 0.21/0.42    spl4_29 <=> ! [X9,X8,X10] : (k2_xboole_0(k2_tarski(X8,X9),X10) = X10 | ~r2_hidden(X9,X10) | ~r2_hidden(X8,X10))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.42  fof(f218,plain,(
% 0.21/0.42    ( ! [X0] : (sK1 = k2_xboole_0(sK1,k2_tarski(X0,sK2)) | ~r2_hidden(X0,sK1)) ) | (~spl4_2 | ~spl4_6 | ~spl4_29)),
% 0.21/0.42    inference(forward_demodulation,[],[f210,f56])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f55])).
% 0.21/0.42  fof(f210,plain,(
% 0.21/0.42    ( ! [X0] : (sK1 = k2_xboole_0(k2_tarski(X0,sK2),sK1) | ~r2_hidden(X0,sK1)) ) | (~spl4_2 | ~spl4_29)),
% 0.21/0.42    inference(resolution,[],[f190,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    r2_hidden(sK2,sK1) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f37])).
% 0.21/0.42  fof(f190,plain,(
% 0.21/0.42    ( ! [X10,X8,X9] : (~r2_hidden(X9,X10) | k2_xboole_0(k2_tarski(X8,X9),X10) = X10 | ~r2_hidden(X8,X10)) ) | ~spl4_29),
% 0.21/0.42    inference(avatar_component_clause,[],[f189])).
% 0.21/0.42  fof(f191,plain,(
% 0.21/0.42    spl4_29 | ~spl4_10 | ~spl4_25),
% 0.21/0.42    inference(avatar_split_clause,[],[f175,f168,f71,f189])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    spl4_10 <=> ! [X1,X0,X2] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.42  fof(f168,plain,(
% 0.21/0.42    spl4_25 <=> ! [X9,X8] : (k2_xboole_0(X8,X9) = X9 | ~r1_tarski(X8,X9))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.42  fof(f175,plain,(
% 0.21/0.42    ( ! [X10,X8,X9] : (k2_xboole_0(k2_tarski(X8,X9),X10) = X10 | ~r2_hidden(X9,X10) | ~r2_hidden(X8,X10)) ) | (~spl4_10 | ~spl4_25)),
% 0.21/0.42    inference(resolution,[],[f169,f72])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) ) | ~spl4_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f71])).
% 0.21/0.42  fof(f169,plain,(
% 0.21/0.42    ( ! [X8,X9] : (~r1_tarski(X8,X9) | k2_xboole_0(X8,X9) = X9) ) | ~spl4_25),
% 0.21/0.42    inference(avatar_component_clause,[],[f168])).
% 0.21/0.42  fof(f170,plain,(
% 0.21/0.42    spl4_25 | ~spl4_7 | ~spl4_8 | ~spl4_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f166,f84,f63,f59,f168])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl4_7 <=> ! [X1,X0,X2] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK3(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl4_8 <=> ! [X1,X0,X2] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X2,sK3(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    spl4_13 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.42  fof(f166,plain,(
% 0.21/0.42    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = X9 | ~r1_tarski(X8,X9)) ) | (~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.21/0.42    inference(subsumption_resolution,[],[f157,f85])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl4_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f84])).
% 0.21/0.42  fof(f157,plain,(
% 0.21/0.42    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = X9 | ~r1_tarski(X9,X9) | ~r1_tarski(X8,X9)) ) | (~spl4_7 | ~spl4_8)),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f156])).
% 0.21/0.42  fof(f156,plain,(
% 0.21/0.42    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = X9 | ~r1_tarski(X9,X9) | ~r1_tarski(X8,X9) | k2_xboole_0(X8,X9) = X9 | ~r1_tarski(X9,X9) | ~r1_tarski(X8,X9)) ) | (~spl4_7 | ~spl4_8)),
% 0.21/0.42    inference(resolution,[],[f64,f60])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK3(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f59])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X2,sK3(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) ) | ~spl4_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f63])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    ~spl4_15 | spl4_1 | ~spl4_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f90,f55,f32,f96])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl4_1 <=> sK1 = k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    sK1 != k2_xboole_0(sK1,k2_tarski(sK0,sK2)) | (spl4_1 | ~spl4_6)),
% 0.21/0.43    inference(superposition,[],[f34,f56])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) | spl4_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f32])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    spl4_13 | ~spl4_4 | ~spl4_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f82,f51,f47,f84])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl4_4 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl4_5 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl4_4 | ~spl4_5)),
% 0.21/0.43    inference(superposition,[],[f52,f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl4_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f47])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl4_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f51])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl4_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f30,f71])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.43    inference(flattening,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.43    inference(nnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    spl4_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f63])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X2,sK3(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK3(X0,X1,X2)) & r1_tarski(X2,sK3(X0,X1,X2)) & r1_tarski(X0,sK3(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK3(X0,X1,X2)) & r1_tarski(X2,sK3(X0,X1,X2)) & r1_tarski(X0,sK3(X0,X1,X2))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    spl4_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f59])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK3(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl4_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f55])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl4_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f51])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl4_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f47])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.43    inference(rectify,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl4_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f19,f42])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f37])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    r2_hidden(sK2,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ~spl4_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f32])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (27091)------------------------------
% 0.21/0.43  % (27091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (27091)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (27091)Memory used [KB]: 6268
% 0.21/0.43  % (27091)Time elapsed: 0.012 s
% 0.21/0.43  % (27091)------------------------------
% 0.21/0.43  % (27091)------------------------------
% 0.21/0.43  % (27080)Success in time 0.069 s
%------------------------------------------------------------------------------

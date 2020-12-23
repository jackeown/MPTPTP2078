%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 117 expanded)
%              Number of leaves         :   19 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  202 ( 536 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f43,f47,f51,f55,f78,f80,f86,f100,f101])).

fof(f101,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f100,plain,
    ( ~ spl3_5
    | spl3_14
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f94,f84,f41,f37,f97,f49])).

fof(f49,plain,
    ( spl3_5
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f97,plain,
    ( spl3_14
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f37,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f41,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f84,plain,
    ( spl3_12
  <=> ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | ~ v3_ordinal1(X2)
        | ~ r2_xboole_0(sK0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f94,plain,
    ( ~ r2_hidden(sK1,sK2)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(resolution,[],[f87,f42])).

fof(f42,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r2_hidden(X0,sK2)
        | sK0 = X0
        | ~ v3_ordinal1(X0) )
    | ~ spl3_12 ),
    inference(resolution,[],[f85,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f85,plain,
    ( ! [X2] :
        ( ~ r2_xboole_0(sK0,X2)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK2) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( ~ spl3_6
    | spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f82,f76,f84,f53])).

fof(f53,plain,
    ( spl3_6
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f76,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f82,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | ~ r2_xboole_0(sK0,X2)
        | ~ v3_ordinal1(X2)
        | ~ v1_ordinal1(sK0) )
    | ~ spl3_11 ),
    inference(resolution,[],[f77,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f77,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f80,plain,
    ( ~ spl3_4
    | spl3_10 ),
    inference(avatar_split_clause,[],[f79,f73,f45])).

fof(f45,plain,
    ( spl3_4
  <=> v3_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f73,plain,
    ( spl3_10
  <=> v1_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f79,plain,
    ( ~ v3_ordinal1(sK2)
    | spl3_10 ),
    inference(resolution,[],[f74,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f74,plain,
    ( ~ v1_ordinal1(sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f78,plain,
    ( ~ spl3_10
    | spl3_11
    | spl3_1 ),
    inference(avatar_split_clause,[],[f71,f33,f76,f73])).

fof(f33,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(sK0,X0)
        | ~ v1_ordinal1(sK2) )
    | spl3_1 ),
    inference(resolution,[],[f31,f34])).

fof(f34,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1)
      | ~ v1_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1)
      | ~ v1_ordinal1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1)
      | ~ v1_ordinal1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_ordinal1(X2)
     => ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X1) )
       => r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_ordinal1)).

fof(f55,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    v1_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r2_hidden(sK1,sK2)
    & r1_tarski(sK0,sK1)
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1)
    & v1_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X0,X2)
                & r2_hidden(X1,X2)
                & r1_tarski(X0,X1)
                & v3_ordinal1(X2) )
            & v3_ordinal1(X1) )
        & v1_ordinal1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(sK0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(sK0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_hidden(sK0,X2)
            & r2_hidden(X1,X2)
            & r1_tarski(sK0,X1)
            & v3_ordinal1(X2) )
        & v3_ordinal1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(sK0,X2)
          & r2_hidden(sK1,X2)
          & r1_tarski(sK0,sK1)
          & v3_ordinal1(X2) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ~ r2_hidden(sK0,X2)
        & r2_hidden(sK1,X2)
        & r1_tarski(sK0,sK1)
        & v3_ordinal1(X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r2_hidden(sK1,sK2)
      & r1_tarski(sK0,sK1)
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r2_hidden(X1,X2)
                    & r1_tarski(X0,X1) )
                 => r2_hidden(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

fof(f51,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f41])).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f37])).

fof(f26,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f27,f33])).

fof(f27,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (22657)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.45  % (22657)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f35,f39,f43,f47,f51,f55,f78,f80,f86,f100,f101])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    sK0 != sK1 | r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 0.21/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    ~spl3_5 | spl3_14 | ~spl3_2 | ~spl3_3 | ~spl3_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f94,f84,f41,f37,f97,f49])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl3_5 <=> v3_ordinal1(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    spl3_14 <=> sK0 = sK1),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    spl3_2 <=> r2_hidden(sK1,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    spl3_12 <=> ! [X2] : (~r2_hidden(X2,sK2) | ~v3_ordinal1(X2) | ~r2_xboole_0(sK0,X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ~r2_hidden(sK1,sK2) | sK0 = sK1 | ~v3_ordinal1(sK1) | (~spl3_3 | ~spl3_12)),
% 0.21/0.45    inference(resolution,[],[f87,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f41])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r2_hidden(X0,sK2) | sK0 = X0 | ~v3_ordinal1(X0)) ) | ~spl3_12),
% 0.21/0.45    inference(resolution,[],[f85,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.21/0.45    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    ( ! [X2] : (~r2_xboole_0(sK0,X2) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK2)) ) | ~spl3_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f84])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    ~spl3_6 | spl3_12 | ~spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f82,f76,f84,f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl3_6 <=> v1_ordinal1(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl3_11 <=> ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(sK0,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    ( ! [X2] : (~r2_hidden(X2,sK2) | ~r2_xboole_0(sK0,X2) | ~v3_ordinal1(X2) | ~v1_ordinal1(sK0)) ) | ~spl3_11),
% 0.21/0.45    inference(resolution,[],[f77,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r2_hidden(X0,sK2)) ) | ~spl3_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f76])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ~spl3_4 | spl3_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f79,f73,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    spl3_4 <=> v3_ordinal1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    spl3_10 <=> v1_ordinal1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ~v3_ordinal1(sK2) | spl3_10),
% 0.21/0.45    inference(resolution,[],[f74,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.21/0.45    inference(pure_predicate_removal,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ~v1_ordinal1(sK2) | spl3_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f73])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ~spl3_10 | spl3_11 | spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f71,f33,f76,f73])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    spl3_1 <=> r2_hidden(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(sK0,X0) | ~v1_ordinal1(sK2)) ) | spl3_1),
% 0.21/0.45    inference(resolution,[],[f31,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ~r2_hidden(sK0,sK2) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f33])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1) | ~v1_ordinal1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1) | ~v1_ordinal1(X2))),
% 0.21/0.45    inference(flattening,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r2_hidden(X0,X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X1))) | ~v1_ordinal1(X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_ordinal1(X2) => ((r2_hidden(X1,X2) & r2_hidden(X0,X1)) => r2_hidden(X0,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_ordinal1)).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f53])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    v1_ordinal1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ((~r2_hidden(sK0,sK2) & r2_hidden(sK1,sK2) & r1_tarski(sK0,sK1) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)) & v1_ordinal1(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19,f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r1_tarski(X0,X1) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_ordinal1(X0)) => (? [X1] : (? [X2] : (~r2_hidden(sK0,X2) & r2_hidden(X1,X2) & r1_tarski(sK0,X1) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_ordinal1(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : (~r2_hidden(sK0,X2) & r2_hidden(X1,X2) & r1_tarski(sK0,X1) & v3_ordinal1(X2)) & v3_ordinal1(X1)) => (? [X2] : (~r2_hidden(sK0,X2) & r2_hidden(sK1,X2) & r1_tarski(sK0,sK1) & v3_ordinal1(X2)) & v3_ordinal1(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ? [X2] : (~r2_hidden(sK0,X2) & r2_hidden(sK1,X2) & r1_tarski(sK0,sK1) & v3_ordinal1(X2)) => (~r2_hidden(sK0,sK2) & r2_hidden(sK1,sK2) & r1_tarski(sK0,sK1) & v3_ordinal1(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r1_tarski(X0,X1) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_ordinal1(X0))),
% 0.21/0.45    inference(flattening,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X0,X2) & (r2_hidden(X1,X2) & r1_tarski(X0,X1))) & v3_ordinal1(X2)) & v3_ordinal1(X1)) & v1_ordinal1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f5])).
% 0.21/0.45  fof(f5,conjecture,(
% 0.21/0.45    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f49])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    v3_ordinal1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f45])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    v3_ordinal1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f25,f41])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f37])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    r2_hidden(sK1,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ~spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f33])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ~r2_hidden(sK0,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (22657)------------------------------
% 0.21/0.45  % (22657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (22657)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (22657)Memory used [KB]: 10618
% 0.21/0.45  % (22657)Time elapsed: 0.007 s
% 0.21/0.45  % (22657)------------------------------
% 0.21/0.45  % (22657)------------------------------
% 0.21/0.46  % (22650)Success in time 0.103 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:54:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 215 expanded)
%              Number of leaves         :   23 (  99 expanded)
%              Depth                    :    9
%              Number of atoms          :  323 ( 996 expanded)
%              Number of equality atoms :    9 (  23 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f639,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f55,f56,f66,f71,f76,f119,f133,f187,f212,f217,f227,f248,f266,f552,f638])).

fof(f638,plain,
    ( spl3_2
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f493,f224,f209,f47])).

fof(f47,plain,
    ( spl3_2
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f209,plain,
    ( spl3_27
  <=> r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f224,plain,
    ( spl3_30
  <=> r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f493,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(unit_resulting_resolution,[],[f211,f226,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f226,plain,
    ( r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(sK0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f224])).

fof(f211,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f209])).

fof(f552,plain,
    ( ~ spl3_28
    | spl3_3
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f501,f73,f68,f51,f214])).

fof(f214,plain,
    ( spl3_28
  <=> r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k10_relat_1(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f51,plain,
    ( spl3_3
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( spl3_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f73,plain,
    ( spl3_7
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f501,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k10_relat_1(sK0,k1_relat_1(sK1))))
    | spl3_3
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f100,f53,f80])).

fof(f53,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f100,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK0,k10_relat_1(sK0,X0)),X0)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f75,f70,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f70,plain,
    ( v1_funct_1(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f75,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f266,plain,
    ( ~ spl3_3
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | spl3_27 ),
    inference(avatar_split_clause,[],[f253,f209,f73,f68,f47,f51])).

fof(f253,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | spl3_27 ),
    inference(unit_resulting_resolution,[],[f75,f70,f210,f48,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

% (23424)Refutation not found, incomplete strategy% (23424)------------------------------
% (23424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23424)Termination reason: Refutation not found, incomplete strategy

% (23424)Memory used [KB]: 10490
% (23424)Time elapsed: 0.106 s
% (23424)------------------------------
% (23424)------------------------------
fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f48,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f210,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f209])).

fof(f248,plain,
    ( ~ spl3_27
    | spl3_1
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f247,f184,f43,f209])).

fof(f43,plain,
    ( spl3_1
  <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f184,plain,
    ( spl3_23
  <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f247,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | spl3_1
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f45,f186])).

fof(f186,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f184])).

fof(f45,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f227,plain,
    ( spl3_30
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f206,f184,f116,f224])).

fof(f116,plain,
    ( spl3_13
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f206,plain,
    ( r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(sK0))
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f118,f186])).

fof(f118,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f217,plain,
    ( spl3_28
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f204,f184,f130,f214])).

fof(f130,plain,
    ( spl3_15
  <=> r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f204,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k10_relat_1(sK0,k1_relat_1(sK1))))
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f132,f186])).

fof(f132,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f130])).

fof(f212,plain,
    ( spl3_27
    | ~ spl3_1
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f203,f184,f43,f209])).

fof(f203,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl3_1
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f44,f186])).

fof(f44,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f187,plain,
    ( spl3_23
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f168,f73,f63,f184])).

fof(f63,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f168,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f75,f65,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f65,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f133,plain,
    ( spl3_15
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f128,f73,f43,f130])).

fof(f128,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f75,f44,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f119,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f102,f73,f63,f116])).

fof(f102,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f75,f65,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

% (23431)Refutation not found, incomplete strategy% (23431)------------------------------
% (23431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23431)Termination reason: Refutation not found, incomplete strategy

% (23431)Memory used [KB]: 10618
% (23431)Time elapsed: 0.104 s
% (23431)------------------------------
% (23431)------------------------------
fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f76,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f28,f73])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
      | ~ r1_tarski(sK2,k1_relat_1(sK0))
      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        & r1_tarski(sK2,k1_relat_1(sK0)) )
      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(sK0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
            & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(sK0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            | ~ r1_tarski(X2,k1_relat_1(sK0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
          & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
              & r1_tarski(X2,k1_relat_1(sK0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
          | ~ r1_tarski(X2,k1_relat_1(sK0))
          | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
        & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            & r1_tarski(X2,k1_relat_1(sK0)) )
          | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
   => ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
      & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
          & r1_tarski(sK2,k1_relat_1(sK0)) )
        | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(f71,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f32,f47,f43])).

fof(f32,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f33,f51,f43])).

fof(f33,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f34,f51,f47,f43])).

fof(f34,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (23439)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.46  % (23433)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.49  % (23432)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.49  % (23426)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (23431)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.49  % (23444)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.50  % (23435)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (23437)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.50  % (23444)Refutation not found, incomplete strategy% (23444)------------------------------
% 0.20/0.50  % (23444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (23444)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (23444)Memory used [KB]: 10618
% 0.20/0.50  % (23444)Time elapsed: 0.059 s
% 0.20/0.50  % (23444)------------------------------
% 0.20/0.50  % (23444)------------------------------
% 0.20/0.50  % (23436)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  % (23442)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (23427)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (23425)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (23423)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (23421)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (23440)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  % (23422)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (23428)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (23430)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  % (23434)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (23428)Refutation not found, incomplete strategy% (23428)------------------------------
% 0.20/0.51  % (23428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23428)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23428)Memory used [KB]: 6140
% 0.20/0.51  % (23428)Time elapsed: 0.108 s
% 0.20/0.51  % (23428)------------------------------
% 0.20/0.51  % (23428)------------------------------
% 0.20/0.51  % (23424)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.51  % (23427)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f639,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f54,f55,f56,f66,f71,f76,f119,f133,f187,f212,f217,f227,f248,f266,f552,f638])).
% 0.20/0.52  fof(f638,plain,(
% 0.20/0.52    spl3_2 | ~spl3_27 | ~spl3_30),
% 0.20/0.52    inference(avatar_split_clause,[],[f493,f224,f209,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    spl3_2 <=> r1_tarski(sK2,k1_relat_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.52  fof(f209,plain,(
% 0.20/0.52    spl3_27 <=> r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.52  fof(f224,plain,(
% 0.20/0.52    spl3_30 <=> r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.52  fof(f493,plain,(
% 0.20/0.52    r1_tarski(sK2,k1_relat_1(sK0)) | (~spl3_27 | ~spl3_30)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f211,f226,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(superposition,[],[f38,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.52  fof(f226,plain,(
% 0.20/0.52    r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(sK0)) | ~spl3_30),
% 0.20/0.52    inference(avatar_component_clause,[],[f224])).
% 0.20/0.52  fof(f211,plain,(
% 0.20/0.52    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~spl3_27),
% 0.20/0.52    inference(avatar_component_clause,[],[f209])).
% 0.20/0.52  fof(f552,plain,(
% 0.20/0.52    ~spl3_28 | spl3_3 | ~spl3_6 | ~spl3_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f501,f73,f68,f51,f214])).
% 0.20/0.52  fof(f214,plain,(
% 0.20/0.52    spl3_28 <=> r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k10_relat_1(sK0,k1_relat_1(sK1))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    spl3_3 <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    spl3_6 <=> v1_funct_1(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    spl3_7 <=> v1_relat_1(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.52  fof(f501,plain,(
% 0.20/0.52    ~r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k10_relat_1(sK0,k1_relat_1(sK1)))) | (spl3_3 | ~spl3_6 | ~spl3_7)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f100,f53,f80])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | spl3_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f51])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k9_relat_1(sK0,k10_relat_1(sK0,X0)),X0)) ) | (~spl3_6 | ~spl3_7)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f75,f70,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    v1_funct_1(sK0) | ~spl3_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f68])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    v1_relat_1(sK0) | ~spl3_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f73])).
% 0.20/0.52  fof(f266,plain,(
% 0.20/0.52    ~spl3_3 | ~spl3_2 | ~spl3_6 | ~spl3_7 | spl3_27),
% 0.20/0.52    inference(avatar_split_clause,[],[f253,f209,f73,f68,f47,f51])).
% 0.20/0.52  fof(f253,plain,(
% 0.20/0.52    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | (~spl3_2 | ~spl3_6 | ~spl3_7 | spl3_27)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f75,f70,f210,f48,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  % (23424)Refutation not found, incomplete strategy% (23424)------------------------------
% 0.20/0.52  % (23424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23424)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23424)Memory used [KB]: 10490
% 0.20/0.52  % (23424)Time elapsed: 0.106 s
% 0.20/0.52  % (23424)------------------------------
% 0.20/0.52  % (23424)------------------------------
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    r1_tarski(sK2,k1_relat_1(sK0)) | ~spl3_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f47])).
% 0.20/0.52  fof(f210,plain,(
% 0.20/0.52    ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | spl3_27),
% 0.20/0.52    inference(avatar_component_clause,[],[f209])).
% 0.20/0.52  fof(f248,plain,(
% 0.20/0.52    ~spl3_27 | spl3_1 | ~spl3_23),
% 0.20/0.52    inference(avatar_split_clause,[],[f247,f184,f43,f209])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    spl3_1 <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.52  fof(f184,plain,(
% 0.20/0.52    spl3_23 <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.52  fof(f247,plain,(
% 0.20/0.52    ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | (spl3_1 | ~spl3_23)),
% 0.20/0.52    inference(forward_demodulation,[],[f45,f186])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) | ~spl3_23),
% 0.20/0.52    inference(avatar_component_clause,[],[f184])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | spl3_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f43])).
% 0.20/0.52  fof(f227,plain,(
% 0.20/0.52    spl3_30 | ~spl3_13 | ~spl3_23),
% 0.20/0.52    inference(avatar_split_clause,[],[f206,f184,f116,f224])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    spl3_13 <=> r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.52  fof(f206,plain,(
% 0.20/0.52    r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(sK0)) | (~spl3_13 | ~spl3_23)),
% 0.20/0.52    inference(backward_demodulation,[],[f118,f186])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | ~spl3_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f116])).
% 0.20/0.52  fof(f217,plain,(
% 0.20/0.52    spl3_28 | ~spl3_15 | ~spl3_23),
% 0.20/0.52    inference(avatar_split_clause,[],[f204,f184,f130,f214])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    spl3_15 <=> r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k10_relat_1(sK0,k1_relat_1(sK1)))) | (~spl3_15 | ~spl3_23)),
% 0.20/0.52    inference(backward_demodulation,[],[f132,f186])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))) | ~spl3_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f130])).
% 0.20/0.52  fof(f212,plain,(
% 0.20/0.52    spl3_27 | ~spl3_1 | ~spl3_23),
% 0.20/0.52    inference(avatar_split_clause,[],[f203,f184,f43,f209])).
% 0.20/0.52  fof(f203,plain,(
% 0.20/0.52    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | (~spl3_1 | ~spl3_23)),
% 0.20/0.52    inference(backward_demodulation,[],[f44,f186])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl3_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f43])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    spl3_23 | ~spl3_5 | ~spl3_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f168,f73,f63,f184])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    spl3_5 <=> v1_relat_1(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) | (~spl3_5 | ~spl3_7)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f75,f65,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    v1_relat_1(sK1) | ~spl3_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f63])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    spl3_15 | ~spl3_1 | ~spl3_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f128,f73,f43,f130])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))) | (~spl3_1 | ~spl3_7)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f75,f44,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    spl3_13 | ~spl3_5 | ~spl3_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f102,f73,f63,f116])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | (~spl3_5 | ~spl3_7)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f75,f65,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  % (23431)Refutation not found, incomplete strategy% (23431)------------------------------
% 0.20/0.52  % (23431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23431)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23431)Memory used [KB]: 10618
% 0.20/0.52  % (23431)Time elapsed: 0.104 s
% 0.20/0.52  % (23431)------------------------------
% 0.20/0.52  % (23431)------------------------------
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    spl3_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f28,f73])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    v1_relat_1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) => ((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    spl3_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f29,f68])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    v1_funct_1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    spl3_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f30,f63])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    spl3_1 | spl3_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f32,f47,f43])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    spl3_1 | spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f33,f51,f43])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f34,f51,f47,f43])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (23427)------------------------------
% 0.20/0.52  % (23427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23427)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (23427)Memory used [KB]: 11129
% 0.20/0.52  % (23427)Time elapsed: 0.078 s
% 0.20/0.52  % (23427)------------------------------
% 0.20/0.52  % (23427)------------------------------
% 0.20/0.52  % (23420)Success in time 0.162 s
%------------------------------------------------------------------------------

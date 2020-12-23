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
% DateTime   : Thu Dec  3 12:51:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 148 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :    7
%              Number of atoms          :  227 ( 431 expanded)
%              Number of equality atoms :   31 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f273,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f45,f49,f53,f57,f61,f69,f80,f97,f102,f108,f112,f135,f188,f236,f267])).

fof(f267,plain,
    ( spl2_1
    | ~ spl2_22
    | ~ spl2_41 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl2_1
    | ~ spl2_22
    | ~ spl2_41 ),
    inference(subsumption_resolution,[],[f257,f29])).

fof(f29,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f257,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_22
    | ~ spl2_41 ),
    inference(superposition,[],[f134,f235])).

fof(f235,plain,
    ( ! [X3] : sK1 = k4_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK0),X3))
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl2_41
  <=> ! [X3] : sK1 = k4_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK0),X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f134,plain,
    ( ! [X2] : r1_xboole_0(sK0,k4_xboole_0(X2,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl2_22
  <=> ! [X2] : r1_xboole_0(sK0,k4_xboole_0(X2,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f236,plain,
    ( spl2_41
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f221,f186,f106,f234])).

fof(f106,plain,
    ( spl2_17
  <=> ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f186,plain,
    ( spl2_32
  <=> ! [X18,X17] : k2_zfmisc_1(k1_relat_1(sK0),X17) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),X17),k2_zfmisc_1(k1_relat_1(sK1),X18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f221,plain,
    ( ! [X3] : sK1 = k4_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK0),X3))
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(superposition,[],[f107,f187])).

fof(f187,plain,
    ( ! [X17,X18] : k2_zfmisc_1(k1_relat_1(sK0),X17) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),X17),k2_zfmisc_1(k1_relat_1(sK1),X18))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f186])).

fof(f107,plain,
    ( ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f106])).

fof(f188,plain,
    ( spl2_32
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f170,f95,f32,f186])).

fof(f32,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f95,plain,
    ( spl2_15
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f170,plain,
    ( ! [X17,X18] : k2_zfmisc_1(k1_relat_1(sK0),X17) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),X17),k2_zfmisc_1(k1_relat_1(sK1),X18))
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(resolution,[],[f96,f34])).

fof(f34,plain,
    ( r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f96,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f135,plain,
    ( spl2_22
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f127,f110,f51,f133])).

fof(f51,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f110,plain,
    ( spl2_18
  <=> ! [X1] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f127,plain,
    ( ! [X2] : r1_xboole_0(sK0,k4_xboole_0(X2,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( ! [X2] :
        ( sK0 != sK0
        | r1_xboole_0(sK0,k4_xboole_0(X2,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) )
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(superposition,[],[f52,f111])).

fof(f111,plain,
    ( ! [X1] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f110])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f112,plain,
    ( spl2_18
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f104,f100,f42,f110])).

fof(f42,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f100,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f104,plain,
    ( ! [X1] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(resolution,[],[f101,f44])).

fof(f44,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k4_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f100])).

fof(f108,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f103,f100,f37,f106])).

fof(f37,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f103,plain,
    ( ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(resolution,[],[f101,f39])).

fof(f39,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f102,plain,
    ( spl2_16
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f98,f78,f47,f100])).

fof(f47,plain,
    ( spl2_5
  <=> ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f78,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(resolution,[],[f79,f48])).

fof(f48,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f79,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0 )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f97,plain,
    ( spl2_15
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f93,f67,f55,f95])).

fof(f55,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f67,plain,
    ( spl2_10
  <=> ! [X1,X3,X0,X2] :
        ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f93,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) )
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(resolution,[],[f68,f56])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f68,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f80,plain,
    ( spl2_12
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f76,f59,f55,f78])).

fof(f59,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0 )
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(resolution,[],[f60,f56])).

fof(f60,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f69,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f24,f67])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f61,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f23,f59])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f57,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f53,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

fof(f40,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f19,f27])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:32:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.40  % (28639)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.40  % (28633)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.40  % (28639)Refutation found. Thanks to Tanya!
% 0.20/0.40  % SZS status Theorem for theBenchmark
% 0.20/0.40  % SZS output start Proof for theBenchmark
% 0.20/0.40  fof(f273,plain,(
% 0.20/0.40    $false),
% 0.20/0.40    inference(avatar_sat_refutation,[],[f30,f35,f40,f45,f49,f53,f57,f61,f69,f80,f97,f102,f108,f112,f135,f188,f236,f267])).
% 0.20/0.40  fof(f267,plain,(
% 0.20/0.40    spl2_1 | ~spl2_22 | ~spl2_41),
% 0.20/0.40    inference(avatar_contradiction_clause,[],[f266])).
% 0.20/0.40  fof(f266,plain,(
% 0.20/0.40    $false | (spl2_1 | ~spl2_22 | ~spl2_41)),
% 0.20/0.40    inference(subsumption_resolution,[],[f257,f29])).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    ~r1_xboole_0(sK0,sK1) | spl2_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f27])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.41  fof(f257,plain,(
% 0.20/0.41    r1_xboole_0(sK0,sK1) | (~spl2_22 | ~spl2_41)),
% 0.20/0.41    inference(superposition,[],[f134,f235])).
% 0.20/0.41  fof(f235,plain,(
% 0.20/0.41    ( ! [X3] : (sK1 = k4_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK0),X3))) ) | ~spl2_41),
% 0.20/0.41    inference(avatar_component_clause,[],[f234])).
% 0.20/0.41  fof(f234,plain,(
% 0.20/0.41    spl2_41 <=> ! [X3] : sK1 = k4_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK0),X3))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.20/0.41  fof(f134,plain,(
% 0.20/0.41    ( ! [X2] : (r1_xboole_0(sK0,k4_xboole_0(X2,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))) ) | ~spl2_22),
% 0.20/0.41    inference(avatar_component_clause,[],[f133])).
% 0.20/0.41  fof(f133,plain,(
% 0.20/0.41    spl2_22 <=> ! [X2] : r1_xboole_0(sK0,k4_xboole_0(X2,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.41  fof(f236,plain,(
% 0.20/0.41    spl2_41 | ~spl2_17 | ~spl2_32),
% 0.20/0.41    inference(avatar_split_clause,[],[f221,f186,f106,f234])).
% 0.20/0.41  fof(f106,plain,(
% 0.20/0.41    spl2_17 <=> ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.41  fof(f186,plain,(
% 0.20/0.41    spl2_32 <=> ! [X18,X17] : k2_zfmisc_1(k1_relat_1(sK0),X17) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),X17),k2_zfmisc_1(k1_relat_1(sK1),X18))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.20/0.41  fof(f221,plain,(
% 0.20/0.41    ( ! [X3] : (sK1 = k4_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK0),X3))) ) | (~spl2_17 | ~spl2_32)),
% 0.20/0.41    inference(superposition,[],[f107,f187])).
% 0.20/0.41  fof(f187,plain,(
% 0.20/0.41    ( ! [X17,X18] : (k2_zfmisc_1(k1_relat_1(sK0),X17) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),X17),k2_zfmisc_1(k1_relat_1(sK1),X18))) ) | ~spl2_32),
% 0.20/0.41    inference(avatar_component_clause,[],[f186])).
% 0.20/0.41  fof(f107,plain,(
% 0.20/0.41    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))) ) | ~spl2_17),
% 0.20/0.41    inference(avatar_component_clause,[],[f106])).
% 0.20/0.41  fof(f188,plain,(
% 0.20/0.41    spl2_32 | ~spl2_2 | ~spl2_15),
% 0.20/0.41    inference(avatar_split_clause,[],[f170,f95,f32,f186])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    spl2_2 <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.41  fof(f95,plain,(
% 0.20/0.41    spl2_15 <=> ! [X1,X3,X0,X2] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.41  fof(f170,plain,(
% 0.20/0.41    ( ! [X17,X18] : (k2_zfmisc_1(k1_relat_1(sK0),X17) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),X17),k2_zfmisc_1(k1_relat_1(sK1),X18))) ) | (~spl2_2 | ~spl2_15)),
% 0.20/0.41    inference(resolution,[],[f96,f34])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f32])).
% 0.20/0.41  fof(f96,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ) | ~spl2_15),
% 0.20/0.41    inference(avatar_component_clause,[],[f95])).
% 0.20/0.41  fof(f135,plain,(
% 0.20/0.41    spl2_22 | ~spl2_6 | ~spl2_18),
% 0.20/0.41    inference(avatar_split_clause,[],[f127,f110,f51,f133])).
% 0.20/0.41  fof(f51,plain,(
% 0.20/0.41    spl2_6 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.41  fof(f110,plain,(
% 0.20/0.41    spl2_18 <=> ! [X1] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.41  fof(f127,plain,(
% 0.20/0.41    ( ! [X2] : (r1_xboole_0(sK0,k4_xboole_0(X2,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))) ) | (~spl2_6 | ~spl2_18)),
% 0.20/0.41    inference(trivial_inequality_removal,[],[f126])).
% 0.20/0.41  fof(f126,plain,(
% 0.20/0.41    ( ! [X2] : (sK0 != sK0 | r1_xboole_0(sK0,k4_xboole_0(X2,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))) ) | (~spl2_6 | ~spl2_18)),
% 0.20/0.41    inference(superposition,[],[f52,f111])).
% 0.20/0.41  fof(f111,plain,(
% 0.20/0.41    ( ! [X1] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))) ) | ~spl2_18),
% 0.20/0.41    inference(avatar_component_clause,[],[f110])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl2_6),
% 0.20/0.41    inference(avatar_component_clause,[],[f51])).
% 0.20/0.41  fof(f112,plain,(
% 0.20/0.41    spl2_18 | ~spl2_4 | ~spl2_16),
% 0.20/0.41    inference(avatar_split_clause,[],[f104,f100,f42,f110])).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    spl2_4 <=> v1_relat_1(sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.41  fof(f100,plain,(
% 0.20/0.41    spl2_16 <=> ! [X1,X0] : (k4_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.41  fof(f104,plain,(
% 0.20/0.41    ( ! [X1] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))) ) | (~spl2_4 | ~spl2_16)),
% 0.20/0.41    inference(resolution,[],[f101,f44])).
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    v1_relat_1(sK0) | ~spl2_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f42])).
% 0.20/0.41  fof(f101,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) ) | ~spl2_16),
% 0.20/0.41    inference(avatar_component_clause,[],[f100])).
% 0.20/0.41  fof(f108,plain,(
% 0.20/0.41    spl2_17 | ~spl2_3 | ~spl2_16),
% 0.20/0.41    inference(avatar_split_clause,[],[f103,f100,f37,f106])).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    spl2_3 <=> v1_relat_1(sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.41  fof(f103,plain,(
% 0.20/0.41    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))) ) | (~spl2_3 | ~spl2_16)),
% 0.20/0.41    inference(resolution,[],[f101,f39])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    v1_relat_1(sK1) | ~spl2_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f37])).
% 0.20/0.41  fof(f102,plain,(
% 0.20/0.41    spl2_16 | ~spl2_5 | ~spl2_12),
% 0.20/0.41    inference(avatar_split_clause,[],[f98,f78,f47,f100])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    spl2_5 <=> ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.41  fof(f78,plain,(
% 0.20/0.41    spl2_12 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.41  fof(f98,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) ) | (~spl2_5 | ~spl2_12)),
% 0.20/0.41    inference(resolution,[],[f79,f48])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.20/0.41    inference(avatar_component_clause,[],[f47])).
% 0.20/0.41  fof(f79,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0) ) | ~spl2_12),
% 0.20/0.41    inference(avatar_component_clause,[],[f78])).
% 0.20/0.41  fof(f97,plain,(
% 0.20/0.41    spl2_15 | ~spl2_7 | ~spl2_10),
% 0.20/0.41    inference(avatar_split_clause,[],[f93,f67,f55,f95])).
% 0.20/0.41  fof(f55,plain,(
% 0.20/0.41    spl2_7 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.41  fof(f67,plain,(
% 0.20/0.41    spl2_10 <=> ! [X1,X3,X0,X2] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.41  fof(f93,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ) | (~spl2_7 | ~spl2_10)),
% 0.20/0.41    inference(resolution,[],[f68,f56])).
% 0.20/0.41  fof(f56,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl2_7),
% 0.20/0.41    inference(avatar_component_clause,[],[f55])).
% 0.20/0.41  fof(f68,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) ) | ~spl2_10),
% 0.20/0.41    inference(avatar_component_clause,[],[f67])).
% 0.20/0.41  fof(f80,plain,(
% 0.20/0.41    spl2_12 | ~spl2_7 | ~spl2_8),
% 0.20/0.41    inference(avatar_split_clause,[],[f76,f59,f55,f78])).
% 0.20/0.41  fof(f59,plain,(
% 0.20/0.41    spl2_8 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.41  fof(f76,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0) ) | (~spl2_7 | ~spl2_8)),
% 0.20/0.41    inference(resolution,[],[f60,f56])).
% 0.20/0.41  fof(f60,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_8),
% 0.20/0.41    inference(avatar_component_clause,[],[f59])).
% 0.20/0.41  fof(f69,plain,(
% 0.20/0.41    spl2_10),
% 0.20/0.41    inference(avatar_split_clause,[],[f24,f67])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.20/0.41  fof(f61,plain,(
% 0.20/0.41    spl2_8),
% 0.20/0.41    inference(avatar_split_clause,[],[f23,f59])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.20/0.41  fof(f57,plain,(
% 0.20/0.41    spl2_7),
% 0.20/0.41    inference(avatar_split_clause,[],[f21,f55])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.41    inference(nnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    spl2_6),
% 0.20/0.41    inference(avatar_split_clause,[],[f22,f51])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f49,plain,(
% 0.20/0.41    spl2_5),
% 0.20/0.41    inference(avatar_split_clause,[],[f20,f47])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.20/0.41  fof(f45,plain,(
% 0.20/0.41    spl2_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f16,f42])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    v1_relat_1(sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13,f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.41    inference(flattening,[],[f7])).
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,negated_conjecture,(
% 0.20/0.41    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.20/0.41    inference(negated_conjecture,[],[f5])).
% 0.20/0.41  fof(f5,conjecture,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    spl2_3),
% 0.20/0.41    inference(avatar_split_clause,[],[f17,f37])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    v1_relat_1(sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f14])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    spl2_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f18,f32])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.20/0.41    inference(cnf_transformation,[],[f14])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    ~spl2_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f19,f27])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f14])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (28639)------------------------------
% 0.20/0.41  % (28639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (28639)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (28639)Memory used [KB]: 6268
% 0.20/0.41  % (28639)Time elapsed: 0.008 s
% 0.20/0.41  % (28639)------------------------------
% 0.20/0.41  % (28639)------------------------------
% 0.20/0.41  % (28628)Success in time 0.06 s
%------------------------------------------------------------------------------

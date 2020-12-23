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
% DateTime   : Thu Dec  3 12:32:47 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 225 expanded)
%              Number of leaves         :   35 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :  375 ( 632 expanded)
%              Number of equality atoms :   28 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2081,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f69,f73,f77,f81,f85,f90,f102,f106,f115,f119,f144,f160,f239,f243,f291,f324,f362,f368,f448,f463,f500,f572,f2062,f2077])).

fof(f2077,plain,
    ( ~ spl3_6
    | spl3_122 ),
    inference(avatar_contradiction_clause,[],[f2063])).

fof(f2063,plain,
    ( $false
    | ~ spl3_6
    | spl3_122 ),
    inference(unit_resulting_resolution,[],[f80,f2061])).

fof(f2061,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))
    | spl3_122 ),
    inference(avatar_component_clause,[],[f2059])).

fof(f2059,plain,
    ( spl3_122
  <=> r1_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_122])])).

fof(f80,plain,
    ( ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f2062,plain,
    ( ~ spl3_122
    | ~ spl3_2
    | ~ spl3_10
    | ~ spl3_15
    | spl3_36
    | ~ spl3_44
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f600,f570,f498,f359,f142,f100,f55,f2059])).

fof(f55,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f100,plain,
    ( spl3_10
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f142,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f359,plain,
    ( spl3_36
  <=> r1_tarski(sK0,k2_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f498,plain,
    ( spl3_44
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f570,plain,
    ( spl3_48
  <=> ! [X1,X0] :
        ( k5_xboole_0(X1,X0) = k2_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f600,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))
    | ~ spl3_10
    | ~ spl3_15
    | spl3_36
    | ~ spl3_44
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f599,f101])).

fof(f101,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f599,plain,
    ( ~ r1_tarski(sK0,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)))
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))
    | ~ spl3_15
    | spl3_36
    | ~ spl3_44
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f598,f499])).

fof(f499,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f498])).

fof(f598,plain,
    ( ~ r1_tarski(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))
    | ~ spl3_15
    | spl3_36
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f583,f143])).

fof(f143,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f583,plain,
    ( ~ r1_tarski(sK0,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))
    | spl3_36
    | ~ spl3_48 ),
    inference(superposition,[],[f361,f571])).

fof(f571,plain,
    ( ! [X0,X1] :
        ( k5_xboole_0(X1,X0) = k2_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f570])).

fof(f361,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | spl3_36 ),
    inference(avatar_component_clause,[],[f359])).

fof(f572,plain,
    ( spl3_48
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f124,f100,f88,f570])).

fof(f88,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( k5_xboole_0(X1,X0) = k2_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(superposition,[],[f101,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f500,plain,
    ( spl3_44
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f127,f104,f75,f498])).

fof(f75,plain,
    ( spl3_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f104,plain,
    ( spl3_11
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f127,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(superposition,[],[f105,f76])).

fof(f76,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f105,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f463,plain,
    ( ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_15
    | spl3_28
    | ~ spl3_37
    | ~ spl3_41 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_15
    | spl3_28
    | ~ spl3_37
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f290,f461])).

fof(f461,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_15
    | ~ spl3_37
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f460,f101])).

fof(f460,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_15
    | ~ spl3_37
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f459,f127])).

fof(f459,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))
    | ~ spl3_15
    | ~ spl3_37
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f453,f143])).

fof(f453,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))
    | ~ spl3_37
    | ~ spl3_41 ),
    inference(unit_resulting_resolution,[],[f367,f447])).

fof(f447,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k5_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl3_41
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k5_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f367,plain,
    ( ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl3_37
  <=> ! [X1,X0] : r1_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f290,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl3_28
  <=> r1_tarski(k5_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f448,plain,
    ( spl3_41
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f121,f88,f83,f446])).

fof(f83,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k5_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f84,f89])).

fof(f84,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f368,plain,
    ( spl3_37
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f95,f79,f71,f366])).

fof(f71,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f95,plain,
    ( ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f80,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f362,plain,
    ( ~ spl3_36
    | spl3_1
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f326,f158,f63,f51,f359])).

fof(f51,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f63,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f158,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f326,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | spl3_1
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f65,f52,f159])).

fof(f159,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X2)
        | r1_tarski(X0,X1) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f158])).

fof(f52,plain,
    ( ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f65,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f324,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f248,f63,f55,f51])).

fof(f248,plain,
    ( ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f59,f65])).

fof(f59,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f34,f57])).

fof(f57,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f34,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
    & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
      | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
        & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
            & r1_tarski(X0,k2_xboole_0(X1,X2)) )
          | r1_tarski(X0,k5_xboole_0(X1,X2)) ) )
   => ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
      & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
          & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
        | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <~> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k5_xboole_0(X1,X2))
      <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f291,plain,
    ( ~ spl3_28
    | ~ spl3_1
    | spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f255,f117,f55,f51,f288])).

fof(f117,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f255,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))
    | ~ spl3_1
    | spl3_2
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f53,f56,f118])).

fof(f118,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f56,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f53,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f243,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | spl3_25 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_6
    | spl3_25 ),
    inference(unit_resulting_resolution,[],[f80,f238,f72])).

fof(f238,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl3_25
  <=> r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f239,plain,
    ( ~ spl3_25
    | ~ spl3_1
    | spl3_3
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f132,f113,f63,f51,f236])).

fof(f113,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f132,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | ~ spl3_1
    | spl3_3
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f64,f53,f114])).

fof(f114,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f64,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f160,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f49,f158])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f144,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f43,f142])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f119,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f48,f117])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f115,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f46,f113])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f106,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f39,f104])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f102,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f38,f100])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f90,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f41,f88])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f85,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f81,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f36,f79])).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f77,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f73,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f69,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f67,f63,f51])).

fof(f67,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f33,f64])).

fof(f33,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f32,f55,f51])).

fof(f32,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 20:18:52 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.42  % (24193)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (24195)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (24183)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (24187)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (24194)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (24189)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (24191)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (24184)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (24185)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (24182)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (24197)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (24198)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (24188)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (24186)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (24199)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (24196)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.53  % (24192)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (24190)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.55/0.57  % (24187)Refutation found. Thanks to Tanya!
% 1.55/0.57  % SZS status Theorem for theBenchmark
% 1.55/0.57  % SZS output start Proof for theBenchmark
% 1.55/0.57  fof(f2081,plain,(
% 1.55/0.57    $false),
% 1.55/0.57    inference(avatar_sat_refutation,[],[f58,f69,f73,f77,f81,f85,f90,f102,f106,f115,f119,f144,f160,f239,f243,f291,f324,f362,f368,f448,f463,f500,f572,f2062,f2077])).
% 1.55/0.57  fof(f2077,plain,(
% 1.55/0.57    ~spl3_6 | spl3_122),
% 1.55/0.57    inference(avatar_contradiction_clause,[],[f2063])).
% 1.55/0.57  fof(f2063,plain,(
% 1.55/0.57    $false | (~spl3_6 | spl3_122)),
% 1.55/0.57    inference(unit_resulting_resolution,[],[f80,f2061])).
% 1.55/0.57  fof(f2061,plain,(
% 1.55/0.57    ~r1_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) | spl3_122),
% 1.55/0.57    inference(avatar_component_clause,[],[f2059])).
% 1.55/0.57  fof(f2059,plain,(
% 1.55/0.57    spl3_122 <=> r1_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_122])])).
% 1.55/0.57  fof(f80,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | ~spl3_6),
% 1.55/0.57    inference(avatar_component_clause,[],[f79])).
% 1.55/0.57  fof(f79,plain,(
% 1.55/0.57    spl3_6 <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.55/0.57  fof(f2062,plain,(
% 1.55/0.57    ~spl3_122 | ~spl3_2 | ~spl3_10 | ~spl3_15 | spl3_36 | ~spl3_44 | ~spl3_48),
% 1.55/0.57    inference(avatar_split_clause,[],[f600,f570,f498,f359,f142,f100,f55,f2059])).
% 1.55/0.57  fof(f55,plain,(
% 1.55/0.57    spl3_2 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.55/0.57  fof(f100,plain,(
% 1.55/0.57    spl3_10 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.55/0.57  fof(f142,plain,(
% 1.55/0.57    spl3_15 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.55/0.57  fof(f359,plain,(
% 1.55/0.57    spl3_36 <=> r1_tarski(sK0,k2_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.55/0.57  fof(f498,plain,(
% 1.55/0.57    spl3_44 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.55/0.57  fof(f570,plain,(
% 1.55/0.57    spl3_48 <=> ! [X1,X0] : (k5_xboole_0(X1,X0) = k2_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 1.55/0.57  fof(f600,plain,(
% 1.55/0.57    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) | (~spl3_10 | ~spl3_15 | spl3_36 | ~spl3_44 | ~spl3_48)),
% 1.55/0.57    inference(forward_demodulation,[],[f599,f101])).
% 1.55/0.57  fof(f101,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_10),
% 1.55/0.57    inference(avatar_component_clause,[],[f100])).
% 1.55/0.57  fof(f599,plain,(
% 1.55/0.57    ~r1_tarski(sK0,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))) | ~r1_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) | (~spl3_15 | spl3_36 | ~spl3_44 | ~spl3_48)),
% 1.55/0.57    inference(forward_demodulation,[],[f598,f499])).
% 1.55/0.57  fof(f499,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) ) | ~spl3_44),
% 1.55/0.57    inference(avatar_component_clause,[],[f498])).
% 1.55/0.57  fof(f598,plain,(
% 1.55/0.57    ~r1_tarski(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))) | ~r1_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) | (~spl3_15 | spl3_36 | ~spl3_48)),
% 1.55/0.57    inference(forward_demodulation,[],[f583,f143])).
% 1.55/0.57  fof(f143,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl3_15),
% 1.55/0.57    inference(avatar_component_clause,[],[f142])).
% 1.55/0.57  fof(f583,plain,(
% 1.55/0.57    ~r1_tarski(sK0,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) | ~r1_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) | (spl3_36 | ~spl3_48)),
% 1.55/0.57    inference(superposition,[],[f361,f571])).
% 1.55/0.57  fof(f571,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k5_xboole_0(X1,X0) = k2_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) ) | ~spl3_48),
% 1.55/0.57    inference(avatar_component_clause,[],[f570])).
% 1.55/0.57  fof(f361,plain,(
% 1.55/0.57    ~r1_tarski(sK0,k2_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) | spl3_36),
% 1.55/0.57    inference(avatar_component_clause,[],[f359])).
% 1.55/0.57  fof(f572,plain,(
% 1.55/0.57    spl3_48 | ~spl3_8 | ~spl3_10),
% 1.55/0.57    inference(avatar_split_clause,[],[f124,f100,f88,f570])).
% 1.55/0.57  fof(f88,plain,(
% 1.55/0.57    spl3_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.55/0.57  fof(f124,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k5_xboole_0(X1,X0) = k2_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) ) | (~spl3_8 | ~spl3_10)),
% 1.55/0.57    inference(superposition,[],[f101,f89])).
% 1.55/0.57  fof(f89,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_8),
% 1.55/0.57    inference(avatar_component_clause,[],[f88])).
% 1.55/0.57  fof(f500,plain,(
% 1.55/0.57    spl3_44 | ~spl3_5 | ~spl3_11),
% 1.55/0.57    inference(avatar_split_clause,[],[f127,f104,f75,f498])).
% 1.55/0.57  fof(f75,plain,(
% 1.55/0.57    spl3_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.55/0.57  fof(f104,plain,(
% 1.55/0.57    spl3_11 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.55/0.57  fof(f127,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) ) | (~spl3_5 | ~spl3_11)),
% 1.55/0.57    inference(superposition,[],[f105,f76])).
% 1.55/0.57  fof(f76,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_5),
% 1.55/0.57    inference(avatar_component_clause,[],[f75])).
% 1.55/0.57  fof(f105,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_11),
% 1.55/0.57    inference(avatar_component_clause,[],[f104])).
% 1.55/0.57  fof(f463,plain,(
% 1.55/0.57    ~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_15 | spl3_28 | ~spl3_37 | ~spl3_41),
% 1.55/0.57    inference(avatar_contradiction_clause,[],[f462])).
% 1.55/0.57  fof(f462,plain,(
% 1.55/0.57    $false | (~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_15 | spl3_28 | ~spl3_37 | ~spl3_41)),
% 1.55/0.57    inference(subsumption_resolution,[],[f290,f461])).
% 1.55/0.57  fof(f461,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) | (~spl3_5 | ~spl3_10 | ~spl3_11 | ~spl3_15 | ~spl3_37 | ~spl3_41)),
% 1.55/0.57    inference(forward_demodulation,[],[f460,f101])).
% 1.55/0.57  fof(f460,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | (~spl3_5 | ~spl3_11 | ~spl3_15 | ~spl3_37 | ~spl3_41)),
% 1.55/0.57    inference(forward_demodulation,[],[f459,f127])).
% 1.55/0.57  fof(f459,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) ) | (~spl3_15 | ~spl3_37 | ~spl3_41)),
% 1.55/0.57    inference(forward_demodulation,[],[f453,f143])).
% 1.55/0.57  fof(f453,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) ) | (~spl3_37 | ~spl3_41)),
% 1.55/0.57    inference(unit_resulting_resolution,[],[f367,f447])).
% 1.55/0.57  fof(f447,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl3_41),
% 1.55/0.57    inference(avatar_component_clause,[],[f446])).
% 1.55/0.57  fof(f446,plain,(
% 1.55/0.57    spl3_41 <=> ! [X1,X0] : (r1_tarski(X0,k5_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.55/0.57  fof(f367,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl3_37),
% 1.55/0.57    inference(avatar_component_clause,[],[f366])).
% 1.55/0.57  fof(f366,plain,(
% 1.55/0.57    spl3_37 <=> ! [X1,X0] : r1_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.55/0.57  fof(f290,plain,(
% 1.55/0.57    ~r1_tarski(k5_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) | spl3_28),
% 1.55/0.57    inference(avatar_component_clause,[],[f288])).
% 1.55/0.57  fof(f288,plain,(
% 1.55/0.57    spl3_28 <=> r1_tarski(k5_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.55/0.57  fof(f448,plain,(
% 1.55/0.57    spl3_41 | ~spl3_7 | ~spl3_8),
% 1.55/0.57    inference(avatar_split_clause,[],[f121,f88,f83,f446])).
% 1.55/0.57  fof(f83,plain,(
% 1.55/0.57    spl3_7 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.55/0.57  fof(f121,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | (~spl3_7 | ~spl3_8)),
% 1.55/0.57    inference(superposition,[],[f84,f89])).
% 1.55/0.57  fof(f84,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | ~spl3_7),
% 1.55/0.57    inference(avatar_component_clause,[],[f83])).
% 1.55/0.57  fof(f368,plain,(
% 1.55/0.57    spl3_37 | ~spl3_4 | ~spl3_6),
% 1.55/0.57    inference(avatar_split_clause,[],[f95,f79,f71,f366])).
% 1.55/0.57  fof(f71,plain,(
% 1.55/0.57    spl3_4 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.55/0.57  fof(f95,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | (~spl3_4 | ~spl3_6)),
% 1.55/0.57    inference(unit_resulting_resolution,[],[f80,f72])).
% 1.55/0.57  fof(f72,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_4),
% 1.55/0.57    inference(avatar_component_clause,[],[f71])).
% 1.55/0.57  fof(f362,plain,(
% 1.55/0.57    ~spl3_36 | spl3_1 | ~spl3_3 | ~spl3_19),
% 1.55/0.57    inference(avatar_split_clause,[],[f326,f158,f63,f51,f359])).
% 1.55/0.57  fof(f51,plain,(
% 1.55/0.57    spl3_1 <=> r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.55/0.57  fof(f63,plain,(
% 1.55/0.57    spl3_3 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.55/0.57  fof(f158,plain,(
% 1.55/0.57    spl3_19 <=> ! [X1,X0,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.55/0.57  fof(f326,plain,(
% 1.55/0.57    ~r1_tarski(sK0,k2_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) | (spl3_1 | ~spl3_3 | ~spl3_19)),
% 1.55/0.57    inference(unit_resulting_resolution,[],[f65,f52,f159])).
% 1.55/0.57  fof(f159,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) ) | ~spl3_19),
% 1.55/0.57    inference(avatar_component_clause,[],[f158])).
% 1.55/0.57  fof(f52,plain,(
% 1.55/0.57    ~r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | spl3_1),
% 1.55/0.57    inference(avatar_component_clause,[],[f51])).
% 1.55/0.57  fof(f65,plain,(
% 1.55/0.57    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_3),
% 1.55/0.57    inference(avatar_component_clause,[],[f63])).
% 1.55/0.57  fof(f324,plain,(
% 1.55/0.57    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 1.55/0.57    inference(avatar_split_clause,[],[f248,f63,f55,f51])).
% 1.55/0.57  fof(f248,plain,(
% 1.55/0.57    ~r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_3)),
% 1.55/0.57    inference(subsumption_resolution,[],[f59,f65])).
% 1.55/0.57  fof(f59,plain,(
% 1.55/0.57    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_2),
% 1.55/0.57    inference(subsumption_resolution,[],[f34,f57])).
% 1.55/0.57  fof(f57,plain,(
% 1.55/0.57    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 1.55/0.57    inference(avatar_component_clause,[],[f55])).
% 1.55/0.57  fof(f34,plain,(
% 1.55/0.57    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 1.55/0.57    inference(cnf_transformation,[],[f30])).
% 1.55/0.57  fof(f30,plain,(
% 1.55/0.57    (~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2)))),
% 1.55/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).
% 1.55/0.57  fof(f29,plain,(
% 1.55/0.57    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2)))) => ((~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))))),
% 1.55/0.57    introduced(choice_axiom,[])).
% 1.55/0.57  fof(f28,plain,(
% 1.55/0.57    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 1.55/0.57    inference(flattening,[],[f27])).
% 1.55/0.57  fof(f27,plain,(
% 1.55/0.57    ? [X0,X1,X2] : (((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 1.55/0.57    inference(nnf_transformation,[],[f17])).
% 1.55/0.57  fof(f17,plain,(
% 1.55/0.57    ? [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <~> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.55/0.57    inference(ennf_transformation,[],[f16])).
% 1.55/0.57  fof(f16,negated_conjecture,(
% 1.55/0.57    ~! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.55/0.57    inference(negated_conjecture,[],[f15])).
% 1.55/0.57  fof(f15,conjecture,(
% 1.55/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 1.55/0.57  fof(f291,plain,(
% 1.55/0.57    ~spl3_28 | ~spl3_1 | spl3_2 | ~spl3_14),
% 1.55/0.57    inference(avatar_split_clause,[],[f255,f117,f55,f51,f288])).
% 1.55/0.57  fof(f117,plain,(
% 1.55/0.57    spl3_14 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.55/0.57  fof(f255,plain,(
% 1.55/0.57    ~r1_tarski(k5_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) | (~spl3_1 | spl3_2 | ~spl3_14)),
% 1.55/0.57    inference(unit_resulting_resolution,[],[f53,f56,f118])).
% 1.55/0.57  fof(f118,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_14),
% 1.55/0.57    inference(avatar_component_clause,[],[f117])).
% 1.55/0.57  fof(f56,plain,(
% 1.55/0.57    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 1.55/0.57    inference(avatar_component_clause,[],[f55])).
% 1.55/0.57  fof(f53,plain,(
% 1.55/0.57    r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_1),
% 1.55/0.57    inference(avatar_component_clause,[],[f51])).
% 1.55/0.57  fof(f243,plain,(
% 1.55/0.57    ~spl3_4 | ~spl3_6 | spl3_25),
% 1.55/0.57    inference(avatar_contradiction_clause,[],[f242])).
% 1.55/0.57  fof(f242,plain,(
% 1.55/0.57    $false | (~spl3_4 | ~spl3_6 | spl3_25)),
% 1.55/0.57    inference(unit_resulting_resolution,[],[f80,f238,f72])).
% 1.55/0.57  fof(f238,plain,(
% 1.55/0.57    ~r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) | spl3_25),
% 1.55/0.57    inference(avatar_component_clause,[],[f236])).
% 1.55/0.57  fof(f236,plain,(
% 1.55/0.57    spl3_25 <=> r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.55/0.57  fof(f239,plain,(
% 1.55/0.57    ~spl3_25 | ~spl3_1 | spl3_3 | ~spl3_13),
% 1.55/0.57    inference(avatar_split_clause,[],[f132,f113,f63,f51,f236])).
% 1.55/0.57  fof(f113,plain,(
% 1.55/0.57    spl3_13 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.55/0.57  fof(f132,plain,(
% 1.55/0.57    ~r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) | (~spl3_1 | spl3_3 | ~spl3_13)),
% 1.55/0.57    inference(unit_resulting_resolution,[],[f64,f53,f114])).
% 1.55/0.57  fof(f114,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl3_13),
% 1.55/0.57    inference(avatar_component_clause,[],[f113])).
% 1.55/0.57  fof(f64,plain,(
% 1.55/0.57    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl3_3),
% 1.55/0.57    inference(avatar_component_clause,[],[f63])).
% 1.55/0.57  fof(f160,plain,(
% 1.55/0.57    spl3_19),
% 1.55/0.57    inference(avatar_split_clause,[],[f49,f158])).
% 1.55/0.57  fof(f49,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f26])).
% 1.55/0.57  fof(f26,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.55/0.57    inference(flattening,[],[f25])).
% 1.55/0.57  fof(f25,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.55/0.57    inference(ennf_transformation,[],[f9])).
% 1.55/0.57  fof(f9,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.55/0.57  fof(f144,plain,(
% 1.55/0.57    spl3_15),
% 1.55/0.57    inference(avatar_split_clause,[],[f43,f142])).
% 1.55/0.57  fof(f43,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f12])).
% 1.55/0.57  fof(f12,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.55/0.57  fof(f119,plain,(
% 1.55/0.57    spl3_14),
% 1.55/0.57    inference(avatar_split_clause,[],[f48,f117])).
% 1.55/0.57  fof(f48,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f24])).
% 1.55/0.57  fof(f24,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.55/0.57    inference(flattening,[],[f23])).
% 1.55/0.57  fof(f23,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.55/0.57    inference(ennf_transformation,[],[f6])).
% 1.55/0.57  fof(f6,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.55/0.57  fof(f115,plain,(
% 1.55/0.57    spl3_13),
% 1.55/0.57    inference(avatar_split_clause,[],[f46,f113])).
% 1.55/0.57  fof(f46,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f20])).
% 1.55/0.57  fof(f20,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.55/0.57    inference(flattening,[],[f19])).
% 1.55/0.57  fof(f19,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.55/0.57    inference(ennf_transformation,[],[f8])).
% 1.55/0.57  fof(f8,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.55/0.57  fof(f106,plain,(
% 1.55/0.57    spl3_11),
% 1.55/0.57    inference(avatar_split_clause,[],[f39,f104])).
% 1.55/0.57  fof(f39,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f4])).
% 1.55/0.57  fof(f4,axiom,(
% 1.55/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.55/0.57  fof(f102,plain,(
% 1.55/0.57    spl3_10),
% 1.55/0.57    inference(avatar_split_clause,[],[f38,f100])).
% 1.55/0.57  fof(f38,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f14])).
% 1.55/0.57  fof(f14,axiom,(
% 1.55/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.55/0.57  fof(f90,plain,(
% 1.55/0.57    spl3_8),
% 1.55/0.57    inference(avatar_split_clause,[],[f41,f88])).
% 1.55/0.57  fof(f41,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f31])).
% 1.55/0.57  fof(f31,plain,(
% 1.55/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.55/0.57    inference(nnf_transformation,[],[f10])).
% 1.55/0.57  fof(f10,axiom,(
% 1.55/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.55/0.57  fof(f85,plain,(
% 1.55/0.57    spl3_7),
% 1.55/0.57    inference(avatar_split_clause,[],[f37,f83])).
% 1.55/0.57  fof(f37,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f13])).
% 1.55/0.57  fof(f13,axiom,(
% 1.55/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).
% 1.55/0.57  fof(f81,plain,(
% 1.55/0.57    spl3_6),
% 1.55/0.57    inference(avatar_split_clause,[],[f36,f79])).
% 1.55/0.57  fof(f36,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f3])).
% 1.55/0.57  fof(f3,axiom,(
% 1.55/0.57    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.55/0.57  fof(f77,plain,(
% 1.55/0.57    spl3_5),
% 1.55/0.57    inference(avatar_split_clause,[],[f35,f75])).
% 1.55/0.57  fof(f35,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f1])).
% 1.55/0.57  fof(f1,axiom,(
% 1.55/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.55/0.57  fof(f73,plain,(
% 1.55/0.57    spl3_4),
% 1.55/0.57    inference(avatar_split_clause,[],[f40,f71])).
% 1.55/0.57  fof(f40,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f18])).
% 1.55/0.57  fof(f18,plain,(
% 1.55/0.57    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.55/0.57    inference(ennf_transformation,[],[f2])).
% 1.55/0.57  fof(f2,axiom,(
% 1.55/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.55/0.57  fof(f69,plain,(
% 1.55/0.57    spl3_1 | spl3_3),
% 1.55/0.57    inference(avatar_split_clause,[],[f67,f63,f51])).
% 1.55/0.57  fof(f67,plain,(
% 1.55/0.57    r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | spl3_3),
% 1.55/0.57    inference(subsumption_resolution,[],[f33,f64])).
% 1.55/0.57  fof(f33,plain,(
% 1.55/0.57    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 1.55/0.57    inference(cnf_transformation,[],[f30])).
% 1.55/0.57  fof(f58,plain,(
% 1.55/0.57    spl3_1 | spl3_2),
% 1.55/0.57    inference(avatar_split_clause,[],[f32,f55,f51])).
% 1.55/0.57  fof(f32,plain,(
% 1.55/0.57    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 1.55/0.57    inference(cnf_transformation,[],[f30])).
% 1.55/0.57  % SZS output end Proof for theBenchmark
% 1.55/0.57  % (24187)------------------------------
% 1.55/0.57  % (24187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (24187)Termination reason: Refutation
% 1.55/0.57  
% 1.55/0.57  % (24187)Memory used [KB]: 7931
% 1.55/0.57  % (24187)Time elapsed: 0.125 s
% 1.55/0.57  % (24187)------------------------------
% 1.55/0.57  % (24187)------------------------------
% 1.55/0.57  % (24181)Success in time 0.209 s
%------------------------------------------------------------------------------

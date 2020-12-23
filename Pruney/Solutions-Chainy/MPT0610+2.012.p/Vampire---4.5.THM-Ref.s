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
% DateTime   : Thu Dec  3 12:51:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 164 expanded)
%              Number of leaves         :   29 (  73 expanded)
%              Depth                    :    7
%              Number of atoms          :  284 ( 478 expanded)
%              Number of equality atoms :   54 (  77 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f272,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f60,f68,f72,f76,f84,f88,f92,f96,f106,f124,f174,f180,f189,f223,f227,f271])).

fof(f271,plain,
    ( spl2_1
    | ~ spl2_12
    | ~ spl2_34 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | spl2_1
    | ~ spl2_12
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f261,f40])).

fof(f40,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f261,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_12
    | ~ spl2_34 ),
    inference(trivial_inequality_removal,[],[f259])).

fof(f259,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1)
    | ~ spl2_12
    | ~ spl2_34 ),
    inference(superposition,[],[f87,f222])).

fof(f222,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl2_34
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f227,plain,
    ( ~ spl2_4
    | ~ spl2_9
    | spl2_31 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_9
    | spl2_31 ),
    inference(subsumption_resolution,[],[f225,f55])).

fof(f55,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f225,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_9
    | spl2_31 ),
    inference(resolution,[],[f210,f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f210,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_31 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl2_31
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f223,plain,
    ( ~ spl2_31
    | spl2_34
    | ~ spl2_7
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f196,f185,f66,f220,f208])).

fof(f66,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f185,plain,
    ( spl2_29
  <=> k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f196,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_7
    | ~ spl2_29 ),
    inference(trivial_inequality_removal,[],[f195])).

fof(f195,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_7
    | ~ spl2_29 ),
    inference(superposition,[],[f67,f187])).

fof(f187,plain,
    ( k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f185])).

fof(f67,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f189,plain,
    ( spl2_29
    | ~ spl2_16
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f182,f177,f104,f185])).

fof(f104,plain,
    ( spl2_16
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f177,plain,
    ( spl2_28
  <=> k1_xboole_0 = k4_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f182,plain,
    ( k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_16
    | ~ spl2_28 ),
    inference(superposition,[],[f105,f179])).

fof(f179,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f177])).

fof(f105,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f180,plain,
    ( spl2_28
    | ~ spl2_14
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f175,f171,f94,f177])).

fof(f94,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f171,plain,
    ( spl2_27
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f175,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl2_14
    | ~ spl2_27 ),
    inference(resolution,[],[f173,f95])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f173,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f171])).

fof(f174,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f169,f121,f70,f53,f48,f171])).

fof(f48,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f70,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f121,plain,
    ( spl2_19
  <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f169,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f168,f55])).

fof(f168,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f145,f50])).

fof(f50,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f145,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl2_8
    | ~ spl2_19 ),
    inference(superposition,[],[f71,f123])).

fof(f123,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f121])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f124,plain,
    ( spl2_19
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f115,f90,f43,f121])).

fof(f43,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f90,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f115,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(resolution,[],[f91,f45])).

fof(f45,plain,
    ( r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f106,plain,
    ( spl2_16
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f101,f82,f58,f104])).

fof(f58,plain,
    ( spl2_5
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f82,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f101,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(resolution,[],[f83,f59])).

fof(f59,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f82])).

fof(f96,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f36,f94])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f92,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f33,f90])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f88,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f34,f86])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f31,f82])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f76,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f72,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f68,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f60,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f56,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17,f16])).

fof(f16,plain,
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

fof(f17,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

fof(f51,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f25,f38])).

fof(f25,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:03:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (2887)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (2887)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f272,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f60,f68,f72,f76,f84,f88,f92,f96,f106,f124,f174,f180,f189,f223,f227,f271])).
% 0.21/0.42  fof(f271,plain,(
% 0.21/0.42    spl2_1 | ~spl2_12 | ~spl2_34),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f270])).
% 0.21/0.42  fof(f270,plain,(
% 0.21/0.42    $false | (spl2_1 | ~spl2_12 | ~spl2_34)),
% 0.21/0.42    inference(subsumption_resolution,[],[f261,f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,sK1) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f261,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1) | (~spl2_12 | ~spl2_34)),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f259])).
% 0.21/0.42  fof(f259,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1) | (~spl2_12 | ~spl2_34)),
% 0.21/0.42    inference(superposition,[],[f87,f222])).
% 0.21/0.42  fof(f222,plain,(
% 0.21/0.42    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl2_34),
% 0.21/0.42    inference(avatar_component_clause,[],[f220])).
% 0.21/0.42  fof(f220,plain,(
% 0.21/0.42    spl2_34 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl2_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f86])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    spl2_12 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.42  fof(f227,plain,(
% 0.21/0.42    ~spl2_4 | ~spl2_9 | spl2_31),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f226])).
% 0.21/0.42  fof(f226,plain,(
% 0.21/0.42    $false | (~spl2_4 | ~spl2_9 | spl2_31)),
% 0.21/0.42    inference(subsumption_resolution,[],[f225,f55])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    v1_relat_1(sK0) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f53])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl2_4 <=> v1_relat_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f225,plain,(
% 0.21/0.42    ~v1_relat_1(sK0) | (~spl2_9 | spl2_31)),
% 0.21/0.42    inference(resolution,[],[f210,f75])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f74])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl2_9 <=> ! [X1,X0] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.42  fof(f210,plain,(
% 0.21/0.42    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_31),
% 0.21/0.42    inference(avatar_component_clause,[],[f208])).
% 0.21/0.42  fof(f208,plain,(
% 0.21/0.42    spl2_31 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.42  fof(f223,plain,(
% 0.21/0.42    ~spl2_31 | spl2_34 | ~spl2_7 | ~spl2_29),
% 0.21/0.42    inference(avatar_split_clause,[],[f196,f185,f66,f220,f208])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl2_7 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.42  fof(f185,plain,(
% 0.21/0.42    spl2_29 <=> k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.42  fof(f196,plain,(
% 0.21/0.42    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_7 | ~spl2_29)),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f195])).
% 0.21/0.42  fof(f195,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_7 | ~spl2_29)),
% 0.21/0.42    inference(superposition,[],[f67,f187])).
% 0.21/0.42  fof(f187,plain,(
% 0.21/0.42    k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1)) | ~spl2_29),
% 0.21/0.42    inference(avatar_component_clause,[],[f185])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) ) | ~spl2_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f189,plain,(
% 0.21/0.42    spl2_29 | ~spl2_16 | ~spl2_28),
% 0.21/0.42    inference(avatar_split_clause,[],[f182,f177,f104,f185])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    spl2_16 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.42  fof(f177,plain,(
% 0.21/0.42    spl2_28 <=> k1_xboole_0 = k4_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.42  fof(f182,plain,(
% 0.21/0.42    k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_16 | ~spl2_28)),
% 0.21/0.42    inference(superposition,[],[f105,f179])).
% 0.21/0.42  fof(f179,plain,(
% 0.21/0.42    k1_xboole_0 = k4_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~spl2_28),
% 0.21/0.42    inference(avatar_component_clause,[],[f177])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f104])).
% 0.21/0.42  fof(f180,plain,(
% 0.21/0.42    spl2_28 | ~spl2_14 | ~spl2_27),
% 0.21/0.42    inference(avatar_split_clause,[],[f175,f171,f94,f177])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    spl2_14 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.42  fof(f171,plain,(
% 0.21/0.42    spl2_27 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.42  fof(f175,plain,(
% 0.21/0.42    k1_xboole_0 = k4_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | (~spl2_14 | ~spl2_27)),
% 0.21/0.42    inference(resolution,[],[f173,f95])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl2_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f94])).
% 0.21/0.42  fof(f173,plain,(
% 0.21/0.42    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~spl2_27),
% 0.21/0.42    inference(avatar_component_clause,[],[f171])).
% 0.21/0.42  fof(f174,plain,(
% 0.21/0.42    spl2_27 | ~spl2_3 | ~spl2_4 | ~spl2_8 | ~spl2_19),
% 0.21/0.42    inference(avatar_split_clause,[],[f169,f121,f70,f53,f48,f171])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl2_3 <=> v1_relat_1(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl2_8 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.42  fof(f121,plain,(
% 0.21/0.42    spl2_19 <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.42  fof(f169,plain,(
% 0.21/0.42    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | (~spl2_3 | ~spl2_4 | ~spl2_8 | ~spl2_19)),
% 0.21/0.42    inference(subsumption_resolution,[],[f168,f55])).
% 0.21/0.42  fof(f168,plain,(
% 0.21/0.42    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~v1_relat_1(sK0) | (~spl2_3 | ~spl2_8 | ~spl2_19)),
% 0.21/0.42    inference(subsumption_resolution,[],[f145,f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    v1_relat_1(sK1) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f48])).
% 0.21/0.42  fof(f145,plain,(
% 0.21/0.42    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | (~spl2_8 | ~spl2_19)),
% 0.21/0.42    inference(superposition,[],[f71,f123])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f121])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f70])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    spl2_19 | ~spl2_2 | ~spl2_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f115,f90,f43,f121])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl2_2 <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    spl2_13 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | (~spl2_2 | ~spl2_13)),
% 0.21/0.42    inference(resolution,[],[f91,f45])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f43])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl2_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f90])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    spl2_16 | ~spl2_5 | ~spl2_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f101,f82,f58,f104])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl2_5 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    spl2_11 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl2_5 | ~spl2_11)),
% 0.21/0.42    inference(resolution,[],[f83,f59])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl2_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f82])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    spl2_14),
% 0.21/0.42    inference(avatar_split_clause,[],[f36,f94])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    spl2_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f33,f90])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    spl2_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f34,f86])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    spl2_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f31,f82])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl2_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f74])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    spl2_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f70])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f66])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f58])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f53])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    v1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.21/0.42    inference(negated_conjecture,[],[f8])).
% 0.21/0.42  fof(f8,conjecture,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f48])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f43])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f38])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (2887)------------------------------
% 0.21/0.42  % (2887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (2887)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (2887)Memory used [KB]: 10618
% 0.21/0.42  % (2887)Time elapsed: 0.009 s
% 0.21/0.42  % (2887)------------------------------
% 0.21/0.42  % (2887)------------------------------
% 0.21/0.43  % (2882)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.43  % (2881)Success in time 0.067 s
%------------------------------------------------------------------------------

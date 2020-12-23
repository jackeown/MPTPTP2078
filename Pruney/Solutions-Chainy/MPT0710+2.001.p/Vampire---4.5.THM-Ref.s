%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 318 expanded)
%              Number of leaves         :   34 ( 145 expanded)
%              Depth                    :   10
%              Number of atoms          :  538 (1970 expanded)
%              Number of equality atoms :  144 ( 603 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f64,f69,f74,f79,f84,f89,f94,f102,f108,f162,f166,f177,f183,f224,f259,f264,f293,f326,f372,f380,f383])).

fof(f383,plain,
    ( spl5_1
    | ~ spl5_23
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f382,f378,f173,f48])).

fof(f48,plain,
    ( spl5_1
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f173,plain,
    ( spl5_23
  <=> sK2 = k3_xboole_0(k1_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f378,plain,
    ( spl5_42
  <=> ! [X0] :
        ( sK2 != k3_xboole_0(k1_relat_1(sK1),X0)
        | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f382,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl5_23
    | ~ spl5_42 ),
    inference(trivial_inequality_removal,[],[f381])).

fof(f381,plain,
    ( sK2 != sK2
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl5_23
    | ~ spl5_42 ),
    inference(superposition,[],[f379,f175])).

fof(f175,plain,
    ( sK2 = k3_xboole_0(k1_relat_1(sK1),sK2)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f173])).

fof(f379,plain,
    ( ! [X0] :
        ( sK2 != k3_xboole_0(k1_relat_1(sK1),X0)
        | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f378])).

fof(f380,plain,
    ( ~ spl5_18
    | ~ spl5_19
    | ~ spl5_8
    | ~ spl5_7
    | spl5_42
    | ~ spl5_12
    | ~ spl5_28
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f376,f369,f231,f105,f378,f76,f81,f146,f142])).

fof(f142,plain,
    ( spl5_18
  <=> v1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f146,plain,
    ( spl5_19
  <=> v1_funct_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f81,plain,
    ( spl5_8
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f76,plain,
    ( spl5_7
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f105,plain,
    ( spl5_12
  <=> sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f231,plain,
    ( spl5_28
  <=> k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f369,plain,
    ( spl5_41
  <=> k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f376,plain,
    ( ! [X0] :
        ( sK2 != k3_xboole_0(k1_relat_1(sK1),X0)
        | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(k7_relat_1(sK0,sK2))
        | ~ v1_relat_1(k7_relat_1(sK0,sK2)) )
    | ~ spl5_12
    | ~ spl5_28
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f375,f107])).

fof(f107,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f375,plain,
    ( ! [X0] :
        ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0)
        | k3_xboole_0(k1_relat_1(sK1),X0) != k1_relat_1(k7_relat_1(sK0,sK2))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(k7_relat_1(sK0,sK2))
        | ~ v1_relat_1(k7_relat_1(sK0,sK2)) )
    | ~ spl5_28
    | ~ spl5_41 ),
    inference(trivial_inequality_removal,[],[f374])).

fof(f374,plain,
    ( ! [X0] :
        ( k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) != k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1))
        | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0)
        | k3_xboole_0(k1_relat_1(sK1),X0) != k1_relat_1(k7_relat_1(sK0,sK2))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(k7_relat_1(sK0,sK2))
        | ~ v1_relat_1(k7_relat_1(sK0,sK2)) )
    | ~ spl5_28
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f373,f233])).

fof(f233,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),sK1))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f231])).

fof(f373,plain,
    ( ! [X0] :
        ( k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) != k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),sK1))
        | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0)
        | k3_xboole_0(k1_relat_1(sK1),X0) != k1_relat_1(k7_relat_1(sK0,sK2))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(k7_relat_1(sK0,sK2))
        | ~ v1_relat_1(k7_relat_1(sK0,sK2)) )
    | ~ spl5_41 ),
    inference(superposition,[],[f45,f371])).

fof(f371,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK0,sK2),sK1))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f369])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,sK4(X1,X2)) != k1_funct_1(X2,sK4(X1,X2))
      | k7_relat_1(X2,X0) = X1
      | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ( k1_funct_1(X1,sK4(X1,X2)) != k1_funct_1(X2,sK4(X1,X2))
            & r2_hidden(sK4(X1,X2),k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f28])).

fof(f28,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK4(X1,X2)) != k1_funct_1(X2,sK4(X1,X2))
        & r2_hidden(sK4(X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0) )
           => k7_relat_1(X2,X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).

fof(f372,plain,
    ( ~ spl5_10
    | spl5_41
    | ~ spl5_9
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f351,f221,f86,f369,f91])).

fof(f91,plain,
    ( spl5_10
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f86,plain,
    ( spl5_9
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f221,plain,
    ( spl5_27
  <=> r2_hidden(sK4(k7_relat_1(sK0,sK2),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f351,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl5_9
    | ~ spl5_27 ),
    inference(resolution,[],[f229,f88])).

fof(f88,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(k7_relat_1(X0,sK2),sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(X0,sK4(k7_relat_1(sK0,sK2),sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl5_27 ),
    inference(resolution,[],[f223,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(f223,plain,
    ( r2_hidden(sK4(k7_relat_1(sK0,sK2),sK1),sK2)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f221])).

fof(f326,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | k1_funct_1(sK0,sK3) != k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK0,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f293,plain,
    ( spl5_28
    | ~ spl5_4
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f292,f221,f62,f231])).

fof(f62,plain,
    ( spl5_4
  <=> ! [X4] :
        ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
        | ~ r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f292,plain,
    ( k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),sK1))
    | ~ spl5_4
    | ~ spl5_27 ),
    inference(resolution,[],[f63,f223])).

fof(f63,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f264,plain,
    ( ~ spl5_10
    | spl5_31
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f248,f86,f57,f261,f91])).

fof(f261,plain,
    ( spl5_31
  <=> k1_funct_1(sK0,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f57,plain,
    ( spl5_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f248,plain,
    ( k1_funct_1(sK0,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | ~ v1_relat_1(sK0)
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(resolution,[],[f226,f88])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(k7_relat_1(X0,sK2),sK3) = k1_funct_1(X0,sK3)
        | ~ v1_relat_1(X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f259,plain,
    ( ~ spl5_8
    | spl5_30
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f254,f76,f57,f48,f256,f81])).

fof(f256,plain,
    ( spl5_30
  <=> k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f254,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | ~ v1_relat_1(sK1)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f247,f49])).

fof(f49,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f247,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK1,sK2),sK3)
    | ~ v1_relat_1(sK1)
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f226,f78])).

fof(f78,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f224,plain,
    ( spl5_27
    | spl5_1
    | ~ spl5_19
    | ~ spl5_18
    | ~ spl5_12
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f219,f181,f105,f142,f146,f48,f221])).

fof(f181,plain,
    ( spl5_24
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK2
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k7_relat_1(sK1,sK2) = X0
        | r2_hidden(sK4(X0,sK1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f219,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | r2_hidden(sK4(k7_relat_1(sK0,sK2),sK1),sK2)
    | ~ spl5_12
    | ~ spl5_24 ),
    inference(trivial_inequality_removal,[],[f214])).

fof(f214,plain,
    ( sK2 != sK2
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | r2_hidden(sK4(k7_relat_1(sK0,sK2),sK1),sK2)
    | ~ spl5_12
    | ~ spl5_24 ),
    inference(superposition,[],[f182,f107])).

fof(f182,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK2
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k7_relat_1(sK1,sK2) = X0
        | r2_hidden(sK4(X0,sK1),sK2) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f181])).

fof(f183,plain,
    ( ~ spl5_8
    | ~ spl5_7
    | spl5_24
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f179,f173,f181,f76,f81])).

fof(f179,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK2
        | r2_hidden(sK4(X0,sK1),sK2)
        | k7_relat_1(sK1,sK2) = X0
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_23 ),
    inference(inner_rewriting,[],[f178])).

fof(f178,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK2
        | r2_hidden(sK4(X0,sK1),k1_relat_1(X0))
        | k7_relat_1(sK1,sK2) = X0
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_23 ),
    inference(superposition,[],[f44,f175])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | r2_hidden(sK4(X1,X2),k1_relat_1(X1))
      | k7_relat_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f177,plain,
    ( spl5_23
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f168,f99,f81,f173])).

fof(f99,plain,
    ( spl5_11
  <=> sK2 = k1_relat_1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f168,plain,
    ( sK2 = k3_xboole_0(k1_relat_1(sK1),sK2)
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(superposition,[],[f101,f95])).

fof(f95,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl5_8 ),
    inference(resolution,[],[f83,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f83,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f101,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK1,sK2))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f166,plain,
    ( ~ spl5_10
    | ~ spl5_9
    | spl5_19 ),
    inference(avatar_split_clause,[],[f165,f146,f86,f91])).

fof(f165,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl5_19 ),
    inference(resolution,[],[f148,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f148,plain,
    ( ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f146])).

fof(f162,plain,
    ( ~ spl5_10
    | ~ spl5_9
    | spl5_18 ),
    inference(avatar_split_clause,[],[f161,f142,f86,f91])).

fof(f161,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl5_18 ),
    inference(resolution,[],[f144,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f144,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f108,plain,
    ( ~ spl5_10
    | spl5_12
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f103,f71,f105,f91])).

fof(f71,plain,
    ( spl5_6
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f103,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f73,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f73,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f102,plain,
    ( ~ spl5_8
    | spl5_11
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f97,f66,f99,f81])).

fof(f66,plain,
    ( spl5_5
  <=> r1_tarski(sK2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f97,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f68,f41])).

fof(f68,plain,
    ( r1_tarski(sK2,k1_relat_1(sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f94,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f30,f91])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ( k1_funct_1(sK1,sK3) != k1_funct_1(sK0,sK3)
        & r2_hidden(sK3,sK2) )
      | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) )
    & ( ! [X4] :
          ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
          | ~ r2_hidden(X4,sK2) )
      | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) )
    & r1_tarski(sK2,k1_relat_1(sK1))
    & r1_tarski(sK2,k1_relat_1(sK0))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( k1_funct_1(X1,X3) != k1_funct_1(X0,X3)
                      & r2_hidden(X3,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
                & ( ! [X4] :
                      ( k1_funct_1(X1,X4) = k1_funct_1(X0,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
                & r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X1,X3) != k1_funct_1(sK0,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) )
              & ( ! [X4] :
                    ( k1_funct_1(X1,X4) = k1_funct_1(sK0,X4)
                    | ~ r2_hidden(X4,X2) )
                | k7_relat_1(X1,X2) = k7_relat_1(sK0,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(sK0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(X1,X3) != k1_funct_1(sK0,X3)
                  & r2_hidden(X3,X2) )
              | k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) )
            & ( ! [X4] :
                  ( k1_funct_1(X1,X4) = k1_funct_1(sK0,X4)
                  | ~ r2_hidden(X4,X2) )
              | k7_relat_1(X1,X2) = k7_relat_1(sK0,X2) )
            & r1_tarski(X2,k1_relat_1(X1))
            & r1_tarski(X2,k1_relat_1(sK0)) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(sK0,X3) != k1_funct_1(sK1,X3)
                & r2_hidden(X3,X2) )
            | k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
                | ~ r2_hidden(X4,X2) )
            | k7_relat_1(sK0,X2) = k7_relat_1(sK1,X2) )
          & r1_tarski(X2,k1_relat_1(sK1))
          & r1_tarski(X2,k1_relat_1(sK0)) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( k1_funct_1(sK0,X3) != k1_funct_1(sK1,X3)
              & r2_hidden(X3,X2) )
          | k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) )
        & ( ! [X4] :
              ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
              | ~ r2_hidden(X4,X2) )
          | k7_relat_1(sK0,X2) = k7_relat_1(sK1,X2) )
        & r1_tarski(X2,k1_relat_1(sK1))
        & r1_tarski(X2,k1_relat_1(sK0)) )
   => ( ( ? [X3] :
            ( k1_funct_1(sK0,X3) != k1_funct_1(sK1,X3)
            & r2_hidden(X3,sK2) )
        | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) )
      & ( ! [X4] :
            ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
            | ~ r2_hidden(X4,sK2) )
        | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) )
      & r1_tarski(sK2,k1_relat_1(sK1))
      & r1_tarski(sK2,k1_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( k1_funct_1(sK0,X3) != k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK2) )
   => ( k1_funct_1(sK1,sK3) != k1_funct_1(sK0,sK3)
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X1,X3) != k1_funct_1(X0,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X4] :
                    ( k1_funct_1(X1,X4) = k1_funct_1(X0,X4)
                    | ~ r2_hidden(X4,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X1,X3) != k1_funct_1(X0,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X3] :
                    ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                    | ~ r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X1,X3) != k1_funct_1(X0,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X3] :
                    ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                    | ~ r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <~> ! [X3] :
                    ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                    | ~ r2_hidden(X3,X2) ) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <~> ! [X3] :
                    ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                    | ~ r2_hidden(X3,X2) ) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( r1_tarski(X2,k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
               => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                <=> ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X1,X3) = k1_funct_1(X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
             => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X1,X3) = k1_funct_1(X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).

fof(f89,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f31,f86])).

fof(f31,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f32,f81])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f34,f71])).

fof(f34,plain,(
    r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    r1_tarski(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,
    ( spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f36,f62,f48])).

fof(f36,plain,(
    ! [X4] :
      ( k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f37,f57,f48])).

fof(f37,plain,
    ( r2_hidden(sK3,sK2)
    | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f38,f52,f48])).

fof(f52,plain,
    ( spl5_2
  <=> k1_funct_1(sK1,sK3) = k1_funct_1(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f38,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK0,sK3)
    | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (7516)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (7517)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.45  % (7524)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (7520)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (7520)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f384,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f55,f60,f64,f69,f74,f79,f84,f89,f94,f102,f108,f162,f166,f177,f183,f224,f259,f264,f293,f326,f372,f380,f383])).
% 0.21/0.46  fof(f383,plain,(
% 0.21/0.46    spl5_1 | ~spl5_23 | ~spl5_42),
% 0.21/0.46    inference(avatar_split_clause,[],[f382,f378,f173,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl5_1 <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    spl5_23 <=> sK2 = k3_xboole_0(k1_relat_1(sK1),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.46  fof(f378,plain,(
% 0.21/0.46    spl5_42 <=> ! [X0] : (sK2 != k3_xboole_0(k1_relat_1(sK1),X0) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.21/0.46  fof(f382,plain,(
% 0.21/0.46    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | (~spl5_23 | ~spl5_42)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f381])).
% 0.21/0.46  fof(f381,plain,(
% 0.21/0.46    sK2 != sK2 | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | (~spl5_23 | ~spl5_42)),
% 0.21/0.46    inference(superposition,[],[f379,f175])).
% 0.21/0.46  fof(f175,plain,(
% 0.21/0.46    sK2 = k3_xboole_0(k1_relat_1(sK1),sK2) | ~spl5_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f173])).
% 0.21/0.46  fof(f379,plain,(
% 0.21/0.46    ( ! [X0] : (sK2 != k3_xboole_0(k1_relat_1(sK1),X0) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0)) ) | ~spl5_42),
% 0.21/0.46    inference(avatar_component_clause,[],[f378])).
% 0.21/0.46  fof(f380,plain,(
% 0.21/0.46    ~spl5_18 | ~spl5_19 | ~spl5_8 | ~spl5_7 | spl5_42 | ~spl5_12 | ~spl5_28 | ~spl5_41),
% 0.21/0.46    inference(avatar_split_clause,[],[f376,f369,f231,f105,f378,f76,f81,f146,f142])).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    spl5_18 <=> v1_relat_1(k7_relat_1(sK0,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    spl5_19 <=> v1_funct_1(k7_relat_1(sK0,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl5_8 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl5_7 <=> v1_funct_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    spl5_12 <=> sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.46  fof(f231,plain,(
% 0.21/0.46    spl5_28 <=> k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.46  fof(f369,plain,(
% 0.21/0.46    spl5_41 <=> k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK0,sK2),sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.21/0.46  fof(f376,plain,(
% 0.21/0.46    ( ! [X0] : (sK2 != k3_xboole_0(k1_relat_1(sK1),X0) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(k7_relat_1(sK0,sK2))) ) | (~spl5_12 | ~spl5_28 | ~spl5_41)),
% 0.21/0.46    inference(forward_demodulation,[],[f375,f107])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) | ~spl5_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f105])).
% 0.21/0.46  fof(f375,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0) | k3_xboole_0(k1_relat_1(sK1),X0) != k1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(k7_relat_1(sK0,sK2))) ) | (~spl5_28 | ~spl5_41)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f374])).
% 0.21/0.46  fof(f374,plain,(
% 0.21/0.46    ( ! [X0] : (k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) != k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0) | k3_xboole_0(k1_relat_1(sK1),X0) != k1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(k7_relat_1(sK0,sK2))) ) | (~spl5_28 | ~spl5_41)),
% 0.21/0.46    inference(forward_demodulation,[],[f373,f233])).
% 0.21/0.46  fof(f233,plain,(
% 0.21/0.46    k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),sK1)) | ~spl5_28),
% 0.21/0.46    inference(avatar_component_clause,[],[f231])).
% 0.21/0.46  fof(f373,plain,(
% 0.21/0.46    ( ! [X0] : (k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) != k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),sK1)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,X0) | k3_xboole_0(k1_relat_1(sK1),X0) != k1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(k7_relat_1(sK0,sK2))) ) | ~spl5_41),
% 0.21/0.46    inference(superposition,[],[f45,f371])).
% 0.21/0.46  fof(f371,plain,(
% 0.21/0.46    k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK0,sK2),sK1)) | ~spl5_41),
% 0.21/0.46    inference(avatar_component_clause,[],[f369])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_funct_1(X1,sK4(X1,X2)) != k1_funct_1(X2,sK4(X1,X2)) | k7_relat_1(X2,X0) = X1 | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | (k1_funct_1(X1,sK4(X1,X2)) != k1_funct_1(X2,sK4(X1,X2)) & r2_hidden(sK4(X1,X2),k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X2,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK4(X1,X2)) != k1_funct_1(X2,sK4(X1,X2)) & r2_hidden(sK4(X1,X2),k1_relat_1(X1))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | ? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : ((k7_relat_1(X2,X0) = X1 | (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)) => k7_relat_1(X2,X0) = X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).
% 0.21/0.46  fof(f372,plain,(
% 0.21/0.46    ~spl5_10 | spl5_41 | ~spl5_9 | ~spl5_27),
% 0.21/0.46    inference(avatar_split_clause,[],[f351,f221,f86,f369,f91])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    spl5_10 <=> v1_relat_1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    spl5_9 <=> v1_funct_1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.46  fof(f221,plain,(
% 0.21/0.46    spl5_27 <=> r2_hidden(sK4(k7_relat_1(sK0,sK2),sK1),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.46  fof(f351,plain,(
% 0.21/0.46    k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(k7_relat_1(sK0,sK2),sK4(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK0) | (~spl5_9 | ~spl5_27)),
% 0.21/0.46    inference(resolution,[],[f229,f88])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    v1_funct_1(sK0) | ~spl5_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f86])).
% 0.21/0.46  fof(f229,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_funct_1(X0) | k1_funct_1(k7_relat_1(X0,sK2),sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(X0,sK4(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(X0)) ) | ~spl5_27),
% 0.21/0.46    inference(resolution,[],[f223,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).
% 0.21/0.46  fof(f223,plain,(
% 0.21/0.46    r2_hidden(sK4(k7_relat_1(sK0,sK2),sK1),sK2) | ~spl5_27),
% 0.21/0.46    inference(avatar_component_clause,[],[f221])).
% 0.21/0.46  fof(f326,plain,(
% 0.21/0.46    k1_funct_1(sK1,sK3) != k1_funct_1(k7_relat_1(sK0,sK2),sK3) | k1_funct_1(sK0,sK3) != k1_funct_1(k7_relat_1(sK0,sK2),sK3) | k1_funct_1(sK1,sK3) = k1_funct_1(sK0,sK3)),
% 0.21/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.46  fof(f293,plain,(
% 0.21/0.46    spl5_28 | ~spl5_4 | ~spl5_27),
% 0.21/0.46    inference(avatar_split_clause,[],[f292,f221,f62,f231])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl5_4 <=> ! [X4] : (k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.46  fof(f292,plain,(
% 0.21/0.46    k1_funct_1(sK0,sK4(k7_relat_1(sK0,sK2),sK1)) = k1_funct_1(sK1,sK4(k7_relat_1(sK0,sK2),sK1)) | (~spl5_4 | ~spl5_27)),
% 0.21/0.46    inference(resolution,[],[f63,f223])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X4] : (~r2_hidden(X4,sK2) | k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4)) ) | ~spl5_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f62])).
% 0.21/0.46  fof(f264,plain,(
% 0.21/0.46    ~spl5_10 | spl5_31 | ~spl5_3 | ~spl5_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f248,f86,f57,f261,f91])).
% 0.21/0.46  fof(f261,plain,(
% 0.21/0.46    spl5_31 <=> k1_funct_1(sK0,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    spl5_3 <=> r2_hidden(sK3,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.46  fof(f248,plain,(
% 0.21/0.46    k1_funct_1(sK0,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3) | ~v1_relat_1(sK0) | (~spl5_3 | ~spl5_9)),
% 0.21/0.46    inference(resolution,[],[f226,f88])).
% 0.21/0.46  fof(f226,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_funct_1(X0) | k1_funct_1(k7_relat_1(X0,sK2),sK3) = k1_funct_1(X0,sK3) | ~v1_relat_1(X0)) ) | ~spl5_3),
% 0.21/0.46    inference(resolution,[],[f59,f46])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    r2_hidden(sK3,sK2) | ~spl5_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f57])).
% 0.21/0.46  fof(f259,plain,(
% 0.21/0.46    ~spl5_8 | spl5_30 | ~spl5_1 | ~spl5_3 | ~spl5_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f254,f76,f57,f48,f256,f81])).
% 0.21/0.46  fof(f256,plain,(
% 0.21/0.46    spl5_30 <=> k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.46  fof(f254,plain,(
% 0.21/0.46    k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3) | ~v1_relat_1(sK1) | (~spl5_1 | ~spl5_3 | ~spl5_7)),
% 0.21/0.46    inference(forward_demodulation,[],[f247,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~spl5_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f247,plain,(
% 0.21/0.46    k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK1,sK2),sK3) | ~v1_relat_1(sK1) | (~spl5_3 | ~spl5_7)),
% 0.21/0.46    inference(resolution,[],[f226,f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    v1_funct_1(sK1) | ~spl5_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f76])).
% 0.21/0.46  fof(f224,plain,(
% 0.21/0.46    spl5_27 | spl5_1 | ~spl5_19 | ~spl5_18 | ~spl5_12 | ~spl5_24),
% 0.21/0.46    inference(avatar_split_clause,[],[f219,f181,f105,f142,f146,f48,f221])).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    spl5_24 <=> ! [X0] : (k1_relat_1(X0) != sK2 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k7_relat_1(sK1,sK2) = X0 | r2_hidden(sK4(X0,sK1),sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.46  fof(f219,plain,(
% 0.21/0.46    ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | r2_hidden(sK4(k7_relat_1(sK0,sK2),sK1),sK2) | (~spl5_12 | ~spl5_24)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f214])).
% 0.21/0.46  fof(f214,plain,(
% 0.21/0.46    sK2 != sK2 | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | r2_hidden(sK4(k7_relat_1(sK0,sK2),sK1),sK2) | (~spl5_12 | ~spl5_24)),
% 0.21/0.46    inference(superposition,[],[f182,f107])).
% 0.21/0.46  fof(f182,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(X0) != sK2 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k7_relat_1(sK1,sK2) = X0 | r2_hidden(sK4(X0,sK1),sK2)) ) | ~spl5_24),
% 0.21/0.46    inference(avatar_component_clause,[],[f181])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    ~spl5_8 | ~spl5_7 | spl5_24 | ~spl5_23),
% 0.21/0.46    inference(avatar_split_clause,[],[f179,f173,f181,f76,f81])).
% 0.21/0.46  fof(f179,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(X0) != sK2 | r2_hidden(sK4(X0,sK1),sK2) | k7_relat_1(sK1,sK2) = X0 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_23),
% 0.21/0.46    inference(inner_rewriting,[],[f178])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(X0) != sK2 | r2_hidden(sK4(X0,sK1),k1_relat_1(X0)) | k7_relat_1(sK1,sK2) = X0 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_23),
% 0.21/0.46    inference(superposition,[],[f44,f175])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | r2_hidden(sK4(X1,X2),k1_relat_1(X1)) | k7_relat_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f177,plain,(
% 0.21/0.46    spl5_23 | ~spl5_8 | ~spl5_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f168,f99,f81,f173])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl5_11 <=> sK2 = k1_relat_1(k7_relat_1(sK1,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    sK2 = k3_xboole_0(k1_relat_1(sK1),sK2) | (~spl5_8 | ~spl5_11)),
% 0.21/0.46    inference(superposition,[],[f101,f95])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl5_8),
% 0.21/0.46    inference(resolution,[],[f83,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl5_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f81])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    sK2 = k1_relat_1(k7_relat_1(sK1,sK2)) | ~spl5_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f99])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    ~spl5_10 | ~spl5_9 | spl5_19),
% 0.21/0.46    inference(avatar_split_clause,[],[f165,f146,f86,f91])).
% 0.21/0.46  fof(f165,plain,(
% 0.21/0.46    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl5_19),
% 0.21/0.46    inference(resolution,[],[f148,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    ~v1_funct_1(k7_relat_1(sK0,sK2)) | spl5_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f146])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    ~spl5_10 | ~spl5_9 | spl5_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f161,f142,f86,f91])).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl5_18),
% 0.21/0.46    inference(resolution,[],[f144,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    ~v1_relat_1(k7_relat_1(sK0,sK2)) | spl5_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f142])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    ~spl5_10 | spl5_12 | ~spl5_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f103,f71,f105,f91])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    spl5_6 <=> r1_tarski(sK2,k1_relat_1(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | ~spl5_6),
% 0.21/0.46    inference(resolution,[],[f73,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    r1_tarski(sK2,k1_relat_1(sK0)) | ~spl5_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f71])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    ~spl5_8 | spl5_11 | ~spl5_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f97,f66,f99,f81])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl5_5 <=> r1_tarski(sK2,k1_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    sK2 = k1_relat_1(k7_relat_1(sK1,sK2)) | ~v1_relat_1(sK1) | ~spl5_5),
% 0.21/0.46    inference(resolution,[],[f68,f41])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    r1_tarski(sK2,k1_relat_1(sK1)) | ~spl5_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f66])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    spl5_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f91])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    v1_relat_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ((((k1_funct_1(sK1,sK3) != k1_funct_1(sK0,sK3) & r2_hidden(sK3,sK2)) | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)) & (! [X4] : (k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,sK2)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)) & r1_tarski(sK2,k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f26,f25,f24,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X0,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X0,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(sK0,X3) & r2_hidden(X3,X2)) | k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(sK0,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X1,X2) = k7_relat_1(sK0,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(sK0,X3) & r2_hidden(X3,X2)) | k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(sK0,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X1,X2) = k7_relat_1(sK0,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(sK0,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,X2)) | k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)) & (! [X4] : (k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(sK0,X2) = k7_relat_1(sK1,X2)) & r1_tarski(X2,k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ? [X2] : ((? [X3] : (k1_funct_1(sK0,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,X2)) | k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)) & (! [X4] : (k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(sK0,X2) = k7_relat_1(sK1,X2)) & r1_tarski(X2,k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) => ((? [X3] : (k1_funct_1(sK0,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,sK2)) | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)) & (! [X4] : (k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,sK2)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)) & r1_tarski(sK2,k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ? [X3] : (k1_funct_1(sK0,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,sK2)) => (k1_funct_1(sK1,sK3) != k1_funct_1(sK0,sK3) & r2_hidden(sK3,sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X0,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X0,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.46    inference(rectify,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X0,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X0,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2))) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2))) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2))) & (r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X1,X3) = k1_funct_1(X0,X3))))))),
% 0.21/0.46    inference(negated_conjecture,[],[f7])).
% 0.21/0.46  fof(f7,conjecture,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X1,X3) = k1_funct_1(X0,X3))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    spl5_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f86])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    v1_funct_1(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    spl5_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f32,f81])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl5_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f76])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    v1_funct_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    spl5_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f34,f71])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    r1_tarski(sK2,k1_relat_1(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl5_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f35,f66])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    r1_tarski(sK2,k1_relat_1(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    spl5_1 | spl5_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f36,f62,f48])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X4] : (k1_funct_1(sK0,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,sK2) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ~spl5_1 | spl5_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f37,f57,f48])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    r2_hidden(sK3,sK2) | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ~spl5_1 | ~spl5_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f38,f52,f48])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl5_2 <=> k1_funct_1(sK1,sK3) = k1_funct_1(sK0,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    k1_funct_1(sK1,sK3) != k1_funct_1(sK0,sK3) | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (7520)------------------------------
% 0.21/0.46  % (7520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (7520)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (7520)Memory used [KB]: 10874
% 0.21/0.46  % (7520)Time elapsed: 0.057 s
% 0.21/0.46  % (7520)------------------------------
% 0.21/0.46  % (7520)------------------------------
% 0.21/0.47  % (7521)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (7512)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (7509)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (7513)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (7514)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (7519)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (7523)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (7511)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (7508)Success in time 0.136 s
%------------------------------------------------------------------------------

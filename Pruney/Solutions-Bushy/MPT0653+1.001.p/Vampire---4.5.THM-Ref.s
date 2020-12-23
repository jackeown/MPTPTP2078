%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0653+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 358 expanded)
%              Number of leaves         :   22 ( 129 expanded)
%              Depth                    :   17
%              Number of atoms          :  775 (1803 expanded)
%              Number of equality atoms :  148 ( 491 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f734,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f99,f104,f109,f259,f267,f278,f290,f299,f319,f329,f345,f346,f371,f380,f505,f726,f727,f733])).

fof(f733,plain,
    ( ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | spl8_15
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f732])).

fof(f732,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | spl8_15
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f730,f288])).

fof(f288,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | spl8_15 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl8_15
  <=> sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f730,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f729,f344])).

fof(f344,plain,
    ( r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl8_18
  <=> r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f729,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f517,f266])).

fof(f266,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl8_13
  <=> r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f517,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(superposition,[],[f130,f258])).

fof(f258,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl8_12
  <=> sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f130,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1))
        | ~ r2_hidden(X3,k2_relat_1(sK0))
        | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 )
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f129,f108])).

fof(f108,plain,
    ( k1_relat_1(sK1) = k2_relat_1(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl8_8
  <=> k1_relat_1(sK1) = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f129,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1))
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 )
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f41,f103])).

fof(f103,plain,
    ( k1_relat_1(sK0) = k2_relat_1(sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl8_7
  <=> k1_relat_1(sK0) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f41,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f11])).

fof(f11,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK1,X3) != X2
      | k1_funct_1(sK0,X2) = X3 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2,X3] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X2,k1_relat_1(X0)) )
                   => ( k1_funct_1(X0,X2) = X3
                    <=> k1_funct_1(X1,X3) = X2 ) )
                & k2_relat_1(X0) = k1_relat_1(X1)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2,X3] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X2,k1_relat_1(X0)) )
                 => ( k1_funct_1(X0,X2) = X3
                  <=> k1_funct_1(X1,X3) = X2 ) )
              & k2_relat_1(X0) = k1_relat_1(X1)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_1)).

fof(f727,plain,
    ( sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sP6(sK3(sK0,sK1),sK1)
    | ~ sP6(k1_funct_1(sK1,sK2(sK0,sK1)),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f726,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f724,f253])).

fof(f253,plain,
    ( sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl8_11
  <=> sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f724,plain,
    ( ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f350,f289])).

fof(f289,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f287])).

fof(f350,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f349,f98])).

fof(f98,plain,
    ( sK1 != k2_funct_1(sK0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl8_6
  <=> sK1 = k2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f349,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f348,f108])).

fof(f348,plain,
    ( k1_relat_1(sK1) != k2_relat_1(sK0)
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f347,f62])).

fof(f62,plain,
    ( v1_funct_1(sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl8_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f347,plain,
    ( ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f322,f57])).

fof(f57,plain,
    ( v1_relat_1(sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl8_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f322,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(resolution,[],[f266,f116])).

fof(f116,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK3(sK0,X3),k2_relat_1(sK1))
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | k2_relat_1(sK0) != k1_relat_1(X3)
        | sK2(sK0,X3) != k1_funct_1(sK0,sK3(sK0,X3))
        | ~ sP4(sK3(sK0,X3),sK2(sK0,X3),X3,sK0)
        | k2_funct_1(sK0) = X3 )
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f115,f72])).

fof(f72,plain,
    ( v1_relat_1(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl8_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f115,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK3(sK0,X3),k2_relat_1(sK1))
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | k2_relat_1(sK0) != k1_relat_1(X3)
        | ~ v1_relat_1(sK0)
        | sK2(sK0,X3) != k1_funct_1(sK0,sK3(sK0,X3))
        | ~ sP4(sK3(sK0,X3),sK2(sK0,X3),X3,sK0)
        | k2_funct_1(sK0) = X3 )
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f114,f67])).

fof(f67,plain,
    ( v2_funct_1(sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl8_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f114,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK3(sK0,X3),k2_relat_1(sK1))
        | ~ v2_funct_1(sK0)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | k2_relat_1(sK0) != k1_relat_1(X3)
        | ~ v1_relat_1(sK0)
        | sK2(sK0,X3) != k1_funct_1(sK0,sK3(sK0,X3))
        | ~ sP4(sK3(sK0,X3),sK2(sK0,X3),X3,sK0)
        | k2_funct_1(sK0) = X3 )
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f112,f77])).

fof(f77,plain,
    ( v1_funct_1(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f112,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK3(sK0,X3),k2_relat_1(sK1))
        | ~ v1_funct_1(sK0)
        | ~ v2_funct_1(sK0)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | k2_relat_1(sK0) != k1_relat_1(X3)
        | ~ v1_relat_1(sK0)
        | sK2(sK0,X3) != k1_funct_1(sK0,sK3(sK0,X3))
        | ~ sP4(sK3(sK0,X3),sK2(sK0,X3),X3,sK0)
        | k2_funct_1(sK0) = X3 )
    | ~ spl8_7 ),
    inference(superposition,[],[f26,f103])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | sK2(X0,X1) != k1_funct_1(X0,sK3(X0,X1))
      | ~ sP4(sK3(X0,X1),sK2(X0,X1),X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(f505,plain,
    ( ~ spl8_7
    | ~ spl8_8
    | spl8_12
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_8
    | spl8_12
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f374,f257])).

fof(f257,plain,
    ( sK3(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f256])).

fof(f374,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f373,f266])).

fof(f373,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_15
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f359,f344])).

fof(f359,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_15 ),
    inference(superposition,[],[f128,f289])).

fof(f128,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_funct_1(sK0,X2),k2_relat_1(sK0))
        | ~ r2_hidden(X2,k2_relat_1(sK1))
        | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2 )
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f127,f108])).

fof(f127,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK1))
        | ~ r2_hidden(k1_funct_1(sK0,X2),k1_relat_1(sK1))
        | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2 )
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f40,f103])).

fof(f40,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ r2_hidden(k1_funct_1(sK0,X2),k1_relat_1(sK1))
      | k1_funct_1(sK1,k1_funct_1(sK0,X2)) = X2 ) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK1,X3) = X2
      | k1_funct_1(sK0,X2) != X3 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f380,plain,
    ( spl8_19
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f368,f342,f106,f377])).

fof(f377,plain,
    ( spl8_19
  <=> sP6(k1_funct_1(sK1,sK2(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f368,plain,
    ( sP6(k1_funct_1(sK1,sK2(sK0,sK1)),sK1)
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(resolution,[],[f344,f119])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | sP6(k1_funct_1(sK1,X0),sK1) )
    | ~ spl8_8 ),
    inference(superposition,[],[f53,f108])).

fof(f53,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | sP6(k1_funct_1(X0,X3),X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f371,plain,
    ( spl8_11
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl8_11
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f367,f254])).

fof(f254,plain,
    ( ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f252])).

fof(f367,plain,
    ( sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | ~ spl8_12
    | ~ spl8_18 ),
    inference(resolution,[],[f344,f315])).

fof(f315,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK2(sK0,sK1),k2_relat_1(X4))
        | sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,X4) )
    | ~ spl8_12 ),
    inference(superposition,[],[f48,f258])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP4(k1_funct_1(X1,X2),X2,X1,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | k1_funct_1(X1,X2) != X3
      | sP4(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f346,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK0,sK3(sK0,sK1))
    | sP6(sK2(sK0,sK1),sK0)
    | ~ sP6(k1_funct_1(sK0,sK3(sK0,sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f345,plain,
    ( spl8_18
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f330,f326,f75,f70,f342])).

fof(f326,plain,
    ( spl8_17
  <=> sP6(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f330,plain,
    ( r2_hidden(sK2(sK0,sK1),k2_relat_1(sK0))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_17 ),
    inference(resolution,[],[f328,f91])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ sP6(X0,sK0)
        | r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f87,f72])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK0)
        | ~ sP6(X0,sK0)
        | r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f77,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP6(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f328,plain,
    ( sP6(sK2(sK0,sK1),sK0)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f326])).

fof(f329,plain,
    ( spl8_17
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f309,f252,f106,f96,f75,f70,f65,f60,f55,f326])).

fof(f309,plain,
    ( sP6(sK2(sK0,sK1),sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f308,f98])).

fof(f308,plain,
    ( sP6(sK2(sK0,sK1),sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f307,f108])).

fof(f307,plain,
    ( k1_relat_1(sK1) != k2_relat_1(sK0)
    | sP6(sK2(sK0,sK1),sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f306,f62])).

fof(f306,plain,
    ( ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | sP6(sK2(sK0,sK1),sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f301,f57])).

fof(f301,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | sP6(sK2(sK0,sK1),sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11 ),
    inference(resolution,[],[f253,f145])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ sP4(sK3(sK0,X0),sK2(sK0,X0),X0,sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | sP6(sK2(sK0,X0),sK0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f144,f72])).

fof(f144,plain,
    ( ! [X0] :
        ( sP6(sK2(sK0,X0),sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ sP4(sK3(sK0,X0),sK2(sK0,X0),X0,sK0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f143,f67])).

fof(f143,plain,
    ( ! [X0] :
        ( sP6(sK2(sK0,X0),sK0)
        | ~ v2_funct_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ sP4(sK3(sK0,X0),sK2(sK0,X0),X0,sK0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f141,f77])).

fof(f141,plain,
    ( ! [X0] :
        ( sP6(sK2(sK0,X0),sK0)
        | ~ v1_funct_1(sK0)
        | ~ v2_funct_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ sP4(sK3(sK0,X0),sK2(sK0,X0),X0,sK0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(resolution,[],[f92,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ sP4(sK3(X0,X1),sK2(X0,X1),X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f92,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK0))
        | sP6(X1,sK0) )
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f88,f72])).

fof(f88,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK0)
        | sP6(X1,sK0)
        | ~ r2_hidden(X1,k2_relat_1(sK0)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f77,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP6(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP6(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f319,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_13
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f282,f265])).

fof(f265,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | spl8_13 ),
    inference(avatar_component_clause,[],[f264])).

fof(f282,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(resolution,[],[f277,f83])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ sP6(X0,sK1)
        | r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f79,f57])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ sP6(X0,sK1)
        | r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f62,f52])).

fof(f277,plain,
    ( sP6(sK3(sK0,sK1),sK1)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl8_14
  <=> sP6(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f299,plain,
    ( spl8_16
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f272,f264,f101,f296])).

fof(f296,plain,
    ( spl8_16
  <=> sP6(k1_funct_1(sK0,sK3(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f272,plain,
    ( sP6(k1_funct_1(sK0,sK3(sK0,sK1)),sK0)
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(resolution,[],[f266,f110])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | sP6(k1_funct_1(sK0,X0),sK0) )
    | ~ spl8_7 ),
    inference(superposition,[],[f53,f103])).

fof(f290,plain,
    ( spl8_15
    | spl8_11 ),
    inference(avatar_split_clause,[],[f261,f252,f287])).

fof(f261,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK0,sK3(sK0,sK1))
    | spl8_11 ),
    inference(resolution,[],[f254,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X2,X1,X0)
      | k1_funct_1(X0,X3) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f278,plain,
    ( spl8_14
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f273,f264,f60,f55,f275])).

fof(f273,plain,
    ( sP6(sK3(sK0,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_13 ),
    inference(resolution,[],[f266,f84])).

fof(f84,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK1))
        | sP6(X1,sK1) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f80,f57])).

fof(f80,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK1)
        | sP6(X1,sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f62,f51])).

fof(f267,plain,
    ( spl8_13
    | ~ spl8_7
    | spl8_11 ),
    inference(avatar_split_clause,[],[f262,f252,f101,f264])).

fof(f262,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_relat_1(sK1))
    | ~ spl8_7
    | spl8_11 ),
    inference(forward_demodulation,[],[f260,f103])).

fof(f260,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_relat_1(sK0))
    | spl8_11 ),
    inference(resolution,[],[f254,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X2,X1,X0)
      | r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f259,plain,
    ( ~ spl8_11
    | spl8_12
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f205,f106,f96,f75,f70,f65,f60,f55,f256,f252])).

fof(f205,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f204,f98])).

fof(f204,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f203,f72])).

fof(f203,plain,
    ( ~ v1_relat_1(sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f202,f67])).

fof(f202,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f201,f77])).

fof(f201,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ sP4(sK3(sK0,sK1),sK2(sK0,sK1),sK1,sK0)
    | sK1 = k2_funct_1(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,
    ( ! [X4] :
        ( k2_relat_1(sK0) != k2_relat_1(X4)
        | ~ v1_funct_1(X4)
        | ~ v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | sK3(X4,sK1) = k1_funct_1(sK1,sK2(X4,sK1))
        | ~ sP4(sK3(X4,sK1),sK2(X4,sK1),sK1,X4)
        | sK1 = k2_funct_1(X4) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f125,f62])).

fof(f125,plain,
    ( ! [X4] :
        ( k2_relat_1(sK0) != k2_relat_1(X4)
        | ~ v1_funct_1(X4)
        | ~ v2_funct_1(X4)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X4)
        | sK3(X4,sK1) = k1_funct_1(sK1,sK2(X4,sK1))
        | ~ sP4(sK3(X4,sK1),sK2(X4,sK1),sK1,X4)
        | sK1 = k2_funct_1(X4) )
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f122,f57])).

fof(f122,plain,
    ( ! [X4] :
        ( k2_relat_1(sK0) != k2_relat_1(X4)
        | ~ v1_funct_1(X4)
        | ~ v2_funct_1(X4)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X4)
        | sK3(X4,sK1) = k1_funct_1(sK1,sK2(X4,sK1))
        | ~ sP4(sK3(X4,sK1),sK2(X4,sK1),sK1,X4)
        | sK1 = k2_funct_1(X4) )
    | ~ spl8_8 ),
    inference(superposition,[],[f30,f108])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | sK3(X0,X1) = k1_funct_1(X1,sK2(X0,X1))
      | ~ sP4(sK3(X0,X1),sK2(X0,X1),X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f109,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f17,f106])).

fof(f17,plain,(
    k1_relat_1(sK1) = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f104,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f16,f101])).

fof(f16,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f99,plain,(
    ~ spl8_6 ),
    inference(avatar_split_clause,[],[f18,f96])).

fof(f18,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f20,f75])).

fof(f20,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f73,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f19,f70])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f68,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f15,f65])).

fof(f15,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f63,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f14,f60])).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f13,f55])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------

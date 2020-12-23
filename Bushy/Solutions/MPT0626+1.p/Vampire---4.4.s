%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t21_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:22 EDT 2019

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 273 expanded)
%              Number of leaves         :   26 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  429 ( 905 expanded)
%              Number of equality atoms :   22 (  58 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f107,f119,f146,f150,f236,f241,f409,f687,f8546,f8731,f9480,f9890,f10504,f11972,f12011,f12029,f12334,f12348])).

fof(f12348,plain,
    ( spl11_18
    | ~ spl11_950 ),
    inference(avatar_split_clause,[],[f12343,f12332,f144])).

fof(f144,plain,
    ( spl11_18
  <=> sP4(sK0,k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f12332,plain,
    ( spl11_950
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,k1_funct_1(sK2,sK0))),k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_950])])).

fof(f12343,plain,
    ( sP4(sK0,k5_relat_1(sK2,sK1))
    | ~ spl11_950 ),
    inference(resolution,[],[f12333,f48])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t21_funct_1.p',d4_relat_1)).

fof(f12333,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,k1_funct_1(sK2,sK0))),k5_relat_1(sK2,sK1))
    | ~ spl11_950 ),
    inference(avatar_component_clause,[],[f12332])).

fof(f12334,plain,
    ( spl11_950
    | ~ spl11_0
    | ~ spl11_4
    | ~ spl11_20
    | ~ spl11_924 ),
    inference(avatar_split_clause,[],[f12039,f12027,f148,f82,f74,f12332])).

fof(f74,plain,
    ( spl11_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f82,plain,
    ( spl11_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f148,plain,
    ( spl11_20
  <=> v1_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f12027,plain,
    ( spl11_924
  <=> sP8(k1_funct_1(sK1,k1_funct_1(sK2,sK0)),sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_924])])).

fof(f12039,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,k1_funct_1(sK2,sK0))),k5_relat_1(sK2,sK1))
    | ~ spl11_0
    | ~ spl11_4
    | ~ spl11_20
    | ~ spl11_924 ),
    inference(subsumption_resolution,[],[f12038,f75])).

fof(f75,plain,
    ( v1_relat_1(sK2)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f74])).

fof(f12038,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,k1_funct_1(sK2,sK0))),k5_relat_1(sK2,sK1))
    | ~ spl11_4
    | ~ spl11_20
    | ~ spl11_924 ),
    inference(subsumption_resolution,[],[f12037,f149])).

fof(f149,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f148])).

fof(f12037,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,k1_funct_1(sK2,sK0))),k5_relat_1(sK2,sK1))
    | ~ spl11_4
    | ~ spl11_924 ),
    inference(subsumption_resolution,[],[f12036,f83])).

fof(f83,plain,
    ( v1_relat_1(sK1)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f12036,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,k1_funct_1(sK2,sK0))),k5_relat_1(sK2,sK1))
    | ~ spl11_924 ),
    inference(resolution,[],[f12028,f72])).

fof(f72,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP8(X4,X3,X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ sP8(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t21_funct_1.p',d8_relat_1)).

fof(f12028,plain,
    ( sP8(k1_funct_1(sK1,k1_funct_1(sK2,sK0)),sK0,sK1,sK2)
    | ~ spl11_924 ),
    inference(avatar_component_clause,[],[f12027])).

fof(f12029,plain,
    ( spl11_924
    | ~ spl11_42
    | ~ spl11_920 ),
    inference(avatar_split_clause,[],[f12017,f12009,f234,f12027])).

fof(f234,plain,
    ( spl11_42
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f12009,plain,
    ( spl11_920
  <=> r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK1,k1_funct_1(sK2,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_920])])).

fof(f12017,plain,
    ( sP8(k1_funct_1(sK1,k1_funct_1(sK2,sK0)),sK0,sK1,sK2)
    | ~ spl11_42
    | ~ spl11_920 ),
    inference(resolution,[],[f12010,f9679])).

fof(f9679,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X2),X3)
        | sP8(X2,sK0,X3,sK2) )
    | ~ spl11_42 ),
    inference(resolution,[],[f235,f54])).

fof(f54,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | sP8(X4,X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f235,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f234])).

fof(f12010,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK1,k1_funct_1(sK2,sK0))),sK1)
    | ~ spl11_920 ),
    inference(avatar_component_clause,[],[f12009])).

fof(f12011,plain,
    ( spl11_920
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f11982,f117,f86,f82,f12009])).

fof(f86,plain,
    ( spl11_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f117,plain,
    ( spl11_12
  <=> r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f11982,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK1,k1_funct_1(sK2,sK0))),sK1)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f11981,f83])).

fof(f11981,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK1,k1_funct_1(sK2,sK0))),sK1)
    | ~ spl11_6
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f11977,f87])).

fof(f87,plain,
    ( v1_funct_1(sK1)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f11977,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK1,k1_funct_1(sK2,sK0))),sK1)
    | ~ spl11_12 ),
    inference(resolution,[],[f118,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t21_funct_1.p',d4_funct_1)).

fof(f118,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f11972,plain,
    ( spl11_732
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_538
    | ~ spl11_682 ),
    inference(avatar_split_clause,[],[f11966,f9478,f8544,f105,f78,f74,f9880])).

fof(f9880,plain,
    ( spl11_732
  <=> sP4(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_732])])).

fof(f78,plain,
    ( spl11_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f105,plain,
    ( spl11_10
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f8544,plain,
    ( spl11_538
  <=> r2_hidden(k4_tarski(sK0,sK9(sK2,sK1,sK0,sK5(k5_relat_1(sK2,sK1),sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_538])])).

fof(f9478,plain,
    ( spl11_682
  <=> r2_hidden(k4_tarski(sK9(sK2,sK1,sK0,sK5(k5_relat_1(sK2,sK1),sK0)),sK5(k5_relat_1(sK2,sK1),sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_682])])).

fof(f11966,plain,
    ( sP4(k1_funct_1(sK2,sK0),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_538
    | ~ spl11_682 ),
    inference(forward_demodulation,[],[f11958,f9521])).

fof(f9521,plain,
    ( k1_funct_1(sK2,sK0) = sK9(sK2,sK1,sK0,sK5(k5_relat_1(sK2,sK1),sK0))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_538 ),
    inference(subsumption_resolution,[],[f8733,f106])).

fof(f106,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f8733,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | k1_funct_1(sK2,sK0) = sK9(sK2,sK1,sK0,sK5(k5_relat_1(sK2,sK1),sK0))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_538 ),
    inference(subsumption_resolution,[],[f8732,f75])).

fof(f8732,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0) = sK9(sK2,sK1,sK0,sK5(k5_relat_1(sK2,sK1),sK0))
    | ~ spl11_2
    | ~ spl11_538 ),
    inference(subsumption_resolution,[],[f8727,f79])).

fof(f79,plain,
    ( v1_funct_1(sK2)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f8727,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0) = sK9(sK2,sK1,sK0,sK5(k5_relat_1(sK2,sK1),sK0))
    | ~ spl11_538 ),
    inference(resolution,[],[f8545,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8545,plain,
    ( r2_hidden(k4_tarski(sK0,sK9(sK2,sK1,sK0,sK5(k5_relat_1(sK2,sK1),sK0))),sK2)
    | ~ spl11_538 ),
    inference(avatar_component_clause,[],[f8544])).

fof(f11958,plain,
    ( sP4(sK9(sK2,sK1,sK0,sK5(k5_relat_1(sK2,sK1),sK0)),sK1)
    | ~ spl11_682 ),
    inference(resolution,[],[f9479,f48])).

fof(f9479,plain,
    ( r2_hidden(k4_tarski(sK9(sK2,sK1,sK0,sK5(k5_relat_1(sK2,sK1),sK0)),sK5(k5_relat_1(sK2,sK1),sK0)),sK1)
    | ~ spl11_682 ),
    inference(avatar_component_clause,[],[f9478])).

fof(f10504,plain,
    ( ~ spl11_10
    | ~ spl11_12
    | ~ spl11_18 ),
    inference(avatar_contradiction_clause,[],[f10503])).

fof(f10503,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f159,f10502])).

fof(f10502,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f10494,f118])).

fof(f10494,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f34,f106])).

fof(f34,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
            <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t21_funct_1.p',t21_funct_1)).

fof(f159,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl11_18 ),
    inference(resolution,[],[f145,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f145,plain,
    ( sP4(sK0,k5_relat_1(sK2,sK1))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f144])).

fof(f9890,plain,
    ( spl11_13
    | ~ spl11_732 ),
    inference(avatar_contradiction_clause,[],[f9889])).

fof(f9889,plain,
    ( $false
    | ~ spl11_13
    | ~ spl11_732 ),
    inference(subsumption_resolution,[],[f9888,f138])).

fof(f138,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl11_13
  <=> ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f9888,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ spl11_732 ),
    inference(resolution,[],[f9881,f70])).

fof(f9881,plain,
    ( sP4(k1_funct_1(sK2,sK0),sK1)
    | ~ spl11_732 ),
    inference(avatar_component_clause,[],[f9880])).

fof(f9480,plain,
    ( spl11_682
    | ~ spl11_112 ),
    inference(avatar_split_clause,[],[f693,f685,f9478])).

fof(f685,plain,
    ( spl11_112
  <=> sP8(sK5(k5_relat_1(sK2,sK1),sK0),sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_112])])).

fof(f693,plain,
    ( r2_hidden(k4_tarski(sK9(sK2,sK1,sK0,sK5(k5_relat_1(sK2,sK1),sK0)),sK5(k5_relat_1(sK2,sK1),sK0)),sK1)
    | ~ spl11_112 ),
    inference(resolution,[],[f686,f56])).

fof(f56,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP8(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(sK9(X0,X1,X3,X4),X4),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f686,plain,
    ( sP8(sK5(k5_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ spl11_112 ),
    inference(avatar_component_clause,[],[f685])).

fof(f8731,plain,
    ( spl11_14
    | ~ spl11_538 ),
    inference(avatar_split_clause,[],[f8726,f8544,f122])).

fof(f122,plain,
    ( spl11_14
  <=> sP4(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f8726,plain,
    ( sP4(sK0,sK2)
    | ~ spl11_538 ),
    inference(resolution,[],[f8545,f48])).

fof(f8546,plain,
    ( spl11_538
    | ~ spl11_112 ),
    inference(avatar_split_clause,[],[f692,f685,f8544])).

fof(f692,plain,
    ( r2_hidden(k4_tarski(sK0,sK9(sK2,sK1,sK0,sK5(k5_relat_1(sK2,sK1),sK0))),sK2)
    | ~ spl11_112 ),
    inference(resolution,[],[f686,f55])).

fof(f55,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP8(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,sK9(X0,X1,X3,X4)),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f687,plain,
    ( spl11_112
    | ~ spl11_0
    | ~ spl11_4
    | ~ spl11_20
    | ~ spl11_78 ),
    inference(avatar_split_clause,[],[f443,f407,f148,f82,f74,f685])).

fof(f407,plain,
    ( spl11_78
  <=> r2_hidden(k4_tarski(sK0,sK5(k5_relat_1(sK2,sK1),sK0)),k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_78])])).

fof(f443,plain,
    ( sP8(sK5(k5_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ spl11_0
    | ~ spl11_4
    | ~ spl11_20
    | ~ spl11_78 ),
    inference(subsumption_resolution,[],[f442,f75])).

fof(f442,plain,
    ( sP8(sK5(k5_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl11_4
    | ~ spl11_20
    | ~ spl11_78 ),
    inference(subsumption_resolution,[],[f441,f149])).

fof(f441,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | sP8(sK5(k5_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl11_4
    | ~ spl11_78 ),
    inference(subsumption_resolution,[],[f434,f83])).

fof(f434,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | sP8(sK5(k5_relat_1(sK2,sK1),sK0),sK0,sK1,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl11_78 ),
    inference(resolution,[],[f408,f71])).

fof(f71,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | sP8(X4,X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | sP8(X4,X3,X1,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f408,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(k5_relat_1(sK2,sK1),sK0)),k5_relat_1(sK2,sK1))
    | ~ spl11_78 ),
    inference(avatar_component_clause,[],[f407])).

fof(f409,plain,
    ( spl11_78
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f158,f144,f407])).

fof(f158,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(k5_relat_1(sK2,sK1),sK0)),k5_relat_1(sK2,sK1))
    | ~ spl11_18 ),
    inference(resolution,[],[f145,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f241,plain,
    ( spl11_11
    | ~ spl11_14 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl11_11
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f219,f141])).

fof(f141,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl11_11
  <=> ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f219,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl11_14 ),
    inference(resolution,[],[f123,f70])).

fof(f123,plain,
    ( sP4(sK0,sK2)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f236,plain,
    ( spl11_42
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f213,f105,f78,f74,f234])).

fof(f213,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f212,f75])).

fof(f212,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl11_2
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f208,f79])).

fof(f208,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl11_10 ),
    inference(resolution,[],[f106,f66])).

fof(f150,plain,
    ( spl11_20
    | ~ spl11_0
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f100,f82,f74,f148])).

fof(f100,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl11_0
    | ~ spl11_4 ),
    inference(resolution,[],[f90,f83])).

fof(f90,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(X2)
        | v1_relat_1(k5_relat_1(sK2,X2)) )
    | ~ spl11_0 ),
    inference(resolution,[],[f75,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t21_funct_1.p',dt_k5_relat_1)).

fof(f146,plain,
    ( spl11_18
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f126,f102,f144])).

fof(f102,plain,
    ( spl11_8
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f126,plain,
    ( sP4(sK0,k5_relat_1(sK2,sK1))
    | ~ spl11_8 ),
    inference(resolution,[],[f103,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | sP4(X2,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f103,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f119,plain,
    ( spl11_8
    | spl11_12 ),
    inference(avatar_split_clause,[],[f36,f117,f102])).

fof(f36,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f107,plain,
    ( spl11_8
    | spl11_10 ),
    inference(avatar_split_clause,[],[f35,f105,f102])).

fof(f35,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f40,f86])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f39,f82])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f37,f74])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------

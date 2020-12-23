%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 158 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :    7
%              Number of atoms          :  284 ( 473 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f717,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f70,f74,f89,f97,f106,f118,f123,f149,f173,f215,f325,f404,f460,f645,f716])).

fof(f716,plain,
    ( ~ spl5_4
    | ~ spl5_12
    | ~ spl5_37
    | spl5_47
    | ~ spl5_60 ),
    inference(avatar_contradiction_clause,[],[f715])).

fof(f715,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_37
    | spl5_47
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f519,f702])).

fof(f702,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl5_4
    | ~ spl5_37
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f61,f644,f324])).

fof(f324,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,X0)
        | r1_xboole_0(X2,X1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl5_37
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,X0)
        | r1_xboole_0(X2,X1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f644,plain,
    ( r1_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f642])).

fof(f642,plain,
    ( spl5_60
  <=> r1_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f61,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f519,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl5_12
    | spl5_47 ),
    inference(unit_resulting_resolution,[],[f459,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_12
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f459,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl5_47 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl5_47
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f645,plain,
    ( spl5_60
    | ~ spl5_7
    | spl5_24 ),
    inference(avatar_split_clause,[],[f259,f212,f72,f642])).

fof(f72,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f212,plain,
    ( spl5_24
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f259,plain,
    ( r1_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_7
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f214,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f214,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl5_24 ),
    inference(avatar_component_clause,[],[f212])).

fof(f460,plain,
    ( ~ spl5_47
    | ~ spl5_6
    | spl5_42 ),
    inference(avatar_split_clause,[],[f405,f401,f68,f457])).

fof(f68,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f401,plain,
    ( spl5_42
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f405,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ spl5_6
    | spl5_42 ),
    inference(unit_resulting_resolution,[],[f403,f69])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f403,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_42 ),
    inference(avatar_component_clause,[],[f401])).

fof(f404,plain,
    ( ~ spl5_42
    | ~ spl5_14
    | ~ spl5_19
    | spl5_21 ),
    inference(avatar_split_clause,[],[f174,f170,f147,f103,f401])).

fof(f103,plain,
    ( spl5_14
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f147,plain,
    ( spl5_19
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f170,plain,
    ( spl5_21
  <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f174,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ spl5_14
    | ~ spl5_19
    | spl5_21 ),
    inference(unit_resulting_resolution,[],[f105,f172,f148])).

fof(f148,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,X2) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f147])).

fof(f172,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f170])).

fof(f105,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f325,plain,
    ( spl5_37
    | ~ spl5_10
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f139,f116,f87,f323])).

fof(f87,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f116,plain,
    ( spl5_17
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,X0)
        | r1_xboole_0(X2,X1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_10
    | ~ spl5_17 ),
    inference(superposition,[],[f117,f88])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f116])).

fof(f215,plain,
    ( ~ spl5_24
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f142,f121,f103,f44,f212])).

fof(f44,plain,
    ( spl5_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f121,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f142,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f105,f46,f122])).

fof(f122,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f121])).

fof(f46,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f173,plain,
    ( ~ spl5_21
    | spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f75,f68,f54,f170])).

fof(f54,plain,
    ( spl5_3
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f75,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl5_3
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f56,f69])).

fof(f56,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f149,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f38,f147])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f123,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f32,f121])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f118,plain,(
    spl5_17 ),
    inference(avatar_split_clause,[],[f42,f116])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f106,plain,
    ( spl5_14
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f76,f68,f49,f103])).

fof(f49,plain,
    ( spl5_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f76,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f51,f69])).

fof(f51,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f97,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f89,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f35,f87])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f74,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f33,f72])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f70,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f62,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f57,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f27,f49])).

fof(f27,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f26,f44])).

fof(f26,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:56:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (29845)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.44  % (29845)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f717,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f70,f74,f89,f97,f106,f118,f123,f149,f173,f215,f325,f404,f460,f645,f716])).
% 0.21/0.44  fof(f716,plain,(
% 0.21/0.44    ~spl5_4 | ~spl5_12 | ~spl5_37 | spl5_47 | ~spl5_60),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f715])).
% 0.21/0.44  fof(f715,plain,(
% 0.21/0.44    $false | (~spl5_4 | ~spl5_12 | ~spl5_37 | spl5_47 | ~spl5_60)),
% 0.21/0.44    inference(subsumption_resolution,[],[f519,f702])).
% 0.21/0.44  fof(f702,plain,(
% 0.21/0.44    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | (~spl5_4 | ~spl5_37 | ~spl5_60)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f61,f644,f324])).
% 0.21/0.44  fof(f324,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1)) ) | ~spl5_37),
% 0.21/0.44    inference(avatar_component_clause,[],[f323])).
% 0.21/0.44  fof(f323,plain,(
% 0.21/0.44    spl5_37 <=> ! [X1,X0,X2] : (~r1_tarski(X2,X0) | r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.44  fof(f644,plain,(
% 0.21/0.44    r1_xboole_0(k1_tarski(sK3),sK1) | ~spl5_60),
% 0.21/0.44    inference(avatar_component_clause,[],[f642])).
% 0.21/0.44  fof(f642,plain,(
% 0.21/0.44    spl5_60 <=> r1_xboole_0(k1_tarski(sK3),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl5_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f59])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    spl5_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.44  fof(f519,plain,(
% 0.21/0.44    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | (~spl5_12 | spl5_47)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f459,f96])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl5_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f95])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    spl5_12 <=> ! [X1,X0] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.44  fof(f459,plain,(
% 0.21/0.44    ~r1_xboole_0(sK0,sK1) | spl5_47),
% 0.21/0.44    inference(avatar_component_clause,[],[f457])).
% 0.21/0.44  fof(f457,plain,(
% 0.21/0.44    spl5_47 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 0.21/0.44  fof(f645,plain,(
% 0.21/0.44    spl5_60 | ~spl5_7 | spl5_24),
% 0.21/0.44    inference(avatar_split_clause,[],[f259,f212,f72,f642])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl5_7 <=> ! [X1,X0] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.44  fof(f212,plain,(
% 0.21/0.44    spl5_24 <=> r2_hidden(sK3,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.44  fof(f259,plain,(
% 0.21/0.44    r1_xboole_0(k1_tarski(sK3),sK1) | (~spl5_7 | spl5_24)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f214,f73])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl5_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f72])).
% 0.21/0.44  fof(f214,plain,(
% 0.21/0.44    ~r2_hidden(sK3,sK1) | spl5_24),
% 0.21/0.44    inference(avatar_component_clause,[],[f212])).
% 0.21/0.44  fof(f460,plain,(
% 0.21/0.44    ~spl5_47 | ~spl5_6 | spl5_42),
% 0.21/0.44    inference(avatar_split_clause,[],[f405,f401,f68,f457])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    spl5_6 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.44  fof(f401,plain,(
% 0.21/0.44    spl5_42 <=> r1_xboole_0(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.21/0.44  fof(f405,plain,(
% 0.21/0.44    ~r1_xboole_0(sK0,sK1) | (~spl5_6 | spl5_42)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f403,f69])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl5_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f68])).
% 0.21/0.44  fof(f403,plain,(
% 0.21/0.44    ~r1_xboole_0(sK1,sK0) | spl5_42),
% 0.21/0.44    inference(avatar_component_clause,[],[f401])).
% 0.21/0.44  fof(f404,plain,(
% 0.21/0.44    ~spl5_42 | ~spl5_14 | ~spl5_19 | spl5_21),
% 0.21/0.44    inference(avatar_split_clause,[],[f174,f170,f147,f103,f401])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    spl5_14 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    spl5_19 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.44  fof(f170,plain,(
% 0.21/0.44    spl5_21 <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.44  fof(f174,plain,(
% 0.21/0.44    ~r1_xboole_0(sK1,sK0) | (~spl5_14 | ~spl5_19 | spl5_21)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f105,f172,f148])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) ) | ~spl5_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f147])).
% 0.21/0.44  fof(f172,plain,(
% 0.21/0.44    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | spl5_21),
% 0.21/0.44    inference(avatar_component_clause,[],[f170])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    r1_xboole_0(sK1,sK2) | ~spl5_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f103])).
% 0.21/0.44  fof(f325,plain,(
% 0.21/0.44    spl5_37 | ~spl5_10 | ~spl5_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f139,f116,f87,f323])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    spl5_10 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    spl5_17 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1)) ) | (~spl5_10 | ~spl5_17)),
% 0.21/0.44    inference(superposition,[],[f117,f88])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl5_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f87])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) ) | ~spl5_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f116])).
% 0.21/0.44  fof(f215,plain,(
% 0.21/0.44    ~spl5_24 | ~spl5_1 | ~spl5_14 | ~spl5_18),
% 0.21/0.44    inference(avatar_split_clause,[],[f142,f121,f103,f44,f212])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    spl5_1 <=> r2_hidden(sK3,sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    spl5_18 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.44  fof(f142,plain,(
% 0.21/0.44    ~r2_hidden(sK3,sK1) | (~spl5_1 | ~spl5_14 | ~spl5_18)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f105,f46,f122])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) ) | ~spl5_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f121])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    r2_hidden(sK3,sK2) | ~spl5_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f44])).
% 0.21/0.44  fof(f173,plain,(
% 0.21/0.44    ~spl5_21 | spl5_3 | ~spl5_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f75,f68,f54,f170])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    spl5_3 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | (spl5_3 | ~spl5_6)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f56,f69])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f54])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    spl5_19),
% 0.21/0.44    inference(avatar_split_clause,[],[f38,f147])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    spl5_18),
% 0.21/0.44    inference(avatar_split_clause,[],[f32,f121])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(rectify,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    spl5_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f42,f116])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    spl5_14 | ~spl5_2 | ~spl5_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f76,f68,f49,f103])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl5_2 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    r1_xboole_0(sK1,sK2) | (~spl5_2 | ~spl5_6)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f51,f69])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    r1_xboole_0(sK2,sK1) | ~spl5_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f49])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    spl5_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f37,f95])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    spl5_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f35,f87])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl5_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f33,f72])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    spl5_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f34,f68])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    spl5_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f25,f59])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.44    inference(negated_conjecture,[],[f9])).
% 0.21/0.44  fof(f9,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ~spl5_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f28,f54])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    spl5_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f27,f49])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    r1_xboole_0(sK2,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl5_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f44])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    r2_hidden(sK3,sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (29845)------------------------------
% 0.21/0.44  % (29845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (29845)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (29845)Memory used [KB]: 6524
% 0.21/0.44  % (29845)Time elapsed: 0.038 s
% 0.21/0.44  % (29845)------------------------------
% 0.21/0.44  % (29845)------------------------------
% 0.21/0.44  % (29839)Success in time 0.085 s
%------------------------------------------------------------------------------

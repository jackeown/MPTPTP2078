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
% DateTime   : Thu Dec  3 13:05:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 338 expanded)
%              Number of leaves         :   35 ( 145 expanded)
%              Depth                    :   10
%              Number of atoms          :  535 (1821 expanded)
%              Number of equality atoms :   98 ( 439 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f357,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f89,f94,f99,f104,f144,f150,f164,f165,f170,f175,f205,f228,f279,f321,f332,f345,f351,f356])).

fof(f356,plain,
    ( sK2 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | sK3 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | sK2 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f351,plain,
    ( spl7_31
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | spl7_21 ),
    inference(avatar_split_clause,[],[f346,f241,f101,f96,f91,f77,f72,f63,f348])).

fof(f348,plain,
    ( spl7_31
  <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f63,plain,
    ( spl7_1
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f72,plain,
    ( spl7_3
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f77,plain,
    ( spl7_4
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f91,plain,
    ( spl7_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f96,plain,
    ( spl7_8
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f101,plain,
    ( spl7_9
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f241,plain,
    ( spl7_21
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f346,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | spl7_21 ),
    inference(forward_demodulation,[],[f334,f74])).

fof(f74,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f334,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | spl7_21 ),
    inference(unit_resulting_resolution,[],[f103,f79,f64,f242,f98,f93,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f93,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f98,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f242,plain,
    ( k1_xboole_0 != sK0
    | spl7_21 ),
    inference(avatar_component_clause,[],[f241])).

fof(f64,plain,
    ( v2_funct_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f79,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f103,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f345,plain,
    ( spl7_30
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | spl7_21 ),
    inference(avatar_split_clause,[],[f335,f241,f101,f96,f91,f82,f63,f342])).

fof(f342,plain,
    ( spl7_30
  <=> sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f82,plain,
    ( spl7_5
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f335,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | spl7_21 ),
    inference(unit_resulting_resolution,[],[f103,f84,f64,f242,f98,f93,f61])).

fof(f84,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f332,plain,
    ( spl7_16
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f330,f146,f110,f179])).

fof(f179,plain,
    ( spl7_16
  <=> r1_tarski(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f110,plain,
    ( spl7_10
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f146,plain,
    ( spl7_13
  <=> v4_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f330,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f111,f148,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f148,plain,
    ( v4_relat_1(sK1,sK0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f111,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f321,plain,
    ( ~ spl7_21
    | spl7_23 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl7_21
    | spl7_23 ),
    inference(subsumption_resolution,[],[f289,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f289,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_21
    | spl7_23 ),
    inference(backward_demodulation,[],[f264,f243])).

fof(f243,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f241])).

fof(f264,plain,
    ( ~ v1_xboole_0(sK0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl7_23
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f279,plain,
    ( ~ spl7_23
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f275,f82,f262])).

fof(f275,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl7_5 ),
    inference(resolution,[],[f84,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f228,plain,
    ( ~ spl7_18
    | ~ spl7_6
    | ~ spl7_11
    | spl7_12
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f219,f179,f172,f119,f114,f87,f202])).

fof(f202,plain,
    ( spl7_18
  <=> r2_hidden(sK5(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f87,plain,
    ( spl7_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f114,plain,
    ( spl7_11
  <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f119,plain,
    ( spl7_12
  <=> sK4(sK1) = sK5(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f172,plain,
    ( spl7_15
  <=> r2_hidden(sK4(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f219,plain,
    ( ~ r2_hidden(sK5(sK1),sK0)
    | ~ spl7_6
    | ~ spl7_11
    | spl7_12
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f181,f121,f116,f174,f152])).

fof(f152,plain,
    ( ! [X4,X2,X3] :
        ( ~ r2_hidden(X3,sK0)
        | X2 = X3
        | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
        | ~ r2_hidden(X2,X4)
        | ~ r1_tarski(X4,sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f88,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f88,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK0)
        | X4 = X5
        | ~ r2_hidden(X5,sK0)
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f174,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f172])).

fof(f116,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f121,plain,
    ( sK4(sK1) != sK5(sK1)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f181,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f205,plain,
    ( spl7_18
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f189,f179,f167,f202])).

fof(f167,plain,
    ( spl7_14
  <=> r2_hidden(sK5(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f189,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f181,f169,f56])).

fof(f169,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f175,plain,
    ( spl7_15
    | spl7_1
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f153,f110,f101,f63,f172])).

fof(f153,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | spl7_1
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f65,f103,f111,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f65,plain,
    ( ~ v2_funct_1(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f170,plain,
    ( spl7_14
    | spl7_1
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f154,f110,f101,f63,f167])).

fof(f154,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | spl7_1
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f65,f103,f111,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f165,plain,
    ( spl7_11
    | spl7_1
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f155,f110,f101,f63,f114])).

fof(f155,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | spl7_1
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f65,f103,f111,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f164,plain,
    ( ~ spl7_12
    | spl7_1
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f156,f110,f101,f63,f119])).

fof(f156,plain,
    ( sK4(sK1) != sK5(sK1)
    | spl7_1
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f65,f103,f111,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK4(X0) != sK5(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f150,plain,
    ( spl7_13
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f132,f91,f146])).

fof(f132,plain,
    ( v4_relat_1(sK1,sK0)
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f93,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f144,plain,
    ( spl7_10
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f133,f91,f110])).

fof(f133,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f93,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f104,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f39,f101])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( sK2 != sK3
        & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,sK0)
        & r2_hidden(sK2,sK0) )
      | ~ v2_funct_1(sK1) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
          | ~ r2_hidden(X5,sK0)
          | ~ r2_hidden(X4,sK0) )
      | v2_funct_1(sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
            & r2_hidden(X3,sK0)
            & r2_hidden(X2,sK0) )
        | ~ v2_funct_1(sK1) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
            | ~ r2_hidden(X5,sK0)
            | ~ r2_hidden(X4,sK0) )
        | v2_funct_1(sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f99,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f40,f96])).

fof(f40,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f41,f91])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f89,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f42,f87,f63])).

fof(f42,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f43,f82,f63])).

fof(f43,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f44,f77,f63])).

fof(f44,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f45,f72,f63])).

fof(f45,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f46,f67,f63])).

fof(f67,plain,
    ( spl7_2
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f46,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:45:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (14956)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.49  % (14980)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.50  % (14969)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (14972)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.51  % (14961)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (14980)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f357,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f89,f94,f99,f104,f144,f150,f164,f165,f170,f175,f205,f228,f279,f321,f332,f345,f351,f356])).
% 0.22/0.51  fof(f356,plain,(
% 0.22/0.51    sK2 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | sK3 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | sK2 = sK3),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f351,plain,(
% 0.22/0.51    spl7_31 | ~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_9 | spl7_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f346,f241,f101,f96,f91,f77,f72,f63,f348])).
% 0.22/0.51  fof(f348,plain,(
% 0.22/0.51    spl7_31 <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    spl7_1 <=> v2_funct_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    spl7_3 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    spl7_4 <=> r2_hidden(sK3,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl7_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    spl7_8 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl7_9 <=> v1_funct_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    spl7_21 <=> k1_xboole_0 = sK0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.51  fof(f346,plain,(
% 0.22/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_9 | spl7_21)),
% 0.22/0.51    inference(forward_demodulation,[],[f334,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl7_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f72])).
% 0.22/0.51  fof(f334,plain,(
% 0.22/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl7_1 | ~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_9 | spl7_21)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f103,f79,f64,f242,f98,f93,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f91])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    v1_funct_2(sK1,sK0,sK0) | ~spl7_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f96])).
% 0.22/0.51  fof(f242,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 | spl7_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f241])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    v2_funct_1(sK1) | ~spl7_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f63])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    r2_hidden(sK3,sK0) | ~spl7_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f77])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    v1_funct_1(sK1) | ~spl7_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f101])).
% 0.22/0.51  fof(f345,plain,(
% 0.22/0.51    spl7_30 | ~spl7_1 | ~spl7_5 | ~spl7_7 | ~spl7_8 | ~spl7_9 | spl7_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f335,f241,f101,f96,f91,f82,f63,f342])).
% 0.22/0.51  fof(f342,plain,(
% 0.22/0.51    spl7_30 <=> sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    spl7_5 <=> r2_hidden(sK2,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.51  fof(f335,plain,(
% 0.22/0.51    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_1 | ~spl7_5 | ~spl7_7 | ~spl7_8 | ~spl7_9 | spl7_21)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f103,f84,f64,f242,f98,f93,f61])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    r2_hidden(sK2,sK0) | ~spl7_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f82])).
% 0.22/0.51  fof(f332,plain,(
% 0.22/0.51    spl7_16 | ~spl7_10 | ~spl7_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f330,f146,f110,f179])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    spl7_16 <=> r1_tarski(k1_relat_1(sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    spl7_10 <=> v1_relat_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    spl7_13 <=> v4_relat_1(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    r1_tarski(k1_relat_1(sK1),sK0) | (~spl7_10 | ~spl7_13)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f111,f148,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    v4_relat_1(sK1,sK0) | ~spl7_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f146])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    v1_relat_1(sK1) | ~spl7_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f110])).
% 0.22/0.51  fof(f321,plain,(
% 0.22/0.51    ~spl7_21 | spl7_23),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f320])).
% 0.22/0.51  fof(f320,plain,(
% 0.22/0.51    $false | (~spl7_21 | spl7_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f289,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    ~v1_xboole_0(k1_xboole_0) | (~spl7_21 | spl7_23)),
% 0.22/0.51    inference(backward_demodulation,[],[f264,f243])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | ~spl7_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f241])).
% 0.22/0.51  fof(f264,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0) | spl7_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f262])).
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    spl7_23 <=> v1_xboole_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    ~spl7_23 | ~spl7_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f275,f82,f262])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0) | ~spl7_5),
% 0.22/0.51    inference(resolution,[],[f84,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    ~spl7_18 | ~spl7_6 | ~spl7_11 | spl7_12 | ~spl7_15 | ~spl7_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f219,f179,f172,f119,f114,f87,f202])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    spl7_18 <=> r2_hidden(sK5(sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl7_6 <=> ! [X5,X4] : (X4 = X5 | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK0) | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    spl7_11 <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl7_12 <=> sK4(sK1) = sK5(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    spl7_15 <=> r2_hidden(sK4(sK1),k1_relat_1(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    ~r2_hidden(sK5(sK1),sK0) | (~spl7_6 | ~spl7_11 | spl7_12 | ~spl7_15 | ~spl7_16)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f181,f121,f116,f174,f152])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ( ! [X4,X2,X3] : (~r2_hidden(X3,sK0) | X2 = X3 | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | ~r2_hidden(X2,X4) | ~r1_tarski(X4,sK0)) ) | ~spl7_6),
% 0.22/0.51    inference(resolution,[],[f88,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~r2_hidden(X4,sK0) | X4 = X5 | ~r2_hidden(X5,sK0) | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)) ) | ~spl7_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f87])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | ~spl7_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f172])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~spl7_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f114])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    sK4(sK1) != sK5(sK1) | spl7_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f119])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    r1_tarski(k1_relat_1(sK1),sK0) | ~spl7_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f179])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    spl7_18 | ~spl7_14 | ~spl7_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f189,f179,f167,f202])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    spl7_14 <=> r2_hidden(sK5(sK1),k1_relat_1(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    r2_hidden(sK5(sK1),sK0) | (~spl7_14 | ~spl7_16)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f181,f169,f56])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | ~spl7_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f167])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    spl7_15 | spl7_1 | ~spl7_9 | ~spl7_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f153,f110,f101,f63,f172])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | (spl7_1 | ~spl7_9 | ~spl7_10)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f65,f103,f111,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK4(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(rectify,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ~v2_funct_1(sK1) | spl7_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f63])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    spl7_14 | spl7_1 | ~spl7_9 | ~spl7_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f154,f110,f101,f63,f167])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | (spl7_1 | ~spl7_9 | ~spl7_10)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f65,f103,f111,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK5(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    spl7_11 | spl7_1 | ~spl7_9 | ~spl7_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f155,f110,f101,f63,f114])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | (spl7_1 | ~spl7_9 | ~spl7_10)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f65,f103,f111,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    ~spl7_12 | spl7_1 | ~spl7_9 | ~spl7_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f156,f110,f101,f63,f119])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    sK4(sK1) != sK5(sK1) | (spl7_1 | ~spl7_9 | ~spl7_10)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f65,f103,f111,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0] : (v2_funct_1(X0) | sK4(X0) != sK5(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    spl7_13 | ~spl7_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f132,f91,f146])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    v4_relat_1(sK1,sK0) | ~spl7_7),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f93,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    spl7_10 | ~spl7_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f133,f91,f110])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    v1_relat_1(sK1) | ~spl7_7),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f93,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    spl7_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f39,f101])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    v1_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ((sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) | ~v2_funct_1(sK1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f28,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) | ~v2_funct_1(sK1)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.51    inference(rectify,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.51    inference(negated_conjecture,[],[f9])).
% 0.22/0.51  fof(f9,conjecture,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    spl7_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f40,f96])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    spl7_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f41,f91])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl7_1 | spl7_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f42,f87,f63])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0) | v2_funct_1(sK1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ~spl7_1 | spl7_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f43,f82,f63])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ~spl7_1 | spl7_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f44,f77,f63])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ~spl7_1 | spl7_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f45,f72,f63])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ~spl7_1 | ~spl7_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f46,f67,f63])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    spl7_2 <=> sK2 = sK3),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    sK2 != sK3 | ~v2_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (14980)------------------------------
% 0.22/0.51  % (14980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14980)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (14980)Memory used [KB]: 6396
% 0.22/0.51  % (14980)Time elapsed: 0.117 s
% 0.22/0.51  % (14980)------------------------------
% 0.22/0.51  % (14980)------------------------------
% 0.22/0.51  % (14954)Success in time 0.149 s
%------------------------------------------------------------------------------

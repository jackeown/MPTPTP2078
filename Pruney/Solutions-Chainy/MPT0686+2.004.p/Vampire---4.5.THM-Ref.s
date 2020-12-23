%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 155 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  242 ( 438 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f86,f105,f126,f136,f180,f240])).

fof(f240,plain,(
    ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f230,f36])).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f230,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),X0),k1_xboole_0)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f179,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f179,plain,
    ( r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_xboole_0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl5_12
  <=> r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f180,plain,
    ( spl5_12
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f171,f132,f123,f177])).

fof(f123,plain,
    ( spl5_8
  <=> r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f132,plain,
    ( spl5_9
  <=> r1_tarski(k10_relat_1(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f171,plain,
    ( r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f125,f134,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f134,plain,
    ( r1_tarski(k10_relat_1(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_xboole_0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f132])).

fof(f125,plain,
    ( r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,k1_setfam_1(k2_tarski(sK1,sK2))))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f136,plain,
    ( spl5_9
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f130,f83,f67,f57,f132])).

fof(f57,plain,
    ( spl5_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f67,plain,
    ( spl5_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f83,plain,
    ( spl5_6
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f130,plain,
    ( r1_tarski(k10_relat_1(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(resolution,[],[f95,f107])).

fof(f107,plain,
    ( ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),X0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f87,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_setfam_1(k2_tarski(sK1,sK2)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f59,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f59,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f95,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k1_xboole_0)
        | r1_tarski(k10_relat_1(sK0,X2),k1_xboole_0) )
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f92,f69])).

fof(f69,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f92,plain,
    ( ! [X2] :
        ( r1_tarski(k10_relat_1(sK0,X2),k1_xboole_0)
        | ~ r1_tarski(X2,k1_xboole_0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_6 ),
    inference(superposition,[],[f45,f85])).

fof(f85,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f126,plain,
    ( spl5_8
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f121,f102,f73,f123])).

fof(f73,plain,
    ( spl5_5
  <=> ! [X1,X0] : k10_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f102,plain,
    ( spl5_7
  <=> r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_setfam_1(k2_tarski(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f121,plain,
    ( r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,k1_setfam_1(k2_tarski(sK1,sK2))))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f104,f74])).

fof(f74,plain,
    ( ! [X0,X1] : k10_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f104,plain,
    ( r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_setfam_1(k2_tarski(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f105,plain,
    ( spl5_7
    | spl5_1 ),
    inference(avatar_split_clause,[],[f97,f52,f102])).

fof(f52,plain,
    ( spl5_1
  <=> r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f97,plain,
    ( r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_setfam_1(k2_tarski(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f54,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f86,plain,
    ( spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f77,f67,f83])).

fof(f77,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f36,f69,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f75,plain,
    ( ~ spl5_4
    | spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f71,f62,f73,f67])).

fof(f62,plain,
    ( spl5_3
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f64,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f46,f37,f37])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

fof(f64,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f70,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f32,f67])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
            & r1_xboole_0(X1,X2) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2,X1] :
        ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
        & r1_xboole_0(X1,X2) )
   => ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
      & r1_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_xboole_0(X1,X2)
           => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_xboole_0(X1,X2)
         => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).

fof(f65,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f33,f62])).

fof(f33,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f34,f57])).

fof(f34,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f35,f52])).

fof(f35,plain,(
    ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (14225)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (14217)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (14240)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (14235)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (14225)Refutation not found, incomplete strategy% (14225)------------------------------
% 0.21/0.51  % (14225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14243)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (14225)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14225)Memory used [KB]: 10618
% 0.21/0.52  % (14225)Time elapsed: 0.095 s
% 0.21/0.52  % (14225)------------------------------
% 0.21/0.52  % (14225)------------------------------
% 0.21/0.52  % (14224)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (14219)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (14240)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f86,f105,f126,f136,f180,f240])).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    ~spl5_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f239])).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    $false | ~spl5_12),
% 0.21/0.53    inference(subsumption_resolution,[],[f230,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_xboole_0(k2_tarski(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),X0),k1_xboole_0)) ) | ~spl5_12),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f179,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_xboole_0) | ~spl5_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f177])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    spl5_12 <=> r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    spl5_12 | ~spl5_8 | ~spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f171,f132,f123,f177])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    spl5_8 <=> r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,k1_setfam_1(k2_tarski(sK1,sK2))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    spl5_9 <=> r1_tarski(k10_relat_1(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_xboole_0) | (~spl5_8 | ~spl5_9)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f125,f134,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    r1_tarski(k10_relat_1(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_xboole_0) | ~spl5_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f132])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))) | ~spl5_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f123])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    spl5_9 | ~spl5_2 | ~spl5_4 | ~spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f130,f83,f67,f57,f132])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    spl5_2 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    spl5_4 <=> v1_relat_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl5_6 <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    r1_tarski(k10_relat_1(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_xboole_0) | (~spl5_2 | ~spl5_4 | ~spl5_6)),
% 0.21/0.53    inference(resolution,[],[f95,f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),X0)) ) | ~spl5_2),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f87,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(sK1,sK2)))) ) | ~spl5_2),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f59,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f39,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    r1_xboole_0(sK1,sK2) | ~spl5_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f57])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | r1_tarski(k10_relat_1(sK0,X2),k1_xboole_0)) ) | (~spl5_4 | ~spl5_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f92,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    v1_relat_1(sK0) | ~spl5_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f67])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X2] : (r1_tarski(k10_relat_1(sK0,X2),k1_xboole_0) | ~r1_tarski(X2,k1_xboole_0) | ~v1_relat_1(sK0)) ) | ~spl5_6),
% 0.21/0.53    inference(superposition,[],[f45,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) | ~spl5_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f83])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    spl5_8 | ~spl5_5 | ~spl5_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f121,f102,f73,f123])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl5_5 <=> ! [X1,X0] : k10_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    spl5_7 <=> r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_setfam_1(k2_tarski(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))) | (~spl5_5 | ~spl5_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f104,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k10_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)))) ) | ~spl5_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f73])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_setfam_1(k2_tarski(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)))) | ~spl5_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f102])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl5_7 | spl5_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f97,f52,f102])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    spl5_1 <=> r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    r2_hidden(sK3(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)),k1_setfam_1(k2_tarski(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)))) | spl5_1),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f54,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f38,f37])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | spl5_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f52])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl5_6 | ~spl5_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f77,f67,f83])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) | ~spl5_4),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f36,f69,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ~spl5_4 | spl5_5 | ~spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f71,f62,f73,f67])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    spl5_3 <=> v1_funct_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k10_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) | ~v1_relat_1(sK0)) ) | ~spl5_3),
% 0.21/0.53    inference(resolution,[],[f64,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k10_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f46,f37,f37])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    v1_funct_1(sK0) | ~spl5_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f62])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    spl5_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f32,f67])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    v1_relat_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    (~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) & r1_xboole_0(sK1,sK2)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2)) & r1_xboole_0(X1,X2)) => (~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) & r1_xboole_0(sK1,sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f62])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v1_funct_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    spl5_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f57])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    r1_xboole_0(sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ~spl5_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f52])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14240)------------------------------
% 0.21/0.53  % (14240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14240)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14240)Memory used [KB]: 6396
% 0.21/0.53  % (14240)Time elapsed: 0.106 s
% 0.21/0.53  % (14240)------------------------------
% 0.21/0.53  % (14240)------------------------------
% 0.21/0.53  % (14237)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (14214)Success in time 0.168 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 143 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  223 ( 418 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f831,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f51,f55,f59,f63,f67,f71,f84,f300,f307,f322,f465,f699,f739,f802,f830])).

fof(f830,plain,
    ( spl3_1
    | ~ spl3_60
    | ~ spl3_105 ),
    inference(avatar_contradiction_clause,[],[f829])).

fof(f829,plain,
    ( $false
    | spl3_1
    | ~ spl3_60
    | ~ spl3_105 ),
    inference(subsumption_resolution,[],[f827,f30])).

fof(f30,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f827,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,sK1))
    | ~ spl3_60
    | ~ spl3_105 ),
    inference(resolution,[],[f801,f464])).

fof(f464,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X0)
        | r1_tarski(sK0,X0) )
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl3_60
  <=> ! [X0] :
        ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X0)
        | r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f801,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1))
    | ~ spl3_105 ),
    inference(avatar_component_clause,[],[f799])).

fof(f799,plain,
    ( spl3_105
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_105])])).

fof(f802,plain,
    ( spl3_105
    | ~ spl3_12
    | ~ spl3_92 ),
    inference(avatar_split_clause,[],[f785,f737,f81,f799])).

fof(f81,plain,
    ( spl3_12
  <=> sK1 = k2_xboole_0(k9_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f737,plain,
    ( spl3_92
  <=> ! [X11,X12] : r1_tarski(k10_relat_1(sK2,X11),k10_relat_1(sK2,k2_xboole_0(X11,X12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).

fof(f785,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1))
    | ~ spl3_12
    | ~ spl3_92 ),
    inference(superposition,[],[f738,f83])).

fof(f83,plain,
    ( sK1 = k2_xboole_0(k9_relat_1(sK2,sK0),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f738,plain,
    ( ! [X12,X11] : r1_tarski(k10_relat_1(sK2,X11),k10_relat_1(sK2,k2_xboole_0(X11,X12)))
    | ~ spl3_92 ),
    inference(avatar_component_clause,[],[f737])).

fof(f739,plain,
    ( spl3_92
    | ~ spl3_6
    | ~ spl3_86 ),
    inference(avatar_split_clause,[],[f705,f697,f53,f737])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f697,plain,
    ( spl3_86
  <=> ! [X1,X0] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f705,plain,
    ( ! [X12,X11] : r1_tarski(k10_relat_1(sK2,X11),k10_relat_1(sK2,k2_xboole_0(X11,X12)))
    | ~ spl3_6
    | ~ spl3_86 ),
    inference(superposition,[],[f54,f698])).

fof(f698,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_86 ),
    inference(avatar_component_clause,[],[f697])).

fof(f54,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f699,plain,
    ( spl3_86
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f695,f65,f48,f697])).

fof(f48,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f65,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f695,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f66,f50])).

fof(f50,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f465,plain,
    ( spl3_60
    | ~ spl3_10
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f454,f319,f69,f463])).

fof(f69,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f319,plain,
    ( spl3_48
  <=> k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = k2_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f454,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X0)
        | r1_tarski(sK0,X0) )
    | ~ spl3_10
    | ~ spl3_48 ),
    inference(superposition,[],[f70,f321])).

fof(f321,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = k2_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f319])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f322,plain,
    ( spl3_48
    | ~ spl3_8
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f317,f304,f61,f319])).

fof(f61,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f304,plain,
    ( spl3_45
  <=> r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f317,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = k2_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ spl3_8
    | ~ spl3_45 ),
    inference(resolution,[],[f306,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f306,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f304])).

fof(f307,plain,
    ( spl3_45
    | ~ spl3_3
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f301,f298,f38,f304])).

fof(f38,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f298,plain,
    ( spl3_44
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f301,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ spl3_3
    | ~ spl3_44 ),
    inference(resolution,[],[f299,f40])).

fof(f40,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) )
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f298])).

fof(f300,plain,
    ( spl3_44
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f296,f57,f48,f298])).

fof(f57,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) )
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f58,f50])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f84,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f73,f61,f33,f81])).

fof(f33,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f73,plain,
    ( sK1 = k2_xboole_0(k9_relat_1(sK2,sK0),sK1)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f62,f35])).

fof(f35,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f71,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f26,f69])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f67,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f63,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f61])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f59,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f55,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f51,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f17,f48])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
    & r1_tarski(k9_relat_1(sK2,sK0),sK1)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
        & r1_tarski(k9_relat_1(X2,X0),X1)
        & r1_tarski(X0,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
      & r1_tarski(k9_relat_1(sK2,sK0),sK1)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
            & r1_tarski(X0,k1_relat_1(X2)) )
         => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f41,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f28])).

fof(f21,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:59:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.41  % (14137)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (14142)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.42  % (14135)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.43  % (14137)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f831,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f31,f36,f41,f51,f55,f59,f63,f67,f71,f84,f300,f307,f322,f465,f699,f739,f802,f830])).
% 0.22/0.43  fof(f830,plain,(
% 0.22/0.43    spl3_1 | ~spl3_60 | ~spl3_105),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f829])).
% 0.22/0.43  fof(f829,plain,(
% 0.22/0.43    $false | (spl3_1 | ~spl3_60 | ~spl3_105)),
% 0.22/0.43    inference(subsumption_resolution,[],[f827,f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ~r1_tarski(sK0,k10_relat_1(sK2,sK1)) | spl3_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    spl3_1 <=> r1_tarski(sK0,k10_relat_1(sK2,sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.43  fof(f827,plain,(
% 0.22/0.43    r1_tarski(sK0,k10_relat_1(sK2,sK1)) | (~spl3_60 | ~spl3_105)),
% 0.22/0.43    inference(resolution,[],[f801,f464])).
% 0.22/0.43  fof(f464,plain,(
% 0.22/0.43    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X0) | r1_tarski(sK0,X0)) ) | ~spl3_60),
% 0.22/0.43    inference(avatar_component_clause,[],[f463])).
% 0.22/0.43  fof(f463,plain,(
% 0.22/0.43    spl3_60 <=> ! [X0] : (~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X0) | r1_tarski(sK0,X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.22/0.43  fof(f801,plain,(
% 0.22/0.43    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1)) | ~spl3_105),
% 0.22/0.43    inference(avatar_component_clause,[],[f799])).
% 0.22/0.43  fof(f799,plain,(
% 0.22/0.43    spl3_105 <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_105])])).
% 0.22/0.43  fof(f802,plain,(
% 0.22/0.43    spl3_105 | ~spl3_12 | ~spl3_92),
% 0.22/0.43    inference(avatar_split_clause,[],[f785,f737,f81,f799])).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    spl3_12 <=> sK1 = k2_xboole_0(k9_relat_1(sK2,sK0),sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.43  fof(f737,plain,(
% 0.22/0.43    spl3_92 <=> ! [X11,X12] : r1_tarski(k10_relat_1(sK2,X11),k10_relat_1(sK2,k2_xboole_0(X11,X12)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).
% 0.22/0.43  fof(f785,plain,(
% 0.22/0.43    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1)) | (~spl3_12 | ~spl3_92)),
% 0.22/0.43    inference(superposition,[],[f738,f83])).
% 0.22/0.43  fof(f83,plain,(
% 0.22/0.43    sK1 = k2_xboole_0(k9_relat_1(sK2,sK0),sK1) | ~spl3_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f81])).
% 0.22/0.43  fof(f738,plain,(
% 0.22/0.43    ( ! [X12,X11] : (r1_tarski(k10_relat_1(sK2,X11),k10_relat_1(sK2,k2_xboole_0(X11,X12)))) ) | ~spl3_92),
% 0.22/0.43    inference(avatar_component_clause,[],[f737])).
% 0.22/0.43  fof(f739,plain,(
% 0.22/0.43    spl3_92 | ~spl3_6 | ~spl3_86),
% 0.22/0.43    inference(avatar_split_clause,[],[f705,f697,f53,f737])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    spl3_6 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.43  fof(f697,plain,(
% 0.22/0.43    spl3_86 <=> ! [X1,X0] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 0.22/0.43  fof(f705,plain,(
% 0.22/0.43    ( ! [X12,X11] : (r1_tarski(k10_relat_1(sK2,X11),k10_relat_1(sK2,k2_xboole_0(X11,X12)))) ) | (~spl3_6 | ~spl3_86)),
% 0.22/0.43    inference(superposition,[],[f54,f698])).
% 0.22/0.43  fof(f698,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | ~spl3_86),
% 0.22/0.43    inference(avatar_component_clause,[],[f697])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f53])).
% 0.22/0.43  fof(f699,plain,(
% 0.22/0.43    spl3_86 | ~spl3_5 | ~spl3_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f695,f65,f48,f697])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl3_5 <=> v1_relat_1(sK2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    spl3_9 <=> ! [X1,X0,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.43  fof(f695,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | (~spl3_5 | ~spl3_9)),
% 0.22/0.43    inference(resolution,[],[f66,f50])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    v1_relat_1(sK2) | ~spl3_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f48])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) | ~spl3_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f65])).
% 0.22/0.43  fof(f465,plain,(
% 0.22/0.43    spl3_60 | ~spl3_10 | ~spl3_48),
% 0.22/0.43    inference(avatar_split_clause,[],[f454,f319,f69,f463])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    spl3_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.43  fof(f319,plain,(
% 0.22/0.43    spl3_48 <=> k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = k2_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.22/0.43  fof(f454,plain,(
% 0.22/0.43    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),X0) | r1_tarski(sK0,X0)) ) | (~spl3_10 | ~spl3_48)),
% 0.22/0.43    inference(superposition,[],[f70,f321])).
% 0.22/0.43  fof(f321,plain,(
% 0.22/0.43    k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = k2_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~spl3_48),
% 0.22/0.43    inference(avatar_component_clause,[],[f319])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl3_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f69])).
% 0.22/0.43  fof(f322,plain,(
% 0.22/0.43    spl3_48 | ~spl3_8 | ~spl3_45),
% 0.22/0.43    inference(avatar_split_clause,[],[f317,f304,f61,f319])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    spl3_8 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.43  fof(f304,plain,(
% 0.22/0.43    spl3_45 <=> r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.22/0.43  fof(f317,plain,(
% 0.22/0.43    k10_relat_1(sK2,k9_relat_1(sK2,sK0)) = k2_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | (~spl3_8 | ~spl3_45)),
% 0.22/0.43    inference(resolution,[],[f306,f62])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f61])).
% 0.22/0.43  fof(f306,plain,(
% 0.22/0.43    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | ~spl3_45),
% 0.22/0.43    inference(avatar_component_clause,[],[f304])).
% 0.22/0.43  fof(f307,plain,(
% 0.22/0.43    spl3_45 | ~spl3_3 | ~spl3_44),
% 0.22/0.43    inference(avatar_split_clause,[],[f301,f298,f38,f304])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    spl3_3 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.43  fof(f298,plain,(
% 0.22/0.43    spl3_44 <=> ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.22/0.43  fof(f301,plain,(
% 0.22/0.43    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | (~spl3_3 | ~spl3_44)),
% 0.22/0.43    inference(resolution,[],[f299,f40])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl3_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f38])).
% 0.22/0.43  fof(f299,plain,(
% 0.22/0.43    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) ) | ~spl3_44),
% 0.22/0.43    inference(avatar_component_clause,[],[f298])).
% 0.22/0.43  fof(f300,plain,(
% 0.22/0.43    spl3_44 | ~spl3_5 | ~spl3_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f296,f57,f48,f298])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    spl3_7 <=> ! [X1,X0] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.43  fof(f296,plain,(
% 0.22/0.43    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) ) | (~spl3_5 | ~spl3_7)),
% 0.22/0.43    inference(resolution,[],[f58,f50])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) ) | ~spl3_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f57])).
% 0.22/0.43  fof(f84,plain,(
% 0.22/0.43    spl3_12 | ~spl3_2 | ~spl3_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f73,f61,f33,f81])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    spl3_2 <=> r1_tarski(k9_relat_1(sK2,sK0),sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    sK1 = k2_xboole_0(k9_relat_1(sK2,sK0),sK1) | (~spl3_2 | ~spl3_8)),
% 0.22/0.43    inference(resolution,[],[f62,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    r1_tarski(k9_relat_1(sK2,sK0),sK1) | ~spl3_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f33])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    spl3_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f26,f69])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    spl3_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f25,f65])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl3_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f24,f61])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    spl3_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f23,f57])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f53])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    spl3_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f17,f48])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    v1_relat_1(sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ~r1_tarski(sK0,k10_relat_1(sK2,sK1)) & r1_tarski(k9_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,k10_relat_1(X2,X1)) & r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,k10_relat_1(sK2,sK1)) & r1_tarski(k9_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,k10_relat_1(X2,X1)) & r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0,X1,X2] : ((~r1_tarski(X0,k10_relat_1(X2,X1)) & (r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    spl3_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f38])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    spl3_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f33])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    r1_tarski(k9_relat_1(sK2,sK0),sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ~spl3_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f28])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ~r1_tarski(sK0,k10_relat_1(sK2,sK1))),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (14137)------------------------------
% 0.22/0.43  % (14137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (14137)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (14137)Memory used [KB]: 11129
% 0.22/0.43  % (14137)Time elapsed: 0.020 s
% 0.22/0.43  % (14137)------------------------------
% 0.22/0.43  % (14137)------------------------------
% 0.22/0.44  % (14131)Success in time 0.078 s
%------------------------------------------------------------------------------

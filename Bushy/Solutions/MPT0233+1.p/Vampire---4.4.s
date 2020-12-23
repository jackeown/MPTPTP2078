%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t28_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:04 EDT 2019

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   52 (  96 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 ( 242 expanded)
%              Number of equality atoms :   77 ( 142 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f59,f63,f359,f375,f379,f381])).

fof(f381,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f363,f32])).

fof(f32,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t28_zfmisc_1.p',dt_o_0_0_xboole_0)).

fof(f363,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_6 ),
    inference(superposition,[],[f35,f358])).

fof(f358,plain,
    ( k2_tarski(sK0,sK1) = o_0_0_xboole_0
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl4_6
  <=> k2_tarski(sK0,sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f35,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t28_zfmisc_1.p',fc3_xboole_0)).

fof(f379,plain,
    ( ~ spl4_11
    | spl4_1
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f362,f357,f53,f377])).

fof(f377,plain,
    ( spl4_11
  <=> o_0_0_xboole_0 != k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f53,plain,
    ( spl4_1
  <=> sK0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f362,plain,
    ( o_0_0_xboole_0 != k1_tarski(sK3)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(superposition,[],[f73,f358])).

fof(f73,plain,
    ( ! [X0] : k2_tarski(sK0,X0) != k1_tarski(sK3)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f54,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t28_zfmisc_1.p',t8_zfmisc_1)).

fof(f54,plain,
    ( sK0 != sK3
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f375,plain,
    ( ~ spl4_9
    | spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f361,f357,f57,f373])).

fof(f373,plain,
    ( spl4_9
  <=> o_0_0_xboole_0 != k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f57,plain,
    ( spl4_3
  <=> sK0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f361,plain,
    ( o_0_0_xboole_0 != k1_tarski(sK2)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(superposition,[],[f85,f358])).

fof(f85,plain,
    ( ! [X0] : k2_tarski(sK0,X0) != k1_tarski(sK2)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f58,f38])).

fof(f58,plain,
    ( sK0 != sK2
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f359,plain,
    ( spl4_6
    | spl4_1
    | spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f319,f61,f57,f53,f357])).

fof(f61,plain,
    ( spl4_4
  <=> r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f319,plain,
    ( k2_tarski(sK0,sK1) = o_0_0_xboole_0
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f73,f85,f62,f76,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | o_0_0_xboole_0 = X0
      | k2_tarski(X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f39,f33])).

fof(f33,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t28_zfmisc_1.p',d2_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t28_zfmisc_1.p',l45_zfmisc_1)).

fof(f76,plain,
    ( ! [X0] : k2_tarski(sK2,sK3) != k2_tarski(sK0,X0)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f54,f58,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X0,X1) != k2_tarski(X2,X3)
      | X0 = X2
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( X0 = X3
      | X0 = X2
      | k2_tarski(X0,X1) != k2_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t28_zfmisc_1.p',t10_zfmisc_1)).

fof(f62,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f63,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t28_zfmisc_1.p',t28_zfmisc_1)).

fof(f59,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f31,f53])).

fof(f31,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t20_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:16 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   45 (  90 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 257 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f73,f83,f92,f105,f107,f109])).

fof(f109,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f104,f93])).

fof(f93,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f82,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t20_setfam_1.p',t7_boole)).

fof(f82,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f104,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl4_3 ),
    inference(resolution,[],[f52,f72])).

fof(f72,plain,
    ( ~ r1_setfam_1(k1_xboole_0,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_3
  <=> ~ r1_setfam_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK2(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK3(X1,X4))
              & r2_hidden(sK3(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f39,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK2(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK3(X1,X4))
        & r2_hidden(sK3(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t20_setfam_1.p',d2_setfam_1)).

fof(f107,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f101,f93])).

fof(f101,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK0),k1_xboole_0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f72,f52])).

fof(f105,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f72,f93,f52])).

fof(f92,plain,
    ( spl4_6
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f74,f64,f90])).

fof(f90,plain,
    ( spl4_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f64,plain,
    ( spl4_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f74,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f65,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t20_setfam_1.p',t6_boole)).

fof(f65,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f64])).

fof(f83,plain,
    ( spl4_4
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f76,f64,f81])).

fof(f76,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_0 ),
    inference(backward_demodulation,[],[f74,f65])).

fof(f73,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f42,f71])).

fof(f42,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f32])).

fof(f32,plain,
    ( ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0)
   => ~ r1_setfam_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t20_setfam_1.p',t20_setfam_1)).

fof(f66,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f43,f64])).

fof(f43,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t20_setfam_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------

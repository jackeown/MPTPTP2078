%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0398+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  48 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   72 (  94 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f34,f41,f46,f50])).

fof(f50,plain,
    ( spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl3_4
    | ~ spl3_5 ),
    inference(resolution,[],[f45,f40])).

fof(f40,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_4
  <=> r1_setfam_1(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f45,plain,
    ( ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f46,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f25,f44])).

fof(f25,plain,
    ( spl3_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0)
    | ~ spl3_2 ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(resolution,[],[f17,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f41,plain,
    ( ~ spl3_4
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f36,f31,f20,f38])).

fof(f20,plain,
    ( spl3_1
  <=> r1_setfam_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f31,plain,
    ( spl3_3
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f36,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f22,f33])).

fof(f33,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f22,plain,
    ( ~ r1_setfam_1(k1_xboole_0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f34,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f29,f25,f31])).

fof(f29,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl3_2 ),
    inference(resolution,[],[f13,f27])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f28,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f23,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f11,f20])).

fof(f11,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_setfam_1)).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t117_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:58 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   58 (  90 expanded)
%              Number of leaves         :   13 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  144 ( 237 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f58,f71,f162,f233,f276,f297,f306])).

fof(f306,plain,
    ( spl10_10
    | spl10_8
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f284,f63,f157,f160])).

fof(f160,plain,
    ( spl10_10
  <=> ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f157,plain,
    ( spl10_8
  <=> ! [X3] : ~ r2_hidden(X3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f63,plain,
    ( spl10_4
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X1,sK1)
        | r2_hidden(X1,sK2) )
    | ~ spl10_4 ),
    inference(resolution,[],[f277,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t117_zfmisc_1.p',l54_zfmisc_1)).

fof(f277,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK2))
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl10_4 ),
    inference(resolution,[],[f64,f81])).

fof(f81,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r1_tarski(k2_zfmisc_1(X11,X9),X12)
      | ~ r2_hidden(X10,X11)
      | r2_hidden(k4_tarski(X10,X8),X12)
      | ~ r2_hidden(X8,X9) ) ),
    inference(resolution,[],[f28,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t117_zfmisc_1.p',d3_tarski)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f297,plain,
    ( spl10_12
    | spl10_7 ),
    inference(avatar_split_clause,[],[f279,f66,f295])).

fof(f295,plain,
    ( spl10_12
  <=> k4_tarski(sK5(sK1,sK0,sK3(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))),sK6(sK1,sK0,sK3(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)))) = sK3(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f66,plain,
    ( spl10_7
  <=> ~ r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f279,plain,
    ( k4_tarski(sK5(sK1,sK0,sK3(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))),sK6(sK1,sK0,sK3(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)))) = sK3(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
    | ~ spl10_7 ),
    inference(resolution,[],[f67,f84])).

fof(f84,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k2_zfmisc_1(X6,X7),X8)
      | k4_tarski(sK5(X6,X7,sK3(k2_zfmisc_1(X6,X7),X8)),sK6(X6,X7,sK3(k2_zfmisc_1(X6,X7),X8))) = sK3(k2_zfmisc_1(X6,X7),X8) ) ),
    inference(resolution,[],[f42,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK5(X0,X1,X3),sK6(X0,X1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK5(X0,X1,X3),sK6(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t117_zfmisc_1.p',d2_zfmisc_1)).

fof(f67,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f276,plain,
    ( spl10_1
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f254,f50])).

fof(f50,plain,
    ( k1_xboole_0 != sK0
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl10_1
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f254,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_8 ),
    inference(resolution,[],[f158,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t117_zfmisc_1.p',t7_xboole_0)).

fof(f158,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f233,plain,
    ( spl10_3
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f231,f57])).

fof(f57,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl10_3
  <=> ~ r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f231,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl10_10 ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,
    ( r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ spl10_10 ),
    inference(resolution,[],[f174,f24])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0,sK2),sK1)
        | r1_tarski(X0,sK2) )
    | ~ spl10_10 ),
    inference(resolution,[],[f161,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f161,plain,
    ( ! [X2] :
        ( r2_hidden(X2,sK2)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( spl10_8
    | spl10_10
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f121,f69,f160,f157])).

fof(f69,plain,
    ( spl10_6
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f121,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,sK1)
        | ~ r2_hidden(X3,sK0)
        | r2_hidden(X2,sK2) )
    | ~ spl10_6 ),
    inference(resolution,[],[f110,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl10_6 ),
    inference(resolution,[],[f81,f70])).

fof(f70,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,
    ( spl10_4
    | spl10_6 ),
    inference(avatar_split_clause,[],[f20,f69,f63])).

fof(f20,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X1,X2)
      & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_tarski(X1,X2)
          & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
            | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t117_zfmisc_1.p',t117_zfmisc_1)).

fof(f58,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------

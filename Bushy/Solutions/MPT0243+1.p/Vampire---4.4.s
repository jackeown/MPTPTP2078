%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t38_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:06 EDT 2019

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 171 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  217 ( 410 expanded)
%              Number of equality atoms :   26 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f335,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f56,f57,f98,f112,f119,f126,f267,f291,f307,f314,f322,f329,f334])).

fof(f334,plain,
    ( ~ spl5_0
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f331,f45])).

fof(f45,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl5_3
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f331,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_0 ),
    inference(resolution,[],[f42,f75])).

fof(f75,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k2_tarski(X3,X5),X4)
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f27,f35])).

fof(f35,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_tarski(X3,X1)) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t38_zfmisc_1.p',d2_tarski)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t38_zfmisc_1.p',d3_tarski)).

fof(f42,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl5_0
  <=> r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f329,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f327,f39])).

fof(f39,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl5_1
  <=> ~ r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f327,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f325,f48])).

fof(f48,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f325,plain,
    ( ~ r2_hidden(sK0,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_18 ),
    inference(superposition,[],[f29,f306])).

fof(f306,plain,
    ( sK0 = sK4(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl5_18
  <=> sK0 = sK4(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f322,plain,
    ( ~ spl5_21
    | spl5_17
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f315,f305,f296,f320])).

fof(f320,plain,
    ( spl5_21
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f296,plain,
    ( spl5_17
  <=> sK1 != sK4(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f315,plain,
    ( sK0 != sK1
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f297,f306])).

fof(f297,plain,
    ( sK1 != sK4(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f296])).

fof(f314,plain,
    ( spl5_1
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f312,f39])).

fof(f312,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f310,f55])).

fof(f55,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_4
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f310,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_16 ),
    inference(superposition,[],[f29,f300])).

fof(f300,plain,
    ( sK1 = sK4(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl5_16
  <=> sK1 = sK4(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f307,plain,
    ( spl5_16
    | spl5_18
    | spl5_1 ),
    inference(avatar_split_clause,[],[f152,f38,f305,f299])).

fof(f152,plain,
    ( sK0 = sK4(k2_tarski(sK0,sK1),sK2)
    | sK1 = sK4(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f79,f39])).

fof(f79,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k2_tarski(X5,X4),X6)
      | sK4(k2_tarski(X5,X4),X6) = X5
      | sK4(k2_tarski(X5,X4),X6) = X4 ) ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f291,plain,
    ( ~ spl5_15
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f274,f54,f289])).

fof(f289,plain,
    ( spl5_15
  <=> ~ r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f274,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK2,sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f133,f102])).

fof(f102,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,X0)
        | ~ r1_tarski(sK2,X0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f55,f27])).

fof(f133,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ r1_tarski(sK2,X2) )
    | ~ spl5_4 ),
    inference(resolution,[],[f102,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t38_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f267,plain,
    ( ~ spl5_13
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f160,f47,f265])).

fof(f265,plain,
    ( spl5_13
  <=> ~ r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f160,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ r1_tarski(sK2,sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f128,f99])).

fof(f99,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | ~ r1_tarski(sK2,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f48,f27])).

fof(f128,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | ~ r1_tarski(sK2,X2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f99,f30])).

fof(f126,plain,
    ( ~ spl5_11
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f103,f54,f124])).

fof(f124,plain,
    ( spl5_11
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f103,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f55,f30])).

fof(f119,plain,
    ( ~ spl5_9
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f100,f47,f117])).

fof(f117,plain,
    ( spl5_9
  <=> ~ r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f100,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f48,f30])).

fof(f112,plain,
    ( ~ spl5_7
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f101,f47,f110])).

fof(f110,plain,
    ( spl5_7
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f101,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t38_zfmisc_1.p',t7_boole)).

fof(f98,plain,
    ( ~ spl5_0
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f92,f52])).

fof(f52,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_5
  <=> ~ r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f92,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_0 ),
    inference(resolution,[],[f74,f42])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X2,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_tarski(X0,X3)) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f17,f44,f51,f38])).

fof(f17,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t38_zfmisc_1.p',t38_zfmisc_1)).

fof(f56,plain,
    ( spl5_0
    | spl5_4 ),
    inference(avatar_split_clause,[],[f19,f54,f41])).

fof(f19,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,
    ( spl5_0
    | spl5_2 ),
    inference(avatar_split_clause,[],[f18,f47,f41])).

fof(f18,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------

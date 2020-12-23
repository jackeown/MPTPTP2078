%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t64_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:12 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 166 expanded)
%              Number of leaves         :   16 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  158 ( 378 expanded)
%              Number of equality atoms :    2 (  20 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f749,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f50,f58,f84,f93,f714,f727,f738,f744,f746,f748])).

fof(f748,plain,
    ( ~ spl8_4
    | spl8_17 ),
    inference(avatar_contradiction_clause,[],[f747])).

fof(f747,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f37,f739])).

fof(f739,plain,
    ( ~ r1_xboole_0(sK1,sK5)
    | ~ spl8_17 ),
    inference(resolution,[],[f737,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f18,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t64_mcart_1.p',symmetry_r1_xboole_0)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t64_mcart_1.p',t127_zfmisc_1)).

fof(f737,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f736])).

fof(f736,plain,
    ( spl8_17
  <=> ~ r1_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f37,plain,
    ( r1_xboole_0(sK1,sK5)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl8_4
  <=> r1_xboole_0(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f746,plain,
    ( ~ spl8_10
    | spl8_17 ),
    inference(avatar_contradiction_clause,[],[f745])).

fof(f745,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f742,f57])).

fof(f57,plain,
    ( r1_xboole_0(sK4,sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl8_10
  <=> r1_xboole_0(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f742,plain,
    ( ~ r1_xboole_0(sK4,sK0)
    | ~ spl8_17 ),
    inference(resolution,[],[f737,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f744,plain,
    ( ~ spl8_2
    | spl8_17 ),
    inference(avatar_contradiction_clause,[],[f743])).

fof(f743,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f740,f31])).

fof(f31,plain,
    ( r1_xboole_0(sK0,sK4)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl8_2
  <=> r1_xboole_0(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f740,plain,
    ( ~ r1_xboole_0(sK0,sK4)
    | ~ spl8_17 ),
    inference(resolution,[],[f737,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X0,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f17,f15])).

fof(f738,plain,
    ( ~ spl8_17
    | spl8_1 ),
    inference(avatar_split_clause,[],[f728,f23,f736])).

fof(f23,plain,
    ( spl8_1
  <=> ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f728,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_1 ),
    inference(resolution,[],[f677,f24])).

fof(f24,plain,
    ( ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f677,plain,(
    ! [X14,X12,X10,X8,X15,X13,X11,X9] :
      ( r1_xboole_0(k4_zfmisc_1(X8,X9,X10,X11),k4_zfmisc_1(X12,X13,X14,X15))
      | ~ r1_xboole_0(k2_zfmisc_1(X12,X13),k2_zfmisc_1(X8,X9)) ) ),
    inference(resolution,[],[f109,f60])).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | r1_xboole_0(k4_zfmisc_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(superposition,[],[f66,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t64_mcart_1.p',t53_mcart_1)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k2_zfmisc_1(X4,X5))
      | ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X4) ) ),
    inference(superposition,[],[f17,f16])).

fof(f727,plain,
    ( ~ spl8_7
    | spl8_1 ),
    inference(avatar_split_clause,[],[f723,f23,f39])).

fof(f39,plain,
    ( spl8_7
  <=> ~ r1_xboole_0(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f723,plain,
    ( ~ r1_xboole_0(sK2,sK6)
    | ~ spl8_1 ),
    inference(resolution,[],[f678,f24])).

fof(f678,plain,(
    ! [X23,X21,X19,X17,X22,X20,X18,X16] :
      ( r1_xboole_0(k4_zfmisc_1(X16,X17,X18,X19),k4_zfmisc_1(X20,X21,X22,X23))
      | ~ r1_xboole_0(X18,X22) ) ),
    inference(resolution,[],[f109,f18])).

fof(f714,plain,
    ( ~ spl8_15
    | spl8_1 ),
    inference(avatar_split_clause,[],[f704,f23,f712])).

fof(f712,plain,
    ( spl8_15
  <=> ~ r1_xboole_0(sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f704,plain,
    ( ~ r1_xboole_0(sK6,sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f676,f24])).

fof(f676,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      | ~ r1_xboole_0(X6,X2) ) ),
    inference(resolution,[],[f109,f61])).

fof(f93,plain,
    ( ~ spl8_13
    | spl8_1 ),
    inference(avatar_split_clause,[],[f85,f23,f91])).

fof(f91,plain,
    ( spl8_13
  <=> ~ r1_xboole_0(sK7,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f85,plain,
    ( ~ r1_xboole_0(sK7,sK3)
    | ~ spl8_1 ),
    inference(resolution,[],[f79,f24])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      | ~ r1_xboole_0(X7,X3) ) ),
    inference(superposition,[],[f72,f16])).

fof(f72,plain,(
    ! [X39,X37,X41,X38,X36,X40] :
      ( r1_xboole_0(k2_zfmisc_1(X40,X41),k4_zfmisc_1(X36,X37,X38,X39))
      | ~ r1_xboole_0(X39,X41) ) ),
    inference(superposition,[],[f61,f16])).

fof(f84,plain,
    ( ~ spl8_9
    | spl8_1 ),
    inference(avatar_split_clause,[],[f82,f23,f45])).

fof(f45,plain,
    ( spl8_9
  <=> ~ r1_xboole_0(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f82,plain,
    ( ~ r1_xboole_0(sK3,sK7)
    | ~ spl8_1 ),
    inference(resolution,[],[f75,f24])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_xboole_0(k4_zfmisc_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ r1_xboole_0(X7,X3) ) ),
    inference(superposition,[],[f68,f16])).

fof(f68,plain,(
    ! [X14,X12,X17,X15,X13,X16] :
      ( r1_xboole_0(k4_zfmisc_1(X12,X13,X14,X15),k2_zfmisc_1(X16,X17))
      | ~ r1_xboole_0(X15,X17) ) ),
    inference(superposition,[],[f18,f16])).

fof(f58,plain,
    ( spl8_10
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f51,f30,f56])).

fof(f51,plain,
    ( r1_xboole_0(sK4,sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f31,f15])).

fof(f50,plain,
    ( spl8_2
    | spl8_4
    | spl8_6
    | spl8_8 ),
    inference(avatar_split_clause,[],[f14,f48,f42,f36,f30])).

fof(f42,plain,
    ( spl8_6
  <=> r1_xboole_0(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f48,plain,
    ( spl8_8
  <=> r1_xboole_0(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f14,plain,
    ( r1_xboole_0(sK3,sK7)
    | r1_xboole_0(sK2,sK6)
    | r1_xboole_0(sK1,sK5)
    | r1_xboole_0(sK0,sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( r1_xboole_0(sK3,sK7)
      | r1_xboole_0(sK2,sK6)
      | r1_xboole_0(sK1,sK5)
      | r1_xboole_0(sK0,sK4) )
    & ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( r1_xboole_0(X3,X7)
          | r1_xboole_0(X2,X6)
          | r1_xboole_0(X1,X5)
          | r1_xboole_0(X0,X4) )
        & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
   => ( ( r1_xboole_0(sK3,sK7)
        | r1_xboole_0(sK2,sK6)
        | r1_xboole_0(sK1,sK5)
        | r1_xboole_0(sK0,sK4) )
      & ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( r1_xboole_0(X3,X7)
        | r1_xboole_0(X2,X6)
        | r1_xboole_0(X1,X5)
        | r1_xboole_0(X0,X4) )
      & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
       => ( ~ r1_xboole_0(X3,X7)
          & ~ r1_xboole_0(X2,X6)
          & ~ r1_xboole_0(X1,X5)
          & ~ r1_xboole_0(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
     => ( ~ r1_xboole_0(X3,X7)
        & ~ r1_xboole_0(X2,X6)
        & ~ r1_xboole_0(X1,X5)
        & ~ r1_xboole_0(X0,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t64_mcart_1.p',t64_mcart_1)).

fof(f25,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f13,f23])).

fof(f13,plain,(
    ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------

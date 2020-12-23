%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 117 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :    6
%              Number of atoms          :  190 ( 288 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f45,f49,f61,f65,f71,f75,f87,f95,f122,f211,f220,f233,f237,f283,f285])).

fof(f285,plain,
    ( spl2_23
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl2_23
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f245,f282])).

fof(f282,plain,
    ( ! [X0,X1] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k5_xboole_0(X1,X0)))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl2_26
  <=> ! [X1,X0] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k5_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f245,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_23
    | ~ spl2_24 ),
    inference(unit_resulting_resolution,[],[f232,f236])).

fof(f236,plain,
    ( ! [X4,X5,X3] :
        ( r1_tarski(k4_xboole_0(X3,X4),X5)
        | ~ r1_tarski(X3,X5) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl2_24
  <=> ! [X3,X5,X4] :
        ( r1_tarski(k4_xboole_0(X3,X4),X5)
        | ~ r1_tarski(X3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f232,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_23 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl2_23
  <=> r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f283,plain,
    ( spl2_26
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f106,f85,f59,f281])).

fof(f59,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f85,plain,
    ( spl2_12
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f106,plain,
    ( ! [X0,X1] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k5_xboole_0(X1,X0)))
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f86,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f86,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f237,plain,
    ( spl2_24
    | ~ spl2_8
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f228,f218,f63,f235])).

fof(f63,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f218,plain,
    ( spl2_22
  <=> ! [X9,X11,X10] :
        ( r1_tarski(k4_xboole_0(X9,X10),X11)
        | ~ r1_tarski(k3_xboole_0(X9,X10),X11)
        | ~ r1_tarski(X9,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f228,plain,
    ( ! [X4,X5,X3] :
        ( r1_tarski(k4_xboole_0(X3,X4),X5)
        | ~ r1_tarski(X3,X5) )
    | ~ spl2_8
    | ~ spl2_22 ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,
    ( ! [X4,X5,X3] :
        ( r1_tarski(k4_xboole_0(X3,X4),X5)
        | ~ r1_tarski(X3,X5)
        | ~ r1_tarski(X3,X5) )
    | ~ spl2_8
    | ~ spl2_22 ),
    inference(resolution,[],[f219,f64])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f219,plain,
    ( ! [X10,X11,X9] :
        ( ~ r1_tarski(k3_xboole_0(X9,X10),X11)
        | r1_tarski(k4_xboole_0(X9,X10),X11)
        | ~ r1_tarski(X9,X11) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f218])).

fof(f233,plain,
    ( ~ spl2_23
    | spl2_1
    | ~ spl2_15
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f212,f209,f120,f34,f230])).

fof(f34,plain,
    ( spl2_1
  <=> r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f120,plain,
    ( spl2_15
  <=> ! [X1,X0] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f209,plain,
    ( spl2_21
  <=> ! [X7,X8,X6] :
        ( r1_tarski(k2_xboole_0(X6,X7),X8)
        | ~ r1_tarski(k4_xboole_0(X7,X6),X8)
        | ~ r1_tarski(X6,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f212,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_1
    | ~ spl2_15
    | ~ spl2_21 ),
    inference(unit_resulting_resolution,[],[f121,f36,f210])).

fof(f210,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_tarski(k4_xboole_0(X7,X6),X8)
        | r1_tarski(k2_xboole_0(X6,X7),X8)
        | ~ r1_tarski(X6,X8) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f209])).

fof(f36,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f121,plain,
    ( ! [X0,X1] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k5_xboole_0(X0,X1)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f120])).

fof(f220,plain,
    ( spl2_22
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f100,f93,f73,f218])).

fof(f73,plain,
    ( spl2_10
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f93,plain,
    ( spl2_13
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f100,plain,
    ( ! [X10,X11,X9] :
        ( r1_tarski(k4_xboole_0(X9,X10),X11)
        | ~ r1_tarski(k3_xboole_0(X9,X10),X11)
        | ~ r1_tarski(X9,X11) )
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(superposition,[],[f94,f74])).

fof(f74,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f94,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k5_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f211,plain,
    ( spl2_21
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f99,f93,f69,f209])).

fof(f69,plain,
    ( spl2_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f99,plain,
    ( ! [X6,X8,X7] :
        ( r1_tarski(k2_xboole_0(X6,X7),X8)
        | ~ r1_tarski(k4_xboole_0(X7,X6),X8)
        | ~ r1_tarski(X6,X8) )
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(superposition,[],[f94,f70])).

fof(f70,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f122,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f76,f59,f47,f120])).

fof(f47,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f76,plain,
    ( ! [X0,X1] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k5_xboole_0(X0,X1)))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f48,f60])).

fof(f48,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f95,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f32,f93])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f87,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f66,f47,f43,f85])).

fof(f43,plain,
    ( spl2_3
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f66,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f48,f44])).

fof(f44,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f75,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f28,f73])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f71,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f65,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f61,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f49,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f45,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f37,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f34])).

fof(f21,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).

fof(f19,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:26:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (27225)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (27221)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (27224)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (27231)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (27224)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f286,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f37,f45,f49,f61,f65,f71,f75,f87,f95,f122,f211,f220,f233,f237,f283,f285])).
% 0.21/0.47  fof(f285,plain,(
% 0.21/0.47    spl2_23 | ~spl2_24 | ~spl2_26),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f284])).
% 0.21/0.47  fof(f284,plain,(
% 0.21/0.47    $false | (spl2_23 | ~spl2_24 | ~spl2_26)),
% 0.21/0.47    inference(subsumption_resolution,[],[f245,f282])).
% 0.21/0.47  fof(f282,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k5_xboole_0(X1,X0)))) ) | ~spl2_26),
% 0.21/0.47    inference(avatar_component_clause,[],[f281])).
% 0.21/0.47  fof(f281,plain,(
% 0.21/0.47    spl2_26 <=> ! [X1,X0] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k5_xboole_0(X1,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.47  fof(f245,plain,(
% 0.21/0.47    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | (spl2_23 | ~spl2_24)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f232,f236])).
% 0.21/0.47  fof(f236,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (r1_tarski(k4_xboole_0(X3,X4),X5) | ~r1_tarski(X3,X5)) ) | ~spl2_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f235])).
% 0.21/0.47  fof(f235,plain,(
% 0.21/0.47    spl2_24 <=> ! [X3,X5,X4] : (r1_tarski(k4_xboole_0(X3,X4),X5) | ~r1_tarski(X3,X5))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.47  fof(f232,plain,(
% 0.21/0.47    ~r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_23),
% 0.21/0.47    inference(avatar_component_clause,[],[f230])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    spl2_23 <=> r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.47  fof(f283,plain,(
% 0.21/0.47    spl2_26 | ~spl2_7 | ~spl2_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f106,f85,f59,f281])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl2_7 <=> ! [X1,X0] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl2_12 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k5_xboole_0(X1,X0)))) ) | (~spl2_7 | ~spl2_12)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f86,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0))) ) | ~spl2_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f85])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    spl2_24 | ~spl2_8 | ~spl2_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f228,f218,f63,f235])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl2_8 <=> ! [X1,X0,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f218,plain,(
% 0.21/0.47    spl2_22 <=> ! [X9,X11,X10] : (r1_tarski(k4_xboole_0(X9,X10),X11) | ~r1_tarski(k3_xboole_0(X9,X10),X11) | ~r1_tarski(X9,X11))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (r1_tarski(k4_xboole_0(X3,X4),X5) | ~r1_tarski(X3,X5)) ) | (~spl2_8 | ~spl2_22)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f224])).
% 0.21/0.47  fof(f224,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (r1_tarski(k4_xboole_0(X3,X4),X5) | ~r1_tarski(X3,X5) | ~r1_tarski(X3,X5)) ) | (~spl2_8 | ~spl2_22)),
% 0.21/0.47    inference(resolution,[],[f219,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) ) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f219,plain,(
% 0.21/0.47    ( ! [X10,X11,X9] : (~r1_tarski(k3_xboole_0(X9,X10),X11) | r1_tarski(k4_xboole_0(X9,X10),X11) | ~r1_tarski(X9,X11)) ) | ~spl2_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f218])).
% 0.21/0.47  fof(f233,plain,(
% 0.21/0.47    ~spl2_23 | spl2_1 | ~spl2_15 | ~spl2_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f212,f209,f120,f34,f230])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl2_1 <=> r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    spl2_15 <=> ! [X1,X0] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.47  fof(f209,plain,(
% 0.21/0.47    spl2_21 <=> ! [X7,X8,X6] : (r1_tarski(k2_xboole_0(X6,X7),X8) | ~r1_tarski(k4_xboole_0(X7,X6),X8) | ~r1_tarski(X6,X8))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.47  fof(f212,plain,(
% 0.21/0.47    ~r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | (spl2_1 | ~spl2_15 | ~spl2_21)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f121,f36,f210])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    ( ! [X6,X8,X7] : (~r1_tarski(k4_xboole_0(X7,X6),X8) | r1_tarski(k2_xboole_0(X6,X7),X8) | ~r1_tarski(X6,X8)) ) | ~spl2_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f209])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f34])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k5_xboole_0(X0,X1)))) ) | ~spl2_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f120])).
% 0.21/0.47  fof(f220,plain,(
% 0.21/0.47    spl2_22 | ~spl2_10 | ~spl2_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f100,f93,f73,f218])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl2_10 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    spl2_13 <=> ! [X1,X0,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    ( ! [X10,X11,X9] : (r1_tarski(k4_xboole_0(X9,X10),X11) | ~r1_tarski(k3_xboole_0(X9,X10),X11) | ~r1_tarski(X9,X11)) ) | (~spl2_10 | ~spl2_13)),
% 0.21/0.47    inference(superposition,[],[f94,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) ) | ~spl2_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f93])).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    spl2_21 | ~spl2_9 | ~spl2_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f99,f93,f69,f209])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl2_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ( ! [X6,X8,X7] : (r1_tarski(k2_xboole_0(X6,X7),X8) | ~r1_tarski(k4_xboole_0(X7,X6),X8) | ~r1_tarski(X6,X8)) ) | (~spl2_9 | ~spl2_13)),
% 0.21/0.47    inference(superposition,[],[f94,f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f69])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    spl2_15 | ~spl2_4 | ~spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f76,f59,f47,f120])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl2_4 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k5_xboole_0(X0,X1)))) ) | (~spl2_4 | ~spl2_7)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f48,f60])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl2_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f93])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl2_12 | ~spl2_3 | ~spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f66,f47,f43,f85])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl2_3 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0))) ) | (~spl2_3 | ~spl2_4)),
% 0.21/0.48    inference(superposition,[],[f48,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f43])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl2_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f73])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl2_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f69])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl2_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f63])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl2_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f59])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f47])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f43])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f34])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (27224)------------------------------
% 0.21/0.48  % (27224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27224)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (27224)Memory used [KB]: 6268
% 0.21/0.48  % (27224)Time elapsed: 0.057 s
% 0.21/0.48  % (27224)------------------------------
% 0.21/0.48  % (27224)------------------------------
% 0.21/0.48  % (27218)Success in time 0.117 s
%------------------------------------------------------------------------------

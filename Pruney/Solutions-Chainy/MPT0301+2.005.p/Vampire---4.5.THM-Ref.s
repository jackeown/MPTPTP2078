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
% DateTime   : Thu Dec  3 12:41:52 EST 2020

% Result     : Theorem 2.91s
% Output     : Refutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 164 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  309 ( 592 expanded)
%              Number of equality atoms :  100 ( 242 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f81,f83,f101,f105,f204,f211,f213,f220,f227,f234])).

fof(f234,plain,
    ( spl9_3
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl9_3
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f231,f79])).

fof(f79,plain,
    ( k1_xboole_0 != sK1
    | spl9_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl9_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f231,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_8 ),
    inference(resolution,[],[f203,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f203,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl9_8
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f227,plain,
    ( spl9_2
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl9_2
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f224,f74])).

fof(f74,plain,
    ( k1_xboole_0 != sK0
    | spl9_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f224,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_7 ),
    inference(resolution,[],[f200,f53])).

fof(f200,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl9_7
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f220,plain,
    ( spl9_1
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl9_1
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f218,f153])).

fof(f153,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl9_5 ),
    inference(resolution,[],[f151,f53])).

fof(f151,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ spl9_5 ),
    inference(resolution,[],[f65,f100])).

fof(f100,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl9_5
  <=> ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f65,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2))
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f218,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl9_1
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f70,f80])).

fof(f80,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f70,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl9_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f213,plain,
    ( ~ spl9_5
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl9_5
    | spl9_9 ),
    inference(unit_resulting_resolution,[],[f176,f210,f53])).

fof(f210,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl9_9
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f176,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))
    | ~ spl9_5 ),
    inference(resolution,[],[f66,f100])).

fof(f66,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f211,plain,
    ( ~ spl9_9
    | spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f206,f72,f68,f208])).

fof(f206,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl9_1
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f70,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f204,plain,
    ( spl9_7
    | spl9_8
    | ~ spl9_1
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f197,f99,f68,f202,f199])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_1
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f191,f100])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_1 ),
    inference(superposition,[],[f44,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f105,plain,(
    ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f55,f97])).

fof(f97,plain,
    ( ! [X0,X1] : ~ r1_xboole_0(X0,X1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_4
  <=> ! [X1,X0] : ~ r1_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f55,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f101,plain,
    ( spl9_4
    | spl9_5 ),
    inference(avatar_split_clause,[],[f94,f99,f96])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f57,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f57,f53])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f83,plain,
    ( ~ spl9_3
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f82,f68,f78])).

fof(f82,plain,
    ( k1_xboole_0 != sK1
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f41,f69])).

fof(f41,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f81,plain,
    ( spl9_2
    | spl9_3
    | spl9_1 ),
    inference(avatar_split_clause,[],[f76,f68,f78,f72])).

fof(f76,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_1 ),
    inference(subsumption_resolution,[],[f39,f70])).

fof(f39,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f40,f72,f68])).

fof(f40,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.53  % (14128)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (14113)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (14105)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (14120)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (14112)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (14106)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (14109)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (14101)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (14109)Refutation not found, incomplete strategy% (14109)------------------------------
% 0.22/0.55  % (14109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14109)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14109)Memory used [KB]: 10618
% 0.22/0.55  % (14109)Time elapsed: 0.129 s
% 0.22/0.55  % (14109)------------------------------
% 0.22/0.55  % (14109)------------------------------
% 0.22/0.56  % (14120)Refutation not found, incomplete strategy% (14120)------------------------------
% 0.22/0.56  % (14120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (14120)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (14120)Memory used [KB]: 1663
% 0.22/0.56  % (14120)Time elapsed: 0.132 s
% 0.22/0.56  % (14120)------------------------------
% 0.22/0.56  % (14120)------------------------------
% 0.22/0.57  % (14103)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (14110)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (14107)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (14100)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.57  % (14107)Refutation not found, incomplete strategy% (14107)------------------------------
% 0.22/0.57  % (14107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (14107)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (14107)Memory used [KB]: 10746
% 0.22/0.57  % (14107)Time elapsed: 0.137 s
% 0.22/0.57  % (14107)------------------------------
% 0.22/0.57  % (14107)------------------------------
% 0.22/0.58  % (14101)Refutation not found, incomplete strategy% (14101)------------------------------
% 0.22/0.58  % (14101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (14101)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (14101)Memory used [KB]: 10618
% 0.22/0.58  % (14101)Time elapsed: 0.144 s
% 0.22/0.58  % (14101)------------------------------
% 0.22/0.58  % (14101)------------------------------
% 0.22/0.58  % (14104)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.58  % (14118)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.58  % (14117)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.58  % (14102)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.58  % (14122)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.58  % (14126)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.58  % (14121)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.59  % (14121)Refutation not found, incomplete strategy% (14121)------------------------------
% 0.22/0.59  % (14121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (14115)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.59  % (14114)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.59  % (14123)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.59  % (14121)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (14121)Memory used [KB]: 10746
% 0.22/0.59  % (14121)Time elapsed: 0.143 s
% 0.22/0.59  % (14121)------------------------------
% 0.22/0.59  % (14121)------------------------------
% 0.22/0.60  % (14110)Refutation not found, incomplete strategy% (14110)------------------------------
% 0.22/0.60  % (14110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (14110)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (14110)Memory used [KB]: 10618
% 0.22/0.60  % (14110)Time elapsed: 0.186 s
% 0.22/0.60  % (14110)------------------------------
% 0.22/0.60  % (14110)------------------------------
% 0.22/0.60  % (14099)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.61  % (14119)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.84/0.62  % (14099)Refutation not found, incomplete strategy% (14099)------------------------------
% 1.84/0.62  % (14099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.62  % (14099)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.62  
% 1.84/0.62  % (14099)Memory used [KB]: 1663
% 1.84/0.62  % (14099)Time elapsed: 0.189 s
% 1.84/0.62  % (14099)------------------------------
% 1.84/0.62  % (14099)------------------------------
% 1.84/0.62  % (14127)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.05/0.62  % (14111)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.05/0.62  % (14125)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.05/0.63  % (14108)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.05/0.63  % (14116)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.05/0.63  % (14116)Refutation not found, incomplete strategy% (14116)------------------------------
% 2.05/0.63  % (14116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.63  % (14116)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.63  
% 2.05/0.63  % (14116)Memory used [KB]: 10618
% 2.05/0.63  % (14116)Time elapsed: 0.196 s
% 2.05/0.63  % (14116)------------------------------
% 2.05/0.63  % (14116)------------------------------
% 2.05/0.63  % (14119)Refutation not found, incomplete strategy% (14119)------------------------------
% 2.05/0.63  % (14119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.63  % (14119)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.63  
% 2.05/0.63  % (14119)Memory used [KB]: 10746
% 2.05/0.63  % (14119)Time elapsed: 0.200 s
% 2.05/0.63  % (14119)------------------------------
% 2.05/0.63  % (14119)------------------------------
% 2.05/0.63  % (14108)Refutation not found, incomplete strategy% (14108)------------------------------
% 2.05/0.63  % (14108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.63  % (14108)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.63  
% 2.05/0.63  % (14108)Memory used [KB]: 10618
% 2.05/0.63  % (14108)Time elapsed: 0.197 s
% 2.05/0.63  % (14108)------------------------------
% 2.05/0.63  % (14108)------------------------------
% 2.05/0.63  % (14124)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.64/0.73  % (14153)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.64/0.75  % (14161)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.64/0.75  % (14162)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.64/0.75  % (14156)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.64/0.77  % (14157)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.64/0.77  % (14158)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.91/0.79  % (14157)Refutation found. Thanks to Tanya!
% 2.91/0.79  % SZS status Theorem for theBenchmark
% 2.91/0.79  % SZS output start Proof for theBenchmark
% 2.91/0.79  fof(f235,plain,(
% 2.91/0.79    $false),
% 2.91/0.79    inference(avatar_sat_refutation,[],[f75,f81,f83,f101,f105,f204,f211,f213,f220,f227,f234])).
% 2.91/0.79  fof(f234,plain,(
% 2.91/0.79    spl9_3 | ~spl9_8),
% 2.91/0.79    inference(avatar_contradiction_clause,[],[f233])).
% 2.91/0.79  fof(f233,plain,(
% 2.91/0.79    $false | (spl9_3 | ~spl9_8)),
% 2.91/0.79    inference(subsumption_resolution,[],[f231,f79])).
% 2.91/0.79  fof(f79,plain,(
% 2.91/0.79    k1_xboole_0 != sK1 | spl9_3),
% 2.91/0.79    inference(avatar_component_clause,[],[f78])).
% 2.91/0.79  fof(f78,plain,(
% 2.91/0.79    spl9_3 <=> k1_xboole_0 = sK1),
% 2.91/0.79    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 2.91/0.79  fof(f231,plain,(
% 2.91/0.79    k1_xboole_0 = sK1 | ~spl9_8),
% 2.91/0.79    inference(resolution,[],[f203,f53])).
% 2.91/0.79  fof(f53,plain,(
% 2.91/0.79    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 2.91/0.79    inference(cnf_transformation,[],[f36])).
% 2.91/0.79  fof(f36,plain,(
% 2.91/0.79    ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0)),
% 2.91/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f35])).
% 2.91/0.79  fof(f35,plain,(
% 2.91/0.79    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 2.91/0.79    introduced(choice_axiom,[])).
% 2.91/0.79  fof(f21,plain,(
% 2.91/0.79    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.91/0.79    inference(ennf_transformation,[],[f3])).
% 2.91/0.79  fof(f3,axiom,(
% 2.91/0.79    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.91/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.91/0.79  fof(f203,plain,(
% 2.91/0.79    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl9_8),
% 2.91/0.79    inference(avatar_component_clause,[],[f202])).
% 2.91/0.79  fof(f202,plain,(
% 2.91/0.79    spl9_8 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 2.91/0.79    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 2.91/0.79  fof(f227,plain,(
% 2.91/0.79    spl9_2 | ~spl9_7),
% 2.91/0.79    inference(avatar_contradiction_clause,[],[f226])).
% 2.91/0.79  fof(f226,plain,(
% 2.91/0.79    $false | (spl9_2 | ~spl9_7)),
% 2.91/0.79    inference(subsumption_resolution,[],[f224,f74])).
% 2.91/0.79  fof(f74,plain,(
% 2.91/0.79    k1_xboole_0 != sK0 | spl9_2),
% 2.91/0.79    inference(avatar_component_clause,[],[f72])).
% 2.91/0.79  fof(f72,plain,(
% 2.91/0.79    spl9_2 <=> k1_xboole_0 = sK0),
% 2.91/0.79    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 2.91/0.79  fof(f224,plain,(
% 2.91/0.79    k1_xboole_0 = sK0 | ~spl9_7),
% 2.91/0.79    inference(resolution,[],[f200,f53])).
% 2.91/0.79  fof(f200,plain,(
% 2.91/0.79    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl9_7),
% 2.91/0.79    inference(avatar_component_clause,[],[f199])).
% 2.91/0.79  fof(f199,plain,(
% 2.91/0.79    spl9_7 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 2.91/0.79    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 2.91/0.79  fof(f220,plain,(
% 2.91/0.79    spl9_1 | ~spl9_3 | ~spl9_5),
% 2.91/0.79    inference(avatar_contradiction_clause,[],[f219])).
% 2.91/0.79  fof(f219,plain,(
% 2.91/0.79    $false | (spl9_1 | ~spl9_3 | ~spl9_5)),
% 2.91/0.79    inference(subsumption_resolution,[],[f218,f153])).
% 2.91/0.79  fof(f153,plain,(
% 2.91/0.79    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl9_5),
% 2.91/0.79    inference(resolution,[],[f151,f53])).
% 2.91/0.79  fof(f151,plain,(
% 2.91/0.79    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) ) | ~spl9_5),
% 2.91/0.79    inference(resolution,[],[f65,f100])).
% 2.91/0.79  fof(f100,plain,(
% 2.91/0.79    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl9_5),
% 2.91/0.79    inference(avatar_component_clause,[],[f99])).
% 2.91/0.79  fof(f99,plain,(
% 2.91/0.79    spl9_5 <=> ! [X2] : ~r2_hidden(X2,k1_xboole_0)),
% 2.91/0.79    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 2.91/0.79  fof(f65,plain,(
% 2.91/0.79    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.91/0.79    inference(equality_resolution,[],[f46])).
% 2.91/0.79  fof(f46,plain,(
% 2.91/0.79    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.91/0.79    inference(cnf_transformation,[],[f34])).
% 2.91/0.79  fof(f34,plain,(
% 2.91/0.79    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.91/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f30,f33,f32,f31])).
% 2.91/0.79  fof(f31,plain,(
% 2.91/0.79    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.91/0.79    introduced(choice_axiom,[])).
% 2.91/0.79  fof(f32,plain,(
% 2.91/0.79    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))),
% 2.91/0.79    introduced(choice_axiom,[])).
% 2.91/0.79  fof(f33,plain,(
% 2.91/0.79    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 2.91/0.79    introduced(choice_axiom,[])).
% 2.91/0.79  fof(f30,plain,(
% 2.91/0.79    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.91/0.79    inference(rectify,[],[f29])).
% 2.91/0.79  fof(f29,plain,(
% 2.91/0.79    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.91/0.79    inference(nnf_transformation,[],[f14])).
% 2.91/0.79  fof(f14,axiom,(
% 2.91/0.79    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.91/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 2.91/0.79  fof(f218,plain,(
% 2.91/0.79    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl9_1 | ~spl9_3)),
% 2.91/0.79    inference(forward_demodulation,[],[f70,f80])).
% 2.91/0.79  fof(f80,plain,(
% 2.91/0.79    k1_xboole_0 = sK1 | ~spl9_3),
% 2.91/0.79    inference(avatar_component_clause,[],[f78])).
% 2.91/0.79  fof(f70,plain,(
% 2.91/0.79    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl9_1),
% 2.91/0.79    inference(avatar_component_clause,[],[f68])).
% 2.91/0.79  fof(f68,plain,(
% 2.91/0.79    spl9_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 2.91/0.79    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 2.91/0.79  fof(f213,plain,(
% 2.91/0.79    ~spl9_5 | spl9_9),
% 2.91/0.79    inference(avatar_contradiction_clause,[],[f212])).
% 2.91/0.79  fof(f212,plain,(
% 2.91/0.79    $false | (~spl9_5 | spl9_9)),
% 2.91/0.79    inference(unit_resulting_resolution,[],[f176,f210,f53])).
% 2.91/0.79  fof(f210,plain,(
% 2.91/0.79    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl9_9),
% 2.91/0.79    inference(avatar_component_clause,[],[f208])).
% 2.91/0.79  fof(f208,plain,(
% 2.91/0.79    spl9_9 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 2.91/0.79    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 2.91/0.79  fof(f176,plain,(
% 2.91/0.79    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) ) | ~spl9_5),
% 2.91/0.79    inference(resolution,[],[f66,f100])).
% 2.91/0.79  fof(f66,plain,(
% 2.91/0.79    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.91/0.79    inference(equality_resolution,[],[f45])).
% 2.91/0.79  fof(f45,plain,(
% 2.91/0.79    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.91/0.79    inference(cnf_transformation,[],[f34])).
% 2.91/0.79  fof(f211,plain,(
% 2.91/0.79    ~spl9_9 | spl9_1 | ~spl9_2),
% 2.91/0.79    inference(avatar_split_clause,[],[f206,f72,f68,f208])).
% 2.91/0.79  fof(f206,plain,(
% 2.91/0.79    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl9_1 | ~spl9_2)),
% 2.91/0.79    inference(forward_demodulation,[],[f70,f73])).
% 2.91/0.79  fof(f73,plain,(
% 2.91/0.79    k1_xboole_0 = sK0 | ~spl9_2),
% 2.91/0.79    inference(avatar_component_clause,[],[f72])).
% 2.91/0.79  fof(f204,plain,(
% 2.91/0.79    spl9_7 | spl9_8 | ~spl9_1 | ~spl9_5),
% 2.91/0.79    inference(avatar_split_clause,[],[f197,f99,f68,f202,f199])).
% 2.91/0.79  fof(f197,plain,(
% 2.91/0.79    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | (~spl9_1 | ~spl9_5)),
% 2.91/0.79    inference(subsumption_resolution,[],[f191,f100])).
% 2.91/0.79  fof(f191,plain,(
% 2.91/0.79    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl9_1),
% 2.91/0.79    inference(superposition,[],[f44,f69])).
% 2.91/0.79  fof(f69,plain,(
% 2.91/0.79    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl9_1),
% 2.91/0.79    inference(avatar_component_clause,[],[f68])).
% 2.91/0.79  fof(f44,plain,(
% 2.91/0.79    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 2.91/0.79    inference(cnf_transformation,[],[f28])).
% 2.91/0.79  fof(f28,plain,(
% 2.91/0.79    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.91/0.79    inference(flattening,[],[f27])).
% 2.91/0.79  fof(f27,plain,(
% 2.91/0.79    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.91/0.79    inference(nnf_transformation,[],[f16])).
% 2.91/0.79  fof(f16,axiom,(
% 2.91/0.79    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.91/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 2.91/0.79  fof(f105,plain,(
% 2.91/0.79    ~spl9_4),
% 2.91/0.79    inference(avatar_contradiction_clause,[],[f102])).
% 2.91/0.79  fof(f102,plain,(
% 2.91/0.79    $false | ~spl9_4),
% 2.91/0.79    inference(unit_resulting_resolution,[],[f55,f97])).
% 2.91/0.79  fof(f97,plain,(
% 2.91/0.79    ( ! [X0,X1] : (~r1_xboole_0(X0,X1)) ) | ~spl9_4),
% 2.91/0.79    inference(avatar_component_clause,[],[f96])).
% 2.91/0.79  fof(f96,plain,(
% 2.91/0.79    spl9_4 <=> ! [X1,X0] : ~r1_xboole_0(X0,X1)),
% 2.91/0.79    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 2.91/0.79  fof(f55,plain,(
% 2.91/0.79    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.91/0.79    inference(cnf_transformation,[],[f5])).
% 2.91/0.79  fof(f5,axiom,(
% 2.91/0.79    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.91/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.91/0.79  fof(f101,plain,(
% 2.91/0.79    spl9_4 | spl9_5),
% 2.91/0.79    inference(avatar_split_clause,[],[f94,f99,f96])).
% 2.91/0.79  fof(f94,plain,(
% 2.91/0.79    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 2.91/0.79    inference(duplicate_literal_removal,[],[f93])).
% 2.91/0.79  fof(f93,plain,(
% 2.91/0.79    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X1)) )),
% 2.91/0.79    inference(superposition,[],[f57,f92])).
% 2.91/0.79  fof(f92,plain,(
% 2.91/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.91/0.79    inference(resolution,[],[f57,f53])).
% 2.91/0.79  fof(f57,plain,(
% 2.91/0.79    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.91/0.79    inference(cnf_transformation,[],[f38])).
% 2.91/0.79  fof(f38,plain,(
% 2.91/0.79    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.91/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f37])).
% 2.91/0.79  fof(f37,plain,(
% 2.91/0.79    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)))),
% 2.91/0.79    introduced(choice_axiom,[])).
% 2.91/0.79  fof(f22,plain,(
% 2.91/0.79    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.91/0.79    inference(ennf_transformation,[],[f19])).
% 2.91/0.79  fof(f19,plain,(
% 2.91/0.79    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.91/0.79    inference(rectify,[],[f2])).
% 2.91/0.79  fof(f2,axiom,(
% 2.91/0.79    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.91/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.91/0.79  fof(f83,plain,(
% 2.91/0.79    ~spl9_3 | ~spl9_1),
% 2.91/0.79    inference(avatar_split_clause,[],[f82,f68,f78])).
% 2.91/0.79  fof(f82,plain,(
% 2.91/0.79    k1_xboole_0 != sK1 | ~spl9_1),
% 2.91/0.79    inference(subsumption_resolution,[],[f41,f69])).
% 2.91/0.79  fof(f41,plain,(
% 2.91/0.79    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 2.91/0.79    inference(cnf_transformation,[],[f26])).
% 2.91/0.79  fof(f26,plain,(
% 2.91/0.79    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 2.91/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 2.91/0.79  fof(f25,plain,(
% 2.91/0.79    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 2.91/0.79    introduced(choice_axiom,[])).
% 2.91/0.79  fof(f24,plain,(
% 2.91/0.79    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.91/0.79    inference(flattening,[],[f23])).
% 2.91/0.79  fof(f23,plain,(
% 2.91/0.79    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.91/0.79    inference(nnf_transformation,[],[f20])).
% 2.91/0.79  fof(f20,plain,(
% 2.91/0.79    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.91/0.79    inference(ennf_transformation,[],[f18])).
% 2.91/0.79  fof(f18,negated_conjecture,(
% 2.91/0.79    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.91/0.79    inference(negated_conjecture,[],[f17])).
% 2.91/0.79  fof(f17,conjecture,(
% 2.91/0.79    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.91/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.91/0.79  fof(f81,plain,(
% 2.91/0.79    spl9_2 | spl9_3 | spl9_1),
% 2.91/0.79    inference(avatar_split_clause,[],[f76,f68,f78,f72])).
% 2.91/0.79  fof(f76,plain,(
% 2.91/0.79    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl9_1),
% 2.91/0.79    inference(subsumption_resolution,[],[f39,f70])).
% 2.91/0.79  fof(f39,plain,(
% 2.91/0.79    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 2.91/0.79    inference(cnf_transformation,[],[f26])).
% 2.91/0.79  fof(f75,plain,(
% 2.91/0.79    ~spl9_1 | ~spl9_2),
% 2.91/0.79    inference(avatar_split_clause,[],[f40,f72,f68])).
% 2.91/0.79  fof(f40,plain,(
% 2.91/0.79    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 2.91/0.79    inference(cnf_transformation,[],[f26])).
% 2.91/0.79  % SZS output end Proof for theBenchmark
% 2.91/0.79  % (14157)------------------------------
% 2.91/0.79  % (14157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.91/0.79  % (14157)Termination reason: Refutation
% 2.91/0.79  
% 2.91/0.79  % (14157)Memory used [KB]: 10874
% 2.91/0.79  % (14157)Time elapsed: 0.138 s
% 2.91/0.79  % (14157)------------------------------
% 2.91/0.79  % (14157)------------------------------
% 2.91/0.80  % (14098)Success in time 0.428 s
%------------------------------------------------------------------------------

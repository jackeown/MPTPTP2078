%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 180 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  294 ( 732 expanded)
%              Number of equality atoms :   67 ( 127 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f319,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f152,f170,f187,f195,f201,f205,f288,f316,f318])).

fof(f318,plain,
    ( spl8_5
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f236,f147,f185])).

fof(f185,plain,
    ( spl8_5
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f147,plain,
    ( spl8_2
  <=> r2_hidden(sK1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f236,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f148,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK2(X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f18])).

fof(f18,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f148,plain,
    ( r2_hidden(sK1(sK0,sK0),sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f316,plain,
    ( ~ spl8_5
    | ~ spl8_19 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f186,f286])).

fof(f286,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl8_19
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f186,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f185])).

fof(f288,plain,
    ( spl8_19
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f280,f203,f199,f285])).

fof(f199,plain,
    ( spl8_7
  <=> r2_hidden(sK1(sK2(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f203,plain,
    ( spl8_8
  <=> r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(sK2(sK0),sK0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f204,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK2(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f204,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f203])).

fof(f205,plain,
    ( spl8_8
    | spl8_6 ),
    inference(avatar_split_clause,[],[f197,f193,f203])).

fof(f193,plain,
    ( spl8_6
  <=> r1_xboole_0(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f197,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
    | spl8_6 ),
    inference(resolution,[],[f194,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f194,plain,
    ( ~ r1_xboole_0(sK2(sK0),sK0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f193])).

fof(f201,plain,
    ( spl8_7
    | spl8_6 ),
    inference(avatar_split_clause,[],[f196,f193,f199])).

fof(f196,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
    | spl8_6 ),
    inference(resolution,[],[f194,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f195,plain,
    ( ~ spl8_6
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f188,f185,f193])).

fof(f188,plain,
    ( ~ r1_xboole_0(sK2(sK0),sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f186,f27])).

fof(f27,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f187,plain,
    ( spl8_5
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f183,f167,f185])).

fof(f167,plain,
    ( spl8_4
  <=> ! [X19] : ~ r1_xboole_0(sK3(sK0,X19,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f183,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f178,f35])).

fof(f178,plain,
    ( ! [X0] : r2_hidden(sK1(sK3(sK0,X0,sK0),sK0),sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f168,f30])).

fof(f168,plain,
    ( ! [X19] : ~ r1_xboole_0(sK3(sK0,X19,sK0),sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f167])).

fof(f170,plain,
    ( spl8_4
    | spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f165,f150,f53,f167])).

fof(f53,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f150,plain,
    ( spl8_3
  <=> ! [X1,X0] :
        ( k3_setfam_1(sK0,X0) = X1
        | r2_hidden(sK3(sK0,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f165,plain,
    ( ! [X19] :
        ( k1_xboole_0 = sK0
        | ~ r1_xboole_0(sK3(sK0,X19,sK0),sK0) )
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f160,f156])).

fof(f156,plain,
    ( ! [X9] : k1_xboole_0 = k3_setfam_1(sK0,X9)
    | ~ spl8_3 ),
    inference(resolution,[],[f151,f56])).

fof(f56,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f28,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f151,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X1)
        | k3_setfam_1(sK0,X0) = X1 )
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f150])).

fof(f160,plain,
    ( ! [X19] :
        ( sK0 = k3_setfam_1(sK0,X19)
        | ~ r1_xboole_0(sK3(sK0,X19,sK0),sK0) )
    | ~ spl8_3 ),
    inference(resolution,[],[f151,f27])).

fof(f152,plain,
    ( spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f145,f150,f147])).

fof(f145,plain,(
    ! [X0,X1] :
      ( k3_setfam_1(sK0,X0) = X1
      | r2_hidden(sK3(sK0,X0,X1),X1)
      | r2_hidden(sK1(sK0,sK0),sK0) ) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( k3_setfam_1(sK0,X0) = X1
      | r2_hidden(sK3(sK0,X0,X1),X1)
      | r2_hidden(sK1(sK0,sK0),sK0)
      | k3_setfam_1(sK0,X0) = X1
      | r2_hidden(sK3(sK0,X0,X1),X1) ) ),
    inference(resolution,[],[f118,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(sK4(sK0,X0,X1),sK0),sK0)
      | k3_setfam_1(sK0,X0) = X1
      | r2_hidden(sK3(sK0,X0,X1),X1) ) ),
    inference(resolution,[],[f67,f30])).

fof(f67,plain,(
    ! [X26,X27] :
      ( ~ r1_xboole_0(sK4(sK0,X26,X27),sK0)
      | r2_hidden(sK3(sK0,X26,X27),X27)
      | k3_setfam_1(sK0,X26) = X27 ) ),
    inference(resolution,[],[f41,f27])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | k3_setfam_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k3_xboole_0(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( sK3(X0,X1,X2) = k3_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2))
              & r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k3_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k3_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X1)
                & r2_hidden(sK6(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k3_xboole_0(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k3_xboole_0(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k3_xboole_0(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k3_xboole_0(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k3_xboole_0(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k3_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k3_xboole_0(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k3_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k3_xboole_0(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k3_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k3_xboole_0(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k3_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k3_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k3_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_setfam_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK1(sK4(sK0,X0,X1),sK0),X2)
      | k3_setfam_1(sK0,X0) = X1
      | r2_hidden(sK3(sK0,X0,X1),X1)
      | r2_hidden(sK1(X2,sK0),sK0) ) ),
    inference(resolution,[],[f73,f30])).

fof(f73,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_xboole_0(X8,sK0)
      | r2_hidden(sK3(sK0,X6,X7),X7)
      | k3_setfam_1(sK0,X6) = X7
      | ~ r2_hidden(sK1(sK4(sK0,X6,X7),sK0),X8) ) ),
    inference(resolution,[],[f69,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:34:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (28007)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (28007)Refutation not found, incomplete strategy% (28007)------------------------------
% 0.21/0.47  % (28007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (28021)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (28013)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (28007)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (28007)Memory used [KB]: 10618
% 0.21/0.49  % (28007)Time elapsed: 0.052 s
% 0.21/0.49  % (28007)------------------------------
% 0.21/0.49  % (28007)------------------------------
% 0.21/0.49  % (28011)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (28020)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (28019)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (28025)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (28017)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (28010)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (28018)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (28026)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (28022)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (28024)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.53  % (28023)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  % (28012)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.54  % (28006)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (28009)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (28008)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.54  % (28006)Refutation not found, incomplete strategy% (28006)------------------------------
% 0.21/0.54  % (28006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28006)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28006)Memory used [KB]: 6140
% 0.21/0.54  % (28006)Time elapsed: 0.114 s
% 0.21/0.54  % (28006)------------------------------
% 0.21/0.54  % (28006)------------------------------
% 0.21/0.54  % (28009)Refutation not found, incomplete strategy% (28009)------------------------------
% 0.21/0.54  % (28009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28009)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28009)Memory used [KB]: 10618
% 0.21/0.54  % (28009)Time elapsed: 0.113 s
% 0.21/0.54  % (28009)------------------------------
% 0.21/0.54  % (28009)------------------------------
% 0.21/0.54  % (28014)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.54  % (28016)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.55  % (28015)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.55  % (28016)Refutation not found, incomplete strategy% (28016)------------------------------
% 0.21/0.55  % (28016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28016)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28016)Memory used [KB]: 6140
% 0.21/0.55  % (28016)Time elapsed: 0.119 s
% 0.21/0.55  % (28016)------------------------------
% 0.21/0.55  % (28016)------------------------------
% 0.21/0.55  % (28026)Refutation not found, incomplete strategy% (28026)------------------------------
% 0.21/0.55  % (28026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28026)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28026)Memory used [KB]: 10618
% 0.21/0.55  % (28026)Time elapsed: 0.133 s
% 0.21/0.55  % (28026)------------------------------
% 0.21/0.55  % (28026)------------------------------
% 0.21/0.56  % (28012)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f319,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f55,f152,f170,f187,f195,f201,f205,f288,f316,f318])).
% 0.21/0.57  fof(f318,plain,(
% 0.21/0.57    spl8_5 | ~spl8_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f236,f147,f185])).
% 0.21/0.57  fof(f185,plain,(
% 0.21/0.57    spl8_5 <=> r2_hidden(sK2(sK0),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    spl8_2 <=> r2_hidden(sK1(sK0,sK0),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.57  fof(f236,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0),sK0) | ~spl8_2),
% 0.21/0.57    inference(resolution,[],[f148,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.57  fof(f148,plain,(
% 0.21/0.57    r2_hidden(sK1(sK0,sK0),sK0) | ~spl8_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f147])).
% 0.21/0.57  fof(f316,plain,(
% 0.21/0.57    ~spl8_5 | ~spl8_19),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f309])).
% 0.21/0.57  fof(f309,plain,(
% 0.21/0.57    $false | (~spl8_5 | ~spl8_19)),
% 0.21/0.57    inference(subsumption_resolution,[],[f186,f286])).
% 0.21/0.57  fof(f286,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl8_19),
% 0.21/0.57    inference(avatar_component_clause,[],[f285])).
% 0.21/0.57  fof(f285,plain,(
% 0.21/0.57    spl8_19 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.57  fof(f186,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0),sK0) | ~spl8_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f185])).
% 0.21/0.57  fof(f288,plain,(
% 0.21/0.57    spl8_19 | ~spl8_7 | ~spl8_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f280,f203,f199,f285])).
% 0.21/0.57  fof(f199,plain,(
% 0.21/0.57    spl8_7 <=> r2_hidden(sK1(sK2(sK0),sK0),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.57  fof(f203,plain,(
% 0.21/0.57    spl8_8 <=> r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.57  fof(f280,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(sK1(sK2(sK0),sK0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl8_8),
% 0.21/0.57    inference(resolution,[],[f204,f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f204,plain,(
% 0.21/0.57    r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | ~spl8_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f203])).
% 0.21/0.57  fof(f205,plain,(
% 0.21/0.57    spl8_8 | spl8_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f197,f193,f203])).
% 0.21/0.57  fof(f193,plain,(
% 0.21/0.57    spl8_6 <=> r1_xboole_0(sK2(sK0),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.57  fof(f197,plain,(
% 0.21/0.57    r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | spl8_6),
% 0.21/0.57    inference(resolution,[],[f194,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,plain,(
% 0.21/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(rectify,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.57  fof(f194,plain,(
% 0.21/0.57    ~r1_xboole_0(sK2(sK0),sK0) | spl8_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f193])).
% 0.21/0.57  fof(f201,plain,(
% 0.21/0.57    spl8_7 | spl8_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f196,f193,f199])).
% 0.21/0.57  fof(f196,plain,(
% 0.21/0.57    r2_hidden(sK1(sK2(sK0),sK0),sK0) | spl8_6),
% 0.21/0.57    inference(resolution,[],[f194,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f195,plain,(
% 0.21/0.57    ~spl8_6 | ~spl8_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f188,f185,f193])).
% 0.21/0.57  fof(f188,plain,(
% 0.21/0.57    ~r1_xboole_0(sK2(sK0),sK0) | ~spl8_5),
% 0.21/0.57    inference(resolution,[],[f186,f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f9,plain,(
% 0.21/0.57    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,negated_conjecture,(
% 0.21/0.57    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.57    inference(negated_conjecture,[],[f6])).
% 0.21/0.57  fof(f6,conjecture,(
% 0.21/0.57    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.21/0.57  fof(f187,plain,(
% 0.21/0.57    spl8_5 | ~spl8_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f183,f167,f185])).
% 0.21/0.57  fof(f167,plain,(
% 0.21/0.57    spl8_4 <=> ! [X19] : ~r1_xboole_0(sK3(sK0,X19,sK0),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.57  fof(f183,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0),sK0) | ~spl8_4),
% 0.21/0.57    inference(resolution,[],[f178,f35])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(sK1(sK3(sK0,X0,sK0),sK0),sK0)) ) | ~spl8_4),
% 0.21/0.57    inference(resolution,[],[f168,f30])).
% 0.21/0.57  fof(f168,plain,(
% 0.21/0.57    ( ! [X19] : (~r1_xboole_0(sK3(sK0,X19,sK0),sK0)) ) | ~spl8_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f167])).
% 0.21/0.57  fof(f170,plain,(
% 0.21/0.57    spl8_4 | spl8_1 | ~spl8_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f165,f150,f53,f167])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    spl8_1 <=> k1_xboole_0 = sK0),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.57  fof(f150,plain,(
% 0.21/0.57    spl8_3 <=> ! [X1,X0] : (k3_setfam_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.57  fof(f165,plain,(
% 0.21/0.57    ( ! [X19] : (k1_xboole_0 = sK0 | ~r1_xboole_0(sK3(sK0,X19,sK0),sK0)) ) | ~spl8_3),
% 0.21/0.57    inference(forward_demodulation,[],[f160,f156])).
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    ( ! [X9] : (k1_xboole_0 = k3_setfam_1(sK0,X9)) ) | ~spl8_3),
% 0.21/0.57    inference(resolution,[],[f151,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(superposition,[],[f28,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.57    inference(nnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.57  fof(f151,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X1) | k3_setfam_1(sK0,X0) = X1) ) | ~spl8_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f150])).
% 0.21/0.57  fof(f160,plain,(
% 0.21/0.57    ( ! [X19] : (sK0 = k3_setfam_1(sK0,X19) | ~r1_xboole_0(sK3(sK0,X19,sK0),sK0)) ) | ~spl8_3),
% 0.21/0.57    inference(resolution,[],[f151,f27])).
% 0.21/0.57  fof(f152,plain,(
% 0.21/0.57    spl8_2 | spl8_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f145,f150,f147])).
% 0.21/0.57  fof(f145,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_setfam_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1) | r2_hidden(sK1(sK0,sK0),sK0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f142])).
% 0.21/0.57  fof(f142,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_setfam_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1) | r2_hidden(sK1(sK0,sK0),sK0) | k3_setfam_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1)) )),
% 0.21/0.57    inference(resolution,[],[f118,f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK1(sK4(sK0,X0,X1),sK0),sK0) | k3_setfam_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1)) )),
% 0.21/0.57    inference(resolution,[],[f67,f30])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X26,X27] : (~r1_xboole_0(sK4(sK0,X26,X27),sK0) | r2_hidden(sK3(sK0,X26,X27),X27) | k3_setfam_1(sK0,X26) = X27) )),
% 0.21/0.57    inference(resolution,[],[f41,f27])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | k3_setfam_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k3_setfam_1(X0,X1) = X2 | ((! [X4,X5] : (k3_xboole_0(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k3_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k3_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k3_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k3_setfam_1(X0,X1) != X2))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f21,f24,f23,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k3_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k3_xboole_0(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k3_xboole_0(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k3_xboole_0(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X7,X6] : (k3_xboole_0(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k3_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X8,X1,X0] : (? [X11,X12] : (k3_xboole_0(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k3_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k3_setfam_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k3_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k3_xboole_0(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k3_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k3_xboole_0(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k3_setfam_1(X0,X1) != X2))),
% 0.21/0.57    inference(rectify,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k3_setfam_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k3_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k3_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k3_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k3_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k3_setfam_1(X0,X1) != X2))),
% 0.21/0.57    inference(nnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (k3_setfam_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k3_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_setfam_1)).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK1(sK4(sK0,X0,X1),sK0),X2) | k3_setfam_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1) | r2_hidden(sK1(X2,sK0),sK0)) )),
% 0.21/0.57    inference(resolution,[],[f73,f30])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X6,X8,X7] : (~r1_xboole_0(X8,sK0) | r2_hidden(sK3(sK0,X6,X7),X7) | k3_setfam_1(sK0,X6) = X7 | ~r2_hidden(sK1(sK4(sK0,X6,X7),sK0),X8)) )),
% 0.21/0.57    inference(resolution,[],[f69,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ~spl8_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f26,f53])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    k1_xboole_0 != sK0),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (28012)------------------------------
% 0.21/0.57  % (28012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (28012)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (28012)Memory used [KB]: 10874
% 0.21/0.57  % (28012)Time elapsed: 0.120 s
% 0.21/0.57  % (28012)------------------------------
% 0.21/0.57  % (28012)------------------------------
% 0.21/0.57  % (28005)Success in time 0.203 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0296+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:22 EST 2020

% Result     : Theorem 41.73s
% Output     : Refutation 41.73s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 179 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  398 ( 788 expanded)
%              Number of equality atoms :   78 ( 152 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73942,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1022,f1221,f1226,f1231,f1297,f2604,f2605,f4757,f20950,f21822,f72205,f73098,f73939])).

fof(f73939,plain,
    ( ~ spl30_13
    | ~ spl30_23
    | spl30_747 ),
    inference(avatar_contradiction_clause,[],[f73938])).

fof(f73938,plain,
    ( $false
    | ~ spl30_13
    | ~ spl30_23
    | spl30_747 ),
    inference(subsumption_resolution,[],[f73896,f20947])).

fof(f20947,plain,
    ( ~ r2_hidden(sK14(sK1,sK2,sK0),sK4)
    | spl30_747 ),
    inference(avatar_component_clause,[],[f20945])).

fof(f20945,plain,
    ( spl30_747
  <=> r2_hidden(sK14(sK1,sK2,sK0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_747])])).

fof(f73896,plain,
    ( r2_hidden(sK14(sK1,sK2,sK0),sK4)
    | ~ spl30_13
    | ~ spl30_23 ),
    inference(unit_resulting_resolution,[],[f1287,f4739])).

fof(f4739,plain,
    ( ! [X14,X15] :
        ( r2_hidden(sK14(sK1,sK2,sK0),X15)
        | ~ r2_hidden(sK0,k2_zfmisc_1(X14,X15)) )
    | ~ spl30_13 ),
    inference(superposition,[],[f768,f1220])).

fof(f1220,plain,
    ( sK0 = k4_tarski(sK13(sK1,sK2,sK0),sK14(sK1,sK2,sK0))
    | ~ spl30_13 ),
    inference(avatar_component_clause,[],[f1218])).

fof(f1218,plain,
    ( spl30_13
  <=> sK0 = k4_tarski(sK13(sK1,sK2,sK0),sK14(sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_13])])).

fof(f768,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f594])).

fof(f594,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f593])).

fof(f593,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f310])).

fof(f310,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f1287,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
    | ~ spl30_23 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f1285,plain,
    ( spl30_23
  <=> r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_23])])).

fof(f73098,plain,
    ( spl30_799
    | ~ spl30_108
    | ~ spl30_1983 ),
    inference(avatar_split_clause,[],[f72906,f72189,f2601,f21817])).

fof(f21817,plain,
    ( spl30_799
  <=> r2_hidden(sK13(sK1,sK2,sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_799])])).

fof(f2601,plain,
    ( spl30_108
  <=> r2_hidden(sK18(sK3,sK4,sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_108])])).

fof(f72189,plain,
    ( spl30_1983
  <=> sK13(sK1,sK2,sK0) = sK18(sK3,sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_1983])])).

fof(f72906,plain,
    ( r2_hidden(sK13(sK1,sK2,sK0),sK3)
    | ~ spl30_108
    | ~ spl30_1983 ),
    inference(backward_demodulation,[],[f2603,f72191])).

fof(f72191,plain,
    ( sK13(sK1,sK2,sK0) = sK18(sK3,sK4,sK0)
    | ~ spl30_1983 ),
    inference(avatar_component_clause,[],[f72189])).

fof(f2603,plain,
    ( r2_hidden(sK18(sK3,sK4,sK0),sK3)
    | ~ spl30_108 ),
    inference(avatar_component_clause,[],[f2601])).

fof(f72205,plain,
    ( spl30_1983
    | ~ spl30_13
    | ~ spl30_106 ),
    inference(avatar_split_clause,[],[f72185,f2591,f1218,f72189])).

fof(f2591,plain,
    ( spl30_106
  <=> sK0 = k4_tarski(sK18(sK3,sK4,sK0),sK19(sK3,sK4,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_106])])).

fof(f72185,plain,
    ( sK13(sK1,sK2,sK0) = sK18(sK3,sK4,sK0)
    | ~ spl30_13
    | ~ spl30_106 ),
    inference(trivial_inequality_removal,[],[f72184])).

fof(f72184,plain,
    ( sK0 != sK0
    | sK13(sK1,sK2,sK0) = sK18(sK3,sK4,sK0)
    | ~ spl30_13
    | ~ spl30_106 ),
    inference(superposition,[],[f4731,f2593])).

fof(f2593,plain,
    ( sK0 = k4_tarski(sK18(sK3,sK4,sK0),sK19(sK3,sK4,sK0))
    | ~ spl30_106 ),
    inference(avatar_component_clause,[],[f2591])).

fof(f4731,plain,
    ( ! [X0,X1] :
        ( k4_tarski(X0,X1) != sK0
        | sK13(sK1,sK2,sK0) = X0 )
    | ~ spl30_13 ),
    inference(superposition,[],[f644,f1220])).

fof(f644,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f402])).

fof(f402,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f339])).

fof(f339,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f21822,plain,
    ( ~ spl30_799
    | ~ spl30_15
    | spl30_179 ),
    inference(avatar_split_clause,[],[f21821,f4754,f1228,f21817])).

fof(f1228,plain,
    ( spl30_15
  <=> r2_hidden(sK13(sK1,sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_15])])).

fof(f4754,plain,
    ( spl30_179
  <=> r2_hidden(sK13(sK1,sK2,sK0),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_179])])).

fof(f21821,plain,
    ( ~ r2_hidden(sK13(sK1,sK2,sK0),sK3)
    | ~ spl30_15
    | spl30_179 ),
    inference(subsumption_resolution,[],[f21703,f1230])).

fof(f1230,plain,
    ( r2_hidden(sK13(sK1,sK2,sK0),sK1)
    | ~ spl30_15 ),
    inference(avatar_component_clause,[],[f1228])).

fof(f21703,plain,
    ( ~ r2_hidden(sK13(sK1,sK2,sK0),sK3)
    | ~ r2_hidden(sK13(sK1,sK2,sK0),sK1)
    | spl30_179 ),
    inference(resolution,[],[f4756,f972])).

fof(f972,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f679])).

fof(f679,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f565])).

fof(f565,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f563,f564])).

fof(f564,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f563,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f562])).

fof(f562,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f561])).

fof(f561,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f4756,plain,
    ( ~ r2_hidden(sK13(sK1,sK2,sK0),k3_xboole_0(sK1,sK3))
    | spl30_179 ),
    inference(avatar_component_clause,[],[f4754])).

fof(f20950,plain,
    ( ~ spl30_747
    | ~ spl30_14
    | spl30_178 ),
    inference(avatar_split_clause,[],[f20949,f4750,f1223,f20945])).

fof(f1223,plain,
    ( spl30_14
  <=> r2_hidden(sK14(sK1,sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_14])])).

fof(f4750,plain,
    ( spl30_178
  <=> r2_hidden(sK14(sK1,sK2,sK0),k3_xboole_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_178])])).

fof(f20949,plain,
    ( ~ r2_hidden(sK14(sK1,sK2,sK0),sK4)
    | ~ spl30_14
    | spl30_178 ),
    inference(subsumption_resolution,[],[f20831,f1225])).

fof(f1225,plain,
    ( r2_hidden(sK14(sK1,sK2,sK0),sK2)
    | ~ spl30_14 ),
    inference(avatar_component_clause,[],[f1223])).

fof(f20831,plain,
    ( ~ r2_hidden(sK14(sK1,sK2,sK0),sK4)
    | ~ r2_hidden(sK14(sK1,sK2,sK0),sK2)
    | spl30_178 ),
    inference(resolution,[],[f4752,f972])).

fof(f4752,plain,
    ( ~ r2_hidden(sK14(sK1,sK2,sK0),k3_xboole_0(sK2,sK4))
    | spl30_178 ),
    inference(avatar_component_clause,[],[f4750])).

fof(f4757,plain,
    ( ~ spl30_178
    | ~ spl30_179
    | ~ spl30_13 ),
    inference(avatar_split_clause,[],[f4748,f1218,f4754,f4750])).

fof(f4748,plain,
    ( ~ r2_hidden(sK13(sK1,sK2,sK0),k3_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK14(sK1,sK2,sK0),k3_xboole_0(sK2,sK4))
    | ~ spl30_13 ),
    inference(trivial_inequality_removal,[],[f4730])).

fof(f4730,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK13(sK1,sK2,sK0),k3_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK14(sK1,sK2,sK0),k3_xboole_0(sK2,sK4))
    | ~ spl30_13 ),
    inference(superposition,[],[f643,f1220])).

fof(f643,plain,(
    ! [X6,X5] :
      ( k4_tarski(X5,X6) != sK0
      | ~ r2_hidden(X5,k3_xboole_0(sK1,sK3))
      | ~ r2_hidden(X6,k3_xboole_0(sK2,sK4)) ) ),
    inference(cnf_transformation,[],[f540])).

fof(f540,plain,
    ( ! [X5,X6] :
        ( ~ r2_hidden(X6,k3_xboole_0(sK2,sK4))
        | ~ r2_hidden(X5,k3_xboole_0(sK1,sK3))
        | k4_tarski(X5,X6) != sK0 )
    & r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f401,f539])).

fof(f539,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ! [X5,X6] :
            ( ~ r2_hidden(X6,k3_xboole_0(X2,X4))
            | ~ r2_hidden(X5,k3_xboole_0(X1,X3))
            | k4_tarski(X5,X6) != X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) )
   => ( ! [X6,X5] :
          ( ~ r2_hidden(X6,k3_xboole_0(sK2,sK4))
          | ~ r2_hidden(X5,k3_xboole_0(sK1,sK3))
          | k4_tarski(X5,X6) != sK0 )
      & r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f401,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6] :
          ( ~ r2_hidden(X6,k3_xboole_0(X2,X4))
          | ~ r2_hidden(X5,k3_xboole_0(X1,X3))
          | k4_tarski(X5,X6) != X0 )
      & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f315])).

fof(f315,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6] :
              ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
                & r2_hidden(X5,k3_xboole_0(X1,X3))
                & k4_tarski(X5,X6) = X0 )
          & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(negated_conjecture,[],[f314])).

fof(f314,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(f2605,plain,
    ( spl30_106
    | ~ spl30_23 ),
    inference(avatar_split_clause,[],[f2389,f1285,f2591])).

fof(f2389,plain,
    ( sK0 = k4_tarski(sK18(sK3,sK4,sK0),sK19(sK3,sK4,sK0))
    | ~ spl30_23 ),
    inference(resolution,[],[f1287,f988])).

fof(f988,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK18(X0,X1,X8),sK19(X0,X1,X8)) = X8 ) ),
    inference(equality_resolution,[],[f772])).

fof(f772,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK18(X0,X1,X8),sK19(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f600])).

fof(f600,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK15(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK15(X0,X1,X2),X2) )
          & ( ( sK15(X0,X1,X2) = k4_tarski(sK16(X0,X1,X2),sK17(X0,X1,X2))
              & r2_hidden(sK17(X0,X1,X2),X1)
              & r2_hidden(sK16(X0,X1,X2),X0) )
            | r2_hidden(sK15(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK18(X0,X1,X8),sK19(X0,X1,X8)) = X8
                & r2_hidden(sK19(X0,X1,X8),X1)
                & r2_hidden(sK18(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17,sK18,sK19])],[f596,f599,f598,f597])).

fof(f597,plain,(
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
              ( k4_tarski(X4,X5) != sK15(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK15(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK15(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK15(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f598,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK15(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK15(X0,X1,X2) = k4_tarski(sK16(X0,X1,X2),sK17(X0,X1,X2))
        & r2_hidden(sK17(X0,X1,X2),X1)
        & r2_hidden(sK16(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f599,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK18(X0,X1,X8),sK19(X0,X1,X8)) = X8
        & r2_hidden(sK19(X0,X1,X8),X1)
        & r2_hidden(sK18(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f596,plain,(
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
    inference(rectify,[],[f595])).

fof(f595,plain,(
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
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f2604,plain,
    ( spl30_108
    | ~ spl30_23 ),
    inference(avatar_split_clause,[],[f2282,f1285,f2601])).

fof(f2282,plain,
    ( r2_hidden(sK18(sK3,sK4,sK0),sK3)
    | ~ spl30_23 ),
    inference(unit_resulting_resolution,[],[f1287,f990])).

fof(f990,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK18(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f770])).

fof(f770,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK18(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f600])).

fof(f1297,plain,
    ( spl30_23
    | ~ spl30_1 ),
    inference(avatar_split_clause,[],[f1114,f1019,f1285])).

fof(f1019,plain,
    ( spl30_1
  <=> r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_1])])).

fof(f1114,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
    | ~ spl30_1 ),
    inference(resolution,[],[f1021,f973])).

fof(f973,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f678])).

fof(f678,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f565])).

fof(f1021,plain,
    ( r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))
    | ~ spl30_1 ),
    inference(avatar_component_clause,[],[f1019])).

fof(f1231,plain,
    ( spl30_15
    | ~ spl30_1 ),
    inference(avatar_split_clause,[],[f1054,f1019,f1228])).

fof(f1054,plain,
    ( r2_hidden(sK13(sK1,sK2,sK0),sK1)
    | ~ spl30_1 ),
    inference(unit_resulting_resolution,[],[f759,f1021,f761])).

fof(f761,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK13(X1,X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f590])).

fof(f590,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK13(X1,X2,X3),sK14(X1,X2,X3)) = X3
        & r2_hidden(sK14(X1,X2,X3),X2)
        & r2_hidden(sK13(X1,X2,X3),X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f440,f589])).

fof(f589,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k4_tarski(sK13(X1,X2,X3),sK14(X1,X2,X3)) = X3
        & r2_hidden(sK14(X1,X2,X3),X2)
        & r2_hidden(sK13(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f440,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f313])).

fof(f313,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f759,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1226,plain,
    ( spl30_14
    | ~ spl30_1 ),
    inference(avatar_split_clause,[],[f1055,f1019,f1223])).

fof(f1055,plain,
    ( r2_hidden(sK14(sK1,sK2,sK0),sK2)
    | ~ spl30_1 ),
    inference(unit_resulting_resolution,[],[f759,f1021,f762])).

fof(f762,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK14(X1,X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f590])).

fof(f1221,plain,
    ( spl30_13
    | ~ spl30_1 ),
    inference(avatar_split_clause,[],[f1056,f1019,f1218])).

fof(f1056,plain,
    ( sK0 = k4_tarski(sK13(sK1,sK2,sK0),sK14(sK1,sK2,sK0))
    | ~ spl30_1 ),
    inference(unit_resulting_resolution,[],[f759,f1021,f763])).

fof(f763,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | k4_tarski(sK13(X1,X2,X3),sK14(X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f590])).

fof(f1022,plain,(
    spl30_1 ),
    inference(avatar_split_clause,[],[f642,f1019])).

fof(f642,plain,(
    r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f540])).
%------------------------------------------------------------------------------

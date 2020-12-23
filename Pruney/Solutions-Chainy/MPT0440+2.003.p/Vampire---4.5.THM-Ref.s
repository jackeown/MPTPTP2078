%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:56 EST 2020

% Result     : Theorem 18.96s
% Output     : Refutation 18.96s
% Verified   : 
% Statistics : Number of formulae       :  320 (1097 expanded)
%              Number of leaves         :   79 ( 454 expanded)
%              Depth                    :   11
%              Number of atoms          :  857 (4083 expanded)
%              Number of equality atoms :  131 (1259 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1094,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f126,f135,f141,f155,f160,f169,f176,f185,f204,f214,f219,f225,f232,f245,f254,f266,f289,f316,f323,f338,f346,f357,f366,f394,f411,f416,f432,f452,f457,f474,f491,f506,f514,f539,f549,f554,f570,f610,f615,f634,f673,f680,f715,f720,f725,f750,f755,f778,f783,f900,f907,f941,f949,f968,f969,f975,f1025,f1033,f1068,f1090])).

fof(f1090,plain,
    ( ~ spl15_2
    | spl15_29
    | ~ spl15_31 ),
    inference(avatar_contradiction_clause,[],[f1075])).

fof(f1075,plain,
    ( $false
    | ~ spl15_2
    | spl15_29
    | ~ spl15_31 ),
    inference(unit_resulting_resolution,[],[f431,f456,f1015])).

fof(f1015,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | sK1 = X0 )
    | ~ spl15_2 ),
    inference(superposition,[],[f307,f125])).

fof(f125,plain,
    ( sK2 = k1_tarski(k4_tarski(sK0,sK1))
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl15_2
  <=> sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f307,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k1_tarski(k4_tarski(X3,X2))))
      | X1 = X2 ) ),
    inference(forward_demodulation,[],[f300,f102])).

fof(f102,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f300,plain,(
    ! [X2,X3,X1] :
      ( X1 = X2
      | ~ r2_hidden(X1,k2_relat_1(k2_zfmisc_1(k1_tarski(X3),k1_tarski(X2)))) ) ),
    inference(resolution,[],[f100,f108])).

fof(f108,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f51,f54,f53,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f456,plain,
    ( r2_hidden(sK11(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl15_31 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl15_31
  <=> r2_hidden(sK11(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_31])])).

fof(f431,plain,
    ( sK1 != sK11(sK1,k2_relat_1(sK2))
    | spl15_29 ),
    inference(avatar_component_clause,[],[f429])).

fof(f429,plain,
    ( spl15_29
  <=> sK1 = sK11(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_29])])).

fof(f1068,plain,
    ( spl15_58
    | ~ spl15_3
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f914,f166,f128,f1065])).

fof(f1065,plain,
    ( spl15_58
  <=> r1_tarski(sK2,k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_58])])).

fof(f128,plain,
    ( spl15_3
  <=> k1_tarski(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f166,plain,
    ( spl15_8
  <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f914,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK2)))
    | ~ spl15_3
    | ~ spl15_8 ),
    inference(superposition,[],[f168,f129])).

fof(f129,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f168,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl15_8 ),
    inference(avatar_component_clause,[],[f166])).

fof(f1033,plain,
    ( spl15_57
    | ~ spl15_35
    | ~ spl15_56 ),
    inference(avatar_split_clause,[],[f1027,f1022,f511,f1030])).

fof(f1030,plain,
    ( spl15_57
  <=> r2_hidden(k4_tarski(sK0,sK6(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_57])])).

fof(f511,plain,
    ( spl15_35
  <=> r2_hidden(k4_tarski(sK5(sK2,sK6(sK2)),sK6(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_35])])).

fof(f1022,plain,
    ( spl15_56
  <=> sK0 = sK5(sK2,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_56])])).

fof(f1027,plain,
    ( r2_hidden(k4_tarski(sK0,sK6(sK2)),sK2)
    | ~ spl15_35
    | ~ spl15_56 ),
    inference(superposition,[],[f513,f1024])).

fof(f1024,plain,
    ( sK0 = sK5(sK2,sK6(sK2))
    | ~ spl15_56 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f513,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK6(sK2)),sK6(sK2)),sK2)
    | ~ spl15_35 ),
    inference(avatar_component_clause,[],[f511])).

fof(f1025,plain,
    ( spl15_56
    | ~ spl15_2
    | ~ spl15_39 ),
    inference(avatar_split_clause,[],[f882,f567,f123,f1022])).

fof(f567,plain,
    ( spl15_39
  <=> r2_hidden(sK5(sK2,sK6(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_39])])).

fof(f882,plain,
    ( sK0 = sK5(sK2,sK6(sK2))
    | ~ spl15_2
    | ~ spl15_39 ),
    inference(unit_resulting_resolution,[],[f569,f875])).

fof(f875,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | sK0 = X0 )
    | ~ spl15_2 ),
    inference(superposition,[],[f284,f125])).

fof(f284,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(k1_tarski(k4_tarski(X5,X6))))
      | X4 = X5 ) ),
    inference(forward_demodulation,[],[f276,f102])).

fof(f276,plain,(
    ! [X6,X4,X5] :
      ( X4 = X5
      | ~ r2_hidden(X4,k1_relat_1(k2_zfmisc_1(k1_tarski(X5),k1_tarski(X6)))) ) ),
    inference(resolution,[],[f99,f110])).

fof(f110,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f61,f64,f63,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f569,plain,
    ( r2_hidden(sK5(sK2,sK6(sK2)),k1_relat_1(sK2))
    | ~ spl15_39 ),
    inference(avatar_component_clause,[],[f567])).

fof(f975,plain,
    ( ~ spl15_55
    | ~ spl15_3
    | spl15_21 ),
    inference(avatar_split_clause,[],[f918,f320,f128,f972])).

fof(f972,plain,
    ( spl15_55
  <=> sK0 = sK11(sK0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_55])])).

fof(f320,plain,
    ( spl15_21
  <=> sK0 = sK11(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_21])])).

fof(f918,plain,
    ( sK0 != sK11(sK0,k1_tarski(sK0))
    | ~ spl15_3
    | spl15_21 ),
    inference(superposition,[],[f322,f129])).

fof(f322,plain,
    ( sK0 != sK11(sK0,k1_relat_1(sK2))
    | spl15_21 ),
    inference(avatar_component_clause,[],[f320])).

fof(f969,plain,(
    spl15_54 ),
    inference(avatar_contradiction_clause,[],[f966])).

fof(f966,plain,
    ( $false
    | spl15_54 ),
    inference(unit_resulting_resolution,[],[f112,f948])).

fof(f948,plain,
    ( ~ r2_hidden(k1_tarski(sK0),k1_tarski(k1_tarski(sK0)))
    | spl15_54 ),
    inference(avatar_component_clause,[],[f946])).

fof(f946,plain,
    ( spl15_54
  <=> r2_hidden(k1_tarski(sK0),k1_tarski(k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_54])])).

fof(f112,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK11(X0,X1) != X0
            | ~ r2_hidden(sK11(X0,X1),X1) )
          & ( sK11(X0,X1) = X0
            | r2_hidden(sK11(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f67,f68])).

fof(f68,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK11(X0,X1) != X0
          | ~ r2_hidden(sK11(X0,X1),X1) )
        & ( sK11(X0,X1) = X0
          | r2_hidden(sK11(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f968,plain,(
    spl15_54 ),
    inference(avatar_contradiction_clause,[],[f967])).

fof(f967,plain,
    ( $false
    | spl15_54 ),
    inference(resolution,[],[f948,f112])).

fof(f949,plain,
    ( ~ spl15_54
    | ~ spl15_3
    | spl15_6 ),
    inference(avatar_split_clause,[],[f912,f152,f128,f946])).

fof(f152,plain,
    ( spl15_6
  <=> r2_hidden(k1_relat_1(sK2),k1_tarski(k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f912,plain,
    ( ~ r2_hidden(k1_tarski(sK0),k1_tarski(k1_tarski(sK0)))
    | ~ spl15_3
    | spl15_6 ),
    inference(superposition,[],[f154,f129])).

fof(f154,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),k1_tarski(k1_tarski(sK0)))
    | spl15_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f941,plain,
    ( spl15_53
    | ~ spl15_2
    | ~ spl15_17 ),
    inference(avatar_split_clause,[],[f881,f251,f123,f938])).

fof(f938,plain,
    ( spl15_53
  <=> sK0 = sK5(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_53])])).

fof(f251,plain,
    ( spl15_17
  <=> r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_17])])).

fof(f881,plain,
    ( sK0 = sK5(sK2,sK1)
    | ~ spl15_2
    | ~ spl15_17 ),
    inference(unit_resulting_resolution,[],[f253,f875])).

fof(f253,plain,
    ( r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | ~ spl15_17 ),
    inference(avatar_component_clause,[],[f251])).

fof(f907,plain,
    ( spl15_52
    | ~ spl15_2
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f883,f229,f123,f904])).

fof(f904,plain,
    ( spl15_52
  <=> sK0 = sK7(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_52])])).

fof(f229,plain,
    ( spl15_15
  <=> r2_hidden(sK7(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f883,plain,
    ( sK0 = sK7(sK2)
    | ~ spl15_2
    | ~ spl15_15 ),
    inference(unit_resulting_resolution,[],[f231,f875])).

fof(f231,plain,
    ( r2_hidden(sK7(sK2),k1_relat_1(sK2))
    | ~ spl15_15 ),
    inference(avatar_component_clause,[],[f229])).

fof(f900,plain,
    ( ~ spl15_2
    | spl15_21
    | ~ spl15_25 ),
    inference(avatar_contradiction_clause,[],[f885])).

fof(f885,plain,
    ( $false
    | ~ spl15_2
    | spl15_21
    | ~ spl15_25 ),
    inference(unit_resulting_resolution,[],[f322,f365,f875])).

fof(f365,plain,
    ( r2_hidden(sK11(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl15_25 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl15_25
  <=> r2_hidden(sK11(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_25])])).

fof(f783,plain,
    ( ~ spl15_51
    | ~ spl15_2
    | spl15_4 ),
    inference(avatar_split_clause,[],[f689,f132,f123,f780])).

fof(f780,plain,
    ( spl15_51
  <=> r2_hidden(k1_tarski(sK1),k1_relat_1(k2_zfmisc_1(k1_tarski(k2_relat_1(sK2)),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_51])])).

fof(f132,plain,
    ( spl15_4
  <=> k1_tarski(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f689,plain,
    ( ~ r2_hidden(k1_tarski(sK1),k1_relat_1(k2_zfmisc_1(k1_tarski(k2_relat_1(sK2)),sK2)))
    | ~ spl15_2
    | spl15_4 ),
    inference(superposition,[],[f617,f206])).

fof(f206,plain,
    ( ! [X0] : k2_zfmisc_1(k1_tarski(X0),sK2) = k1_tarski(k4_tarski(X0,k4_tarski(sK0,sK1)))
    | ~ spl15_2 ),
    inference(superposition,[],[f102,f125])).

fof(f617,plain,
    ( ! [X0] : ~ r2_hidden(k1_tarski(sK1),k1_relat_1(k1_tarski(k4_tarski(k2_relat_1(sK2),X0))))
    | spl15_4 ),
    inference(unit_resulting_resolution,[],[f485,f110])).

fof(f485,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(k1_tarski(sK1),X0),k1_tarski(k4_tarski(k2_relat_1(sK2),X1)))
    | spl15_4 ),
    inference(forward_demodulation,[],[f478,f102])).

fof(f478,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(k1_tarski(sK1),X0),k2_zfmisc_1(k1_tarski(k2_relat_1(sK2)),k1_tarski(X1)))
    | spl15_4 ),
    inference(unit_resulting_resolution,[],[f134,f99])).

fof(f134,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | spl15_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f778,plain,
    ( ~ spl15_50
    | ~ spl15_2
    | spl15_3 ),
    inference(avatar_split_clause,[],[f687,f128,f123,f775])).

fof(f775,plain,
    ( spl15_50
  <=> r2_hidden(k1_tarski(sK0),k1_relat_1(k2_zfmisc_1(k1_tarski(k1_relat_1(sK2)),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_50])])).

fof(f687,plain,
    ( ~ r2_hidden(k1_tarski(sK0),k1_relat_1(k2_zfmisc_1(k1_tarski(k1_relat_1(sK2)),sK2)))
    | ~ spl15_2
    | spl15_3 ),
    inference(superposition,[],[f555,f206])).

fof(f555,plain,
    ( ! [X0] : ~ r2_hidden(k1_tarski(sK0),k1_relat_1(k1_tarski(k4_tarski(k1_relat_1(sK2),X0))))
    | spl15_3 ),
    inference(unit_resulting_resolution,[],[f405,f110])).

fof(f405,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(k1_tarski(sK0),X0),k1_tarski(k4_tarski(k1_relat_1(sK2),X1)))
    | spl15_3 ),
    inference(forward_demodulation,[],[f398,f102])).

fof(f398,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(k1_tarski(sK0),X0),k2_zfmisc_1(k1_tarski(k1_relat_1(sK2)),k1_tarski(X1)))
    | spl15_3 ),
    inference(unit_resulting_resolution,[],[f130,f99])).

fof(f130,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | spl15_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f755,plain,
    ( ~ spl15_49
    | ~ spl15_2
    | spl15_4 ),
    inference(avatar_split_clause,[],[f684,f132,f123,f752])).

fof(f752,plain,
    ( spl15_49
  <=> r2_hidden(k2_relat_1(sK2),k1_relat_1(k2_zfmisc_1(k1_tarski(k1_tarski(sK1)),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_49])])).

fof(f684,plain,
    ( ~ r2_hidden(k2_relat_1(sK2),k1_relat_1(k2_zfmisc_1(k1_tarski(k1_tarski(sK1)),sK2)))
    | ~ spl15_2
    | spl15_4 ),
    inference(superposition,[],[f587,f206])).

fof(f587,plain,
    ( ! [X0] : ~ r2_hidden(k2_relat_1(sK2),k1_relat_1(k1_tarski(k4_tarski(k1_tarski(sK1),X0))))
    | spl15_4 ),
    inference(unit_resulting_resolution,[],[f483,f110])).

fof(f483,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(k2_relat_1(sK2),X0),k1_tarski(k4_tarski(k1_tarski(sK1),X1)))
    | spl15_4 ),
    inference(forward_demodulation,[],[f481,f102])).

fof(f481,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(k2_relat_1(sK2),X0),k2_zfmisc_1(k1_tarski(k1_tarski(sK1)),k1_tarski(X1)))
    | spl15_4 ),
    inference(unit_resulting_resolution,[],[f134,f99])).

fof(f750,plain,
    ( ~ spl15_48
    | ~ spl15_2
    | spl15_3 ),
    inference(avatar_split_clause,[],[f682,f128,f123,f747])).

fof(f747,plain,
    ( spl15_48
  <=> r2_hidden(k1_relat_1(sK2),k1_relat_1(k2_zfmisc_1(k1_tarski(k1_tarski(sK0)),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_48])])).

fof(f682,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k2_zfmisc_1(k1_tarski(k1_tarski(sK0)),sK2)))
    | ~ spl15_2
    | spl15_3 ),
    inference(superposition,[],[f528,f206])).

fof(f528,plain,
    ( ! [X0] : ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k1_tarski(k4_tarski(k1_tarski(sK0),X0))))
    | spl15_3 ),
    inference(unit_resulting_resolution,[],[f403,f110])).

fof(f403,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(k1_relat_1(sK2),X0),k1_tarski(k4_tarski(k1_tarski(sK0),X1)))
    | spl15_3 ),
    inference(forward_demodulation,[],[f401,f102])).

fof(f401,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(k1_relat_1(sK2),X0),k2_zfmisc_1(k1_tarski(k1_tarski(sK0)),k1_tarski(X1)))
    | spl15_3 ),
    inference(unit_resulting_resolution,[],[f130,f99])).

fof(f725,plain,
    ( ~ spl15_47
    | ~ spl15_2
    | spl15_4 ),
    inference(avatar_split_clause,[],[f647,f132,f123,f722])).

fof(f722,plain,
    ( spl15_47
  <=> r2_hidden(k1_tarski(sK1),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k2_relat_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_47])])).

fof(f647,plain,
    ( ~ r2_hidden(k1_tarski(sK1),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k2_relat_1(sK2)))))
    | ~ spl15_2
    | spl15_4 ),
    inference(superposition,[],[f625,f205])).

fof(f205,plain,
    ( ! [X0] : k2_zfmisc_1(sK2,k1_tarski(X0)) = k1_tarski(k4_tarski(k4_tarski(sK0,sK1),X0))
    | ~ spl15_2 ),
    inference(superposition,[],[f102,f125])).

fof(f625,plain,
    ( ! [X0] : ~ r2_hidden(k1_tarski(sK1),k2_relat_1(k1_tarski(k4_tarski(X0,k2_relat_1(sK2)))))
    | spl15_4 ),
    inference(unit_resulting_resolution,[],[f486,f108])).

fof(f486,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,k1_tarski(sK1)),k1_tarski(k4_tarski(X1,k2_relat_1(sK2))))
    | spl15_4 ),
    inference(forward_demodulation,[],[f477,f102])).

fof(f477,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,k1_tarski(sK1)),k2_zfmisc_1(k1_tarski(X1),k1_tarski(k2_relat_1(sK2))))
    | spl15_4 ),
    inference(unit_resulting_resolution,[],[f134,f100])).

fof(f720,plain,
    ( ~ spl15_46
    | ~ spl15_2
    | spl15_3 ),
    inference(avatar_split_clause,[],[f645,f128,f123,f717])).

fof(f717,plain,
    ( spl15_46
  <=> r2_hidden(k1_tarski(sK0),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k1_relat_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_46])])).

fof(f645,plain,
    ( ~ r2_hidden(k1_tarski(sK0),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k1_relat_1(sK2)))))
    | ~ spl15_2
    | spl15_3 ),
    inference(superposition,[],[f571,f205])).

fof(f571,plain,
    ( ! [X0] : ~ r2_hidden(k1_tarski(sK0),k2_relat_1(k1_tarski(k4_tarski(X0,k1_relat_1(sK2)))))
    | spl15_3 ),
    inference(unit_resulting_resolution,[],[f406,f108])).

fof(f406,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,k1_tarski(sK0)),k1_tarski(k4_tarski(X1,k1_relat_1(sK2))))
    | spl15_3 ),
    inference(forward_demodulation,[],[f397,f102])).

fof(f397,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,k1_tarski(sK0)),k2_zfmisc_1(k1_tarski(X1),k1_tarski(k1_relat_1(sK2))))
    | spl15_3 ),
    inference(unit_resulting_resolution,[],[f130,f100])).

fof(f715,plain,
    ( ~ spl15_45
    | ~ spl15_2
    | spl15_4 ),
    inference(avatar_split_clause,[],[f643,f132,f123,f712])).

fof(f712,plain,
    ( spl15_45
  <=> r2_hidden(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k1_tarski(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_45])])).

fof(f643,plain,
    ( ~ r2_hidden(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k1_tarski(sK1)))))
    | ~ spl15_2
    | spl15_4 ),
    inference(superposition,[],[f603,f205])).

fof(f603,plain,
    ( ! [X0] : ~ r2_hidden(k2_relat_1(sK2),k2_relat_1(k1_tarski(k4_tarski(X0,k1_tarski(sK1)))))
    | spl15_4 ),
    inference(unit_resulting_resolution,[],[f484,f108])).

fof(f484,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,k2_relat_1(sK2)),k1_tarski(k4_tarski(X1,k1_tarski(sK1))))
    | spl15_4 ),
    inference(forward_demodulation,[],[f480,f102])).

fof(f480,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,k2_relat_1(sK2)),k2_zfmisc_1(k1_tarski(X1),k1_tarski(k1_tarski(sK1))))
    | spl15_4 ),
    inference(unit_resulting_resolution,[],[f134,f100])).

fof(f680,plain,
    ( ~ spl15_44
    | ~ spl15_2
    | spl15_3 ),
    inference(avatar_split_clause,[],[f641,f128,f123,f677])).

fof(f677,plain,
    ( spl15_44
  <=> r2_hidden(k1_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_44])])).

fof(f641,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k1_tarski(sK0)))))
    | ~ spl15_2
    | spl15_3 ),
    inference(superposition,[],[f540,f205])).

fof(f540,plain,
    ( ! [X0] : ~ r2_hidden(k1_relat_1(sK2),k2_relat_1(k1_tarski(k4_tarski(X0,k1_tarski(sK0)))))
    | spl15_3 ),
    inference(unit_resulting_resolution,[],[f404,f108])).

fof(f404,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,k1_relat_1(sK2)),k1_tarski(k4_tarski(X1,k1_tarski(sK0))))
    | spl15_3 ),
    inference(forward_demodulation,[],[f400,f102])).

fof(f400,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,k1_relat_1(sK2)),k2_zfmisc_1(k1_tarski(X1),k1_tarski(k1_tarski(sK0))))
    | spl15_3 ),
    inference(unit_resulting_resolution,[],[f130,f100])).

fof(f673,plain,
    ( spl15_43
    | ~ spl15_42 ),
    inference(avatar_split_clause,[],[f637,f631,f670])).

fof(f670,plain,
    ( spl15_43
  <=> r2_hidden(sK10(sK2,sK7(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_43])])).

fof(f631,plain,
    ( spl15_42
  <=> r2_hidden(k4_tarski(sK7(sK2),sK10(sK2,sK7(sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_42])])).

fof(f637,plain,
    ( r2_hidden(sK10(sK2,sK7(sK2)),k2_relat_1(sK2))
    | ~ spl15_42 ),
    inference(unit_resulting_resolution,[],[f633,f107])).

fof(f107,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f633,plain,
    ( r2_hidden(k4_tarski(sK7(sK2),sK10(sK2,sK7(sK2))),sK2)
    | ~ spl15_42 ),
    inference(avatar_component_clause,[],[f631])).

fof(f634,plain,
    ( spl15_42
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f257,f229,f631])).

fof(f257,plain,
    ( r2_hidden(k4_tarski(sK7(sK2),sK10(sK2,sK7(sK2))),sK2)
    | ~ spl15_15 ),
    inference(unit_resulting_resolution,[],[f231,f110])).

fof(f615,plain,
    ( spl15_41
    | ~ spl15_38 ),
    inference(avatar_split_clause,[],[f602,f551,f612])).

fof(f612,plain,
    ( spl15_41
  <=> r2_hidden(sK1,k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_41])])).

fof(f551,plain,
    ( spl15_38
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_38])])).

fof(f602,plain,
    ( r2_hidden(sK1,k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl15_38 ),
    inference(unit_resulting_resolution,[],[f553,f107])).

fof(f553,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl15_38 ),
    inference(avatar_component_clause,[],[f551])).

fof(f610,plain,
    ( spl15_40
    | ~ spl15_38 ),
    inference(avatar_split_clause,[],[f601,f551,f607])).

fof(f607,plain,
    ( spl15_40
  <=> r2_hidden(sK0,k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_40])])).

fof(f601,plain,
    ( r2_hidden(sK0,k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl15_38 ),
    inference(unit_resulting_resolution,[],[f553,f109])).

fof(f109,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f570,plain,
    ( spl15_39
    | ~ spl15_35 ),
    inference(avatar_split_clause,[],[f561,f511,f567])).

fof(f561,plain,
    ( r2_hidden(sK5(sK2,sK6(sK2)),k1_relat_1(sK2))
    | ~ spl15_35 ),
    inference(unit_resulting_resolution,[],[f513,f109])).

fof(f554,plain,
    ( spl15_38
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_8
    | ~ spl15_18 ),
    inference(avatar_split_clause,[],[f424,f263,f166,f123,f118,f551])).

fof(f118,plain,
    ( spl15_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f263,plain,
    ( spl15_18
  <=> r2_hidden(k4_tarski(sK0,sK10(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f424,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_8
    | ~ spl15_18 ),
    inference(forward_demodulation,[],[f419,f269])).

fof(f269,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK0,sK10(sK2,sK0))
    | ~ spl15_2
    | ~ spl15_18 ),
    inference(unit_resulting_resolution,[],[f265,f150])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k4_tarski(sK0,sK1) = X0 )
    | ~ spl15_2 ),
    inference(superposition,[],[f113,f125])).

fof(f113,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f265,plain,
    ( r2_hidden(k4_tarski(sK0,sK10(sK2,sK0)),sK2)
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f263])).

fof(f419,plain,
    ( r2_hidden(k4_tarski(sK0,sK10(sK2,sK0)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl15_1
    | ~ spl15_8
    | ~ spl15_18 ),
    inference(unit_resulting_resolution,[],[f120,f168,f265,f103])).

fof(f103,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK13(X0,X1),sK14(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK13(X0,X1),sK14(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f76,f77])).

fof(f77,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK13(X0,X1),sK14(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK13(X0,X1),sK14(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f120,plain,
    ( v1_relat_1(sK2)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f549,plain,
    ( spl15_37
    | ~ spl15_2
    | ~ spl15_18 ),
    inference(avatar_split_clause,[],[f269,f263,f123,f546])).

fof(f546,plain,
    ( spl15_37
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK0,sK10(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_37])])).

fof(f539,plain,
    ( spl15_36
    | ~ spl15_2
    | ~ spl15_16 ),
    inference(avatar_split_clause,[],[f248,f242,f123,f536])).

fof(f536,plain,
    ( spl15_36
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK5(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_36])])).

fof(f242,plain,
    ( spl15_16
  <=> r2_hidden(k4_tarski(sK5(sK2,sK1),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f248,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK5(sK2,sK1),sK1)
    | ~ spl15_2
    | ~ spl15_16 ),
    inference(unit_resulting_resolution,[],[f244,f150])).

fof(f244,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK1),sK1),sK2)
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f242])).

fof(f514,plain,
    ( spl15_35
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f238,f222,f511])).

fof(f222,plain,
    ( spl15_14
  <=> r2_hidden(sK6(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f238,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK6(sK2)),sK6(sK2)),sK2)
    | ~ spl15_14 ),
    inference(unit_resulting_resolution,[],[f224,f108])).

fof(f224,plain,
    ( r2_hidden(sK6(sK2),k2_relat_1(sK2))
    | ~ spl15_14 ),
    inference(avatar_component_clause,[],[f222])).

fof(f506,plain,
    ( spl15_34
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f295,f123,f503])).

fof(f503,plain,
    ( spl15_34
  <=> r2_hidden(k4_tarski(sK0,sK1),k1_relat_1(k2_zfmisc_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_34])])).

fof(f295,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k1_relat_1(k2_zfmisc_1(sK2,sK2)))
    | ~ spl15_2 ),
    inference(superposition,[],[f194,f125])).

fof(f194,plain,
    ( ! [X0] : r2_hidden(k4_tarski(sK0,sK1),k1_relat_1(k2_zfmisc_1(sK2,k1_tarski(X0))))
    | ~ spl15_2 ),
    inference(unit_resulting_resolution,[],[f190,f109])).

fof(f190,plain,
    ( ! [X0] : r2_hidden(k4_tarski(k4_tarski(sK0,sK1),X0),k2_zfmisc_1(sK2,k1_tarski(X0)))
    | ~ spl15_2 ),
    inference(superposition,[],[f115,f125])).

fof(f115,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X0 != X2 ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X1 != X3
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f491,plain,
    ( ~ spl15_33
    | spl15_29 ),
    inference(avatar_split_clause,[],[f439,f429,f488])).

fof(f488,plain,
    ( spl15_33
  <=> r2_hidden(sK1,k1_tarski(sK11(sK1,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_33])])).

fof(f439,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK11(sK1,k2_relat_1(sK2))))
    | spl15_29 ),
    inference(unit_resulting_resolution,[],[f431,f113])).

fof(f474,plain,
    ( spl15_32
    | ~ spl15_4
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f460,f222,f132,f471])).

fof(f471,plain,
    ( spl15_32
  <=> r2_hidden(sK6(sK2),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_32])])).

fof(f460,plain,
    ( r2_hidden(sK6(sK2),k1_tarski(sK1))
    | ~ spl15_4
    | ~ spl15_14 ),
    inference(superposition,[],[f224,f133])).

fof(f133,plain,
    ( k1_tarski(sK1) = k2_relat_1(sK2)
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f457,plain,
    ( spl15_31
    | spl15_4
    | spl15_29 ),
    inference(avatar_split_clause,[],[f436,f429,f132,f454])).

fof(f436,plain,
    ( r2_hidden(sK11(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl15_4
    | spl15_29 ),
    inference(unit_resulting_resolution,[],[f134,f431,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1),X1)
      | sK11(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f452,plain,
    ( ~ spl15_30
    | spl15_29 ),
    inference(avatar_split_clause,[],[f435,f429,f449])).

fof(f449,plain,
    ( spl15_30
  <=> r2_hidden(sK11(sK1,k2_relat_1(sK2)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_30])])).

fof(f435,plain,
    ( ~ r2_hidden(sK11(sK1,k2_relat_1(sK2)),k1_tarski(sK1))
    | spl15_29 ),
    inference(unit_resulting_resolution,[],[f431,f113])).

fof(f432,plain,
    ( ~ spl15_29
    | spl15_4
    | ~ spl15_9 ),
    inference(avatar_split_clause,[],[f379,f173,f132,f429])).

fof(f173,plain,
    ( spl15_9
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_9])])).

fof(f379,plain,
    ( sK1 != sK11(sK1,k2_relat_1(sK2))
    | spl15_4
    | ~ spl15_9 ),
    inference(unit_resulting_resolution,[],[f175,f134,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( sK11(X0,X1) != X0
      | k1_tarski(X0) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(inner_rewriting,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK11(X0,X1) != X0
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f175,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl15_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f416,plain,
    ( ~ spl15_28
    | spl15_4 ),
    inference(avatar_split_clause,[],[f385,f132,f413])).

fof(f413,plain,
    ( spl15_28
  <=> r2_hidden(k1_tarski(sK1),k1_tarski(k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_28])])).

fof(f385,plain,
    ( ~ r2_hidden(k1_tarski(sK1),k1_tarski(k2_relat_1(sK2)))
    | spl15_4 ),
    inference(unit_resulting_resolution,[],[f134,f113])).

fof(f411,plain,
    ( ~ spl15_27
    | spl15_4 ),
    inference(avatar_split_clause,[],[f382,f132,f408])).

fof(f408,plain,
    ( spl15_27
  <=> r2_hidden(k2_relat_1(sK2),k1_tarski(k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_27])])).

fof(f382,plain,
    ( ~ r2_hidden(k2_relat_1(sK2),k1_tarski(k1_tarski(sK1)))
    | spl15_4 ),
    inference(unit_resulting_resolution,[],[f134,f113])).

fof(f394,plain,
    ( spl15_26
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f371,f229,f128,f391])).

fof(f391,plain,
    ( spl15_26
  <=> r2_hidden(sK7(sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_26])])).

fof(f371,plain,
    ( r2_hidden(sK7(sK2),k1_tarski(sK0))
    | ~ spl15_3
    | ~ spl15_15 ),
    inference(superposition,[],[f231,f129])).

fof(f366,plain,
    ( spl15_25
    | spl15_3
    | spl15_21 ),
    inference(avatar_split_clause,[],[f359,f320,f128,f363])).

fof(f359,plain,
    ( r2_hidden(sK11(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))
    | spl15_3
    | spl15_21 ),
    inference(unit_resulting_resolution,[],[f130,f322,f95])).

fof(f357,plain,
    ( spl15_24
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f352,f123,f354])).

fof(f354,plain,
    ( spl15_24
  <=> r2_hidden(sK1,k2_relat_1(k1_relat_1(k2_zfmisc_1(sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_24])])).

fof(f352,plain,
    ( r2_hidden(sK1,k2_relat_1(k1_relat_1(k2_zfmisc_1(sK2,sK2))))
    | ~ spl15_2 ),
    inference(superposition,[],[f293,f125])).

fof(f293,plain,
    ( ! [X0] : r2_hidden(sK1,k2_relat_1(k1_relat_1(k2_zfmisc_1(sK2,k1_tarski(X0)))))
    | ~ spl15_2 ),
    inference(unit_resulting_resolution,[],[f194,f107])).

fof(f346,plain,
    ( ~ spl15_23
    | spl15_21 ),
    inference(avatar_split_clause,[],[f329,f320,f343])).

fof(f343,plain,
    ( spl15_23
  <=> r2_hidden(sK0,k1_tarski(sK11(sK0,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_23])])).

fof(f329,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK11(sK0,k1_relat_1(sK2))))
    | spl15_21 ),
    inference(unit_resulting_resolution,[],[f322,f113])).

fof(f338,plain,
    ( ~ spl15_22
    | spl15_21 ),
    inference(avatar_split_clause,[],[f326,f320,f335])).

fof(f335,plain,
    ( spl15_22
  <=> r2_hidden(sK11(sK0,k1_relat_1(sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).

fof(f326,plain,
    ( ~ r2_hidden(sK11(sK0,k1_relat_1(sK2)),k1_tarski(sK0))
    | spl15_21 ),
    inference(unit_resulting_resolution,[],[f322,f113])).

fof(f323,plain,
    ( ~ spl15_21
    | spl15_3
    | ~ spl15_10 ),
    inference(avatar_split_clause,[],[f318,f182,f128,f320])).

fof(f182,plain,
    ( spl15_10
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_10])])).

fof(f318,plain,
    ( sK0 != sK11(sK0,k1_relat_1(sK2))
    | spl15_3
    | ~ spl15_10 ),
    inference(unit_resulting_resolution,[],[f184,f130,f116])).

fof(f184,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl15_10 ),
    inference(avatar_component_clause,[],[f182])).

fof(f316,plain,
    ( spl15_20
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f311,f123,f313])).

fof(f313,plain,
    ( spl15_20
  <=> r2_hidden(sK0,k1_relat_1(k1_relat_1(k2_zfmisc_1(sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).

fof(f311,plain,
    ( r2_hidden(sK0,k1_relat_1(k1_relat_1(k2_zfmisc_1(sK2,sK2))))
    | ~ spl15_2 ),
    inference(superposition,[],[f292,f125])).

fof(f292,plain,
    ( ! [X0] : r2_hidden(sK0,k1_relat_1(k1_relat_1(k2_zfmisc_1(sK2,k1_tarski(X0)))))
    | ~ spl15_2 ),
    inference(unit_resulting_resolution,[],[f194,f109])).

fof(f289,plain,
    ( spl15_19
    | ~ spl15_18 ),
    inference(avatar_split_clause,[],[f268,f263,f286])).

fof(f286,plain,
    ( spl15_19
  <=> r2_hidden(sK10(sK2,sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).

fof(f268,plain,
    ( r2_hidden(sK10(sK2,sK0),k2_relat_1(sK2))
    | ~ spl15_18 ),
    inference(unit_resulting_resolution,[],[f265,f107])).

fof(f266,plain,
    ( spl15_18
    | ~ spl15_10 ),
    inference(avatar_split_clause,[],[f255,f182,f263])).

fof(f255,plain,
    ( r2_hidden(k4_tarski(sK0,sK10(sK2,sK0)),sK2)
    | ~ spl15_10 ),
    inference(unit_resulting_resolution,[],[f184,f110])).

fof(f254,plain,
    ( spl15_17
    | ~ spl15_16 ),
    inference(avatar_split_clause,[],[f246,f242,f251])).

fof(f246,plain,
    ( r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | ~ spl15_16 ),
    inference(unit_resulting_resolution,[],[f244,f109])).

fof(f245,plain,
    ( spl15_16
    | ~ spl15_9 ),
    inference(avatar_split_clause,[],[f236,f173,f242])).

fof(f236,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK1),sK1),sK2)
    | ~ spl15_9 ),
    inference(unit_resulting_resolution,[],[f175,f108])).

fof(f232,plain,
    ( spl15_15
    | ~ spl15_1
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f227,f222,f118,f229])).

fof(f227,plain,
    ( r2_hidden(sK7(sK2),k1_relat_1(sK2))
    | ~ spl15_1
    | ~ spl15_14 ),
    inference(unit_resulting_resolution,[],[f120,f224,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f58])).

fof(f58,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK7(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f225,plain,
    ( spl15_14
    | ~ spl15_1
    | ~ spl15_10 ),
    inference(avatar_split_clause,[],[f220,f182,f118,f222])).

fof(f220,plain,
    ( r2_hidden(sK6(sK2),k2_relat_1(sK2))
    | ~ spl15_1
    | ~ spl15_10 ),
    inference(unit_resulting_resolution,[],[f120,f184,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f56])).

fof(f56,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK6(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

fof(f219,plain,
    ( spl15_13
    | ~ spl15_11 ),
    inference(avatar_split_clause,[],[f209,f201,f216])).

fof(f216,plain,
    ( spl15_13
  <=> r2_hidden(sK1,k2_relat_1(k2_relat_1(k2_zfmisc_1(sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).

fof(f201,plain,
    ( spl15_11
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_relat_1(k2_zfmisc_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_11])])).

fof(f209,plain,
    ( r2_hidden(sK1,k2_relat_1(k2_relat_1(k2_zfmisc_1(sK2,sK2))))
    | ~ spl15_11 ),
    inference(unit_resulting_resolution,[],[f203,f107])).

fof(f203,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_relat_1(k2_zfmisc_1(sK2,sK2)))
    | ~ spl15_11 ),
    inference(avatar_component_clause,[],[f201])).

fof(f214,plain,
    ( spl15_12
    | ~ spl15_11 ),
    inference(avatar_split_clause,[],[f208,f201,f211])).

fof(f211,plain,
    ( spl15_12
  <=> r2_hidden(sK0,k1_relat_1(k2_relat_1(k2_zfmisc_1(sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).

fof(f208,plain,
    ( r2_hidden(sK0,k1_relat_1(k2_relat_1(k2_zfmisc_1(sK2,sK2))))
    | ~ spl15_11 ),
    inference(unit_resulting_resolution,[],[f203,f109])).

fof(f204,plain,
    ( spl15_11
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f199,f123,f201])).

fof(f199,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_relat_1(k2_zfmisc_1(sK2,sK2)))
    | ~ spl15_2 ),
    inference(superposition,[],[f195,f125])).

fof(f195,plain,
    ( ! [X0] : r2_hidden(X0,k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(X0))))
    | ~ spl15_2 ),
    inference(unit_resulting_resolution,[],[f190,f107])).

fof(f185,plain,
    ( spl15_10
    | ~ spl15_5 ),
    inference(avatar_split_clause,[],[f179,f138,f182])).

fof(f138,plain,
    ( spl15_5
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f179,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl15_5 ),
    inference(unit_resulting_resolution,[],[f140,f109])).

fof(f140,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl15_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f176,plain,
    ( spl15_9
    | ~ spl15_5 ),
    inference(avatar_split_clause,[],[f170,f138,f173])).

fof(f170,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl15_5 ),
    inference(unit_resulting_resolution,[],[f140,f107])).

fof(f169,plain,
    ( spl15_8
    | ~ spl15_1 ),
    inference(avatar_split_clause,[],[f161,f118,f166])).

fof(f161,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl15_1 ),
    inference(unit_resulting_resolution,[],[f120,f88])).

fof(f88,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f160,plain,
    ( ~ spl15_7
    | spl15_3 ),
    inference(avatar_split_clause,[],[f147,f128,f157])).

fof(f157,plain,
    ( spl15_7
  <=> r2_hidden(k1_tarski(sK0),k1_tarski(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).

fof(f147,plain,
    ( ~ r2_hidden(k1_tarski(sK0),k1_tarski(k1_relat_1(sK2)))
    | spl15_3 ),
    inference(unit_resulting_resolution,[],[f130,f113])).

fof(f155,plain,
    ( ~ spl15_6
    | spl15_3 ),
    inference(avatar_split_clause,[],[f146,f128,f152])).

fof(f146,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),k1_tarski(k1_tarski(sK0)))
    | spl15_3 ),
    inference(unit_resulting_resolution,[],[f130,f113])).

fof(f141,plain,
    ( spl15_5
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f136,f123,f138])).

fof(f136,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl15_2 ),
    inference(superposition,[],[f112,f125])).

fof(f135,plain,
    ( ~ spl15_3
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f81,f132,f128])).

fof(f81,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( k1_tarski(sK1) != k2_relat_1(sK2)
      | k1_tarski(sK0) != k1_relat_1(sK2) )
    & sK2 = k1_tarski(k4_tarski(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2
        & v1_relat_1(X2) )
   => ( ( k1_tarski(sK1) != k2_relat_1(sK2)
        | k1_tarski(sK0) != k1_relat_1(sK2) )
      & sK2 = k1_tarski(k4_tarski(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f36,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(f126,plain,(
    spl15_2 ),
    inference(avatar_split_clause,[],[f80,f123])).

fof(f80,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f121,plain,(
    spl15_1 ),
    inference(avatar_split_clause,[],[f79,f118])).

fof(f79,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:03:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (605)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (610)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (598)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (619)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (625)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (617)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (602)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (603)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (600)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.54  % (599)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.54  % (620)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.54  % (612)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.54  % (609)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.54  % (614)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.28/0.54  % (623)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.28/0.54  % (611)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.28/0.54  % (601)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.54  % (604)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.55  % (613)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.55  % (622)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.28/0.55  % (627)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.28/0.55  % (624)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.28/0.55  % (626)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.28/0.55  % (607)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.55  % (615)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.55  % (606)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.28/0.56  % (616)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.28/0.56  % (618)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.56  % (621)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.28/0.56  % (608)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 3.50/0.83  % (603)Time limit reached!
% 3.50/0.83  % (603)------------------------------
% 3.50/0.83  % (603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.50/0.83  % (603)Termination reason: Time limit
% 3.50/0.83  % (603)Termination phase: Saturation
% 3.50/0.83  
% 3.50/0.83  % (603)Memory used [KB]: 9338
% 3.50/0.83  % (603)Time elapsed: 0.400 s
% 3.50/0.83  % (603)------------------------------
% 3.50/0.83  % (603)------------------------------
% 3.77/0.91  % (608)Time limit reached!
% 3.77/0.91  % (608)------------------------------
% 3.77/0.91  % (608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.77/0.91  % (608)Termination reason: Time limit
% 3.77/0.91  % (608)Termination phase: Saturation
% 3.77/0.91  
% 3.77/0.91  % (608)Memory used [KB]: 12665
% 3.77/0.91  % (608)Time elapsed: 0.500 s
% 3.77/0.91  % (608)------------------------------
% 3.77/0.91  % (608)------------------------------
% 3.77/0.92  % (610)Time limit reached!
% 3.77/0.92  % (610)------------------------------
% 3.77/0.92  % (610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.77/0.92  % (610)Termination reason: Time limit
% 3.77/0.92  
% 3.77/0.92  % (610)Memory used [KB]: 9850
% 3.77/0.92  % (610)Time elapsed: 0.506 s
% 3.77/0.92  % (610)------------------------------
% 3.77/0.92  % (610)------------------------------
% 4.37/0.93  % (615)Time limit reached!
% 4.37/0.93  % (615)------------------------------
% 4.37/0.93  % (615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.93  % (615)Termination reason: Time limit
% 4.37/0.93  % (615)Termination phase: Saturation
% 4.37/0.93  
% 4.37/0.93  % (615)Memory used [KB]: 17526
% 4.37/0.93  % (615)Time elapsed: 0.500 s
% 4.37/0.93  % (615)------------------------------
% 4.37/0.93  % (615)------------------------------
% 4.37/0.93  % (598)Time limit reached!
% 4.37/0.93  % (598)------------------------------
% 4.37/0.93  % (598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.93  % (598)Termination reason: Time limit
% 4.37/0.93  
% 4.37/0.93  % (598)Memory used [KB]: 4349
% 4.37/0.93  % (598)Time elapsed: 0.510 s
% 4.37/0.93  % (598)------------------------------
% 4.37/0.93  % (598)------------------------------
% 4.37/0.93  % (599)Time limit reached!
% 4.37/0.93  % (599)------------------------------
% 4.37/0.93  % (599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.93  % (599)Termination reason: Time limit
% 4.37/0.93  
% 4.37/0.93  % (599)Memory used [KB]: 8571
% 4.37/0.93  % (599)Time elapsed: 0.517 s
% 4.37/0.93  % (599)------------------------------
% 4.37/0.93  % (599)------------------------------
% 4.37/0.94  % (721)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.64/1.02  % (614)Time limit reached!
% 4.64/1.02  % (614)------------------------------
% 4.64/1.02  % (614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.02  % (614)Termination reason: Time limit
% 4.64/1.02  % (614)Termination phase: Saturation
% 4.64/1.02  
% 4.64/1.02  % (614)Memory used [KB]: 15735
% 4.64/1.02  % (614)Time elapsed: 0.600 s
% 4.64/1.02  % (614)------------------------------
% 4.64/1.02  % (614)------------------------------
% 4.64/1.02  % (779)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.64/1.04  % (626)Time limit reached!
% 4.64/1.04  % (626)------------------------------
% 4.64/1.04  % (626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.08/1.04  % (767)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.08/1.05  % (626)Termination reason: Time limit
% 5.08/1.05  
% 5.08/1.05  % (626)Memory used [KB]: 8315
% 5.08/1.05  % (626)Time elapsed: 0.624 s
% 5.08/1.05  % (626)------------------------------
% 5.08/1.05  % (626)------------------------------
% 5.08/1.05  % (605)Time limit reached!
% 5.08/1.05  % (605)------------------------------
% 5.08/1.05  % (605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.08/1.05  % (605)Termination reason: Time limit
% 5.08/1.05  
% 5.08/1.05  % (605)Memory used [KB]: 13688
% 5.08/1.05  % (605)Time elapsed: 0.638 s
% 5.08/1.05  % (605)------------------------------
% 5.08/1.05  % (605)------------------------------
% 5.08/1.06  % (784)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.08/1.07  % (789)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.50/1.07  % (788)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.99/1.15  % (832)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.24/1.17  % (842)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.24/1.19  % (843)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.72/1.25  % (619)Time limit reached!
% 6.72/1.25  % (619)------------------------------
% 6.72/1.25  % (619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.72/1.25  % (619)Termination reason: Time limit
% 6.72/1.25  
% 6.72/1.25  % (619)Memory used [KB]: 7931
% 6.72/1.25  % (619)Time elapsed: 0.832 s
% 6.72/1.25  % (619)------------------------------
% 6.72/1.25  % (619)------------------------------
% 7.48/1.36  % (874)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.80/1.37  % (784)Time limit reached!
% 7.80/1.37  % (784)------------------------------
% 7.80/1.37  % (784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.80/1.37  % (784)Termination reason: Time limit
% 7.80/1.37  % (784)Termination phase: Saturation
% 7.80/1.37  
% 7.80/1.37  % (784)Memory used [KB]: 8315
% 7.80/1.37  % (784)Time elapsed: 0.405 s
% 7.80/1.37  % (784)------------------------------
% 7.80/1.37  % (784)------------------------------
% 7.80/1.39  % (788)Time limit reached!
% 7.80/1.39  % (788)------------------------------
% 7.80/1.39  % (788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.80/1.39  % (788)Termination reason: Time limit
% 7.80/1.39  
% 7.80/1.39  % (788)Memory used [KB]: 13944
% 7.80/1.39  % (788)Time elapsed: 0.424 s
% 7.80/1.39  % (788)------------------------------
% 7.80/1.39  % (788)------------------------------
% 7.80/1.43  % (600)Time limit reached!
% 7.80/1.43  % (600)------------------------------
% 7.80/1.43  % (600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.80/1.43  % (600)Termination reason: Time limit
% 7.80/1.43  
% 7.80/1.43  % (600)Memory used [KB]: 20852
% 7.80/1.43  % (600)Time elapsed: 1.005 s
% 7.80/1.43  % (600)------------------------------
% 7.80/1.43  % (600)------------------------------
% 8.58/1.48  % (920)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 8.58/1.51  % (921)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.21/1.56  % (922)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.21/1.62  % (624)Time limit reached!
% 9.21/1.62  % (624)------------------------------
% 9.21/1.62  % (624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.21/1.62  % (624)Termination reason: Time limit
% 9.21/1.62  % (624)Termination phase: Saturation
% 9.21/1.62  
% 9.21/1.62  % (624)Memory used [KB]: 14839
% 9.21/1.62  % (624)Time elapsed: 1.200 s
% 9.21/1.62  % (624)------------------------------
% 9.21/1.62  % (624)------------------------------
% 9.97/1.66  % (620)Time limit reached!
% 9.97/1.66  % (620)------------------------------
% 9.97/1.66  % (620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.97/1.67  % (620)Termination reason: Time limit
% 9.97/1.67  
% 9.97/1.67  % (620)Memory used [KB]: 21364
% 9.97/1.67  % (620)Time elapsed: 1.214 s
% 9.97/1.67  % (620)------------------------------
% 9.97/1.67  % (620)------------------------------
% 10.29/1.72  % (613)Time limit reached!
% 10.29/1.72  % (613)------------------------------
% 10.29/1.72  % (613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.29/1.73  % (622)Time limit reached!
% 10.29/1.73  % (622)------------------------------
% 10.29/1.73  % (622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.29/1.73  % (622)Termination reason: Time limit
% 10.29/1.73  % (622)Termination phase: Saturation
% 10.29/1.73  
% 10.29/1.73  % (622)Memory used [KB]: 19317
% 10.29/1.73  % (622)Time elapsed: 1.300 s
% 10.29/1.73  % (622)------------------------------
% 10.29/1.73  % (622)------------------------------
% 10.29/1.73  % (613)Termination reason: Time limit
% 10.29/1.73  
% 10.29/1.73  % (613)Memory used [KB]: 17782
% 10.29/1.73  % (613)Time elapsed: 1.306 s
% 10.29/1.73  % (613)------------------------------
% 10.29/1.73  % (613)------------------------------
% 10.87/1.75  % (923)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 10.99/1.81  % (924)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.58/1.86  % (925)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.58/1.87  % (926)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.58/1.92  % (625)Time limit reached!
% 11.58/1.92  % (625)------------------------------
% 11.58/1.92  % (625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.14/1.93  % (625)Termination reason: Time limit
% 12.14/1.93  % (625)Termination phase: Saturation
% 12.14/1.93  
% 12.14/1.93  % (625)Memory used [KB]: 13304
% 12.14/1.93  % (625)Time elapsed: 1.500 s
% 12.14/1.93  % (625)------------------------------
% 12.14/1.93  % (625)------------------------------
% 12.14/1.96  % (922)Time limit reached!
% 12.14/1.96  % (922)------------------------------
% 12.14/1.96  % (922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.14/1.97  % (602)Time limit reached!
% 12.14/1.97  % (602)------------------------------
% 12.14/1.97  % (602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.53/1.98  % (602)Termination reason: Time limit
% 12.53/1.98  
% 12.53/1.98  % (602)Memory used [KB]: 22771
% 12.53/1.98  % (602)Time elapsed: 1.530 s
% 12.53/1.98  % (602)------------------------------
% 12.53/1.98  % (602)------------------------------
% 12.53/1.98  % (922)Termination reason: Time limit
% 12.53/1.98  % (922)Termination phase: Saturation
% 12.53/1.98  
% 12.53/1.98  % (922)Memory used [KB]: 3582
% 12.53/1.98  % (922)Time elapsed: 0.500 s
% 12.53/1.98  % (922)------------------------------
% 12.53/1.98  % (922)------------------------------
% 12.53/2.04  % (609)Time limit reached!
% 12.53/2.04  % (609)------------------------------
% 12.53/2.04  % (609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.53/2.04  % (609)Termination reason: Time limit
% 12.53/2.04  
% 12.53/2.04  % (609)Memory used [KB]: 20724
% 12.53/2.04  % (609)Time elapsed: 1.620 s
% 12.53/2.04  % (609)------------------------------
% 12.53/2.04  % (609)------------------------------
% 12.53/2.04  % (927)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 13.16/2.11  % (929)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.16/2.11  % (928)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 14.15/2.16  % (926)Time limit reached!
% 14.15/2.16  % (926)------------------------------
% 14.15/2.16  % (926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.15/2.16  % (926)Termination reason: Time limit
% 14.15/2.16  
% 14.15/2.16  % (926)Memory used [KB]: 4477
% 14.15/2.16  % (926)Time elapsed: 0.411 s
% 14.15/2.16  % (926)------------------------------
% 14.15/2.16  % (926)------------------------------
% 14.15/2.18  % (930)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 14.77/2.28  % (832)Time limit reached!
% 14.77/2.28  % (832)------------------------------
% 14.77/2.28  % (832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.16/2.29  % (832)Termination reason: Time limit
% 15.16/2.29  
% 15.16/2.29  % (832)Memory used [KB]: 13816
% 15.16/2.29  % (832)Time elapsed: 1.234 s
% 15.16/2.29  % (832)------------------------------
% 15.16/2.29  % (832)------------------------------
% 15.16/2.30  % (931)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.71/2.37  % (612)Time limit reached!
% 15.71/2.37  % (612)------------------------------
% 15.71/2.37  % (612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.71/2.39  % (612)Termination reason: Time limit
% 15.71/2.39  
% 15.71/2.39  % (612)Memory used [KB]: 9722
% 15.71/2.39  % (612)Time elapsed: 1.919 s
% 15.71/2.39  % (612)------------------------------
% 15.71/2.39  % (612)------------------------------
% 15.71/2.40  % (929)Time limit reached!
% 15.71/2.40  % (929)------------------------------
% 15.71/2.40  % (929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.71/2.40  % (929)Termination reason: Time limit
% 15.71/2.40  
% 15.71/2.40  % (929)Memory used [KB]: 2814
% 15.71/2.40  % (929)Time elapsed: 0.406 s
% 15.71/2.40  % (929)------------------------------
% 15.71/2.40  % (929)------------------------------
% 16.13/2.42  % (932)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 16.41/2.48  % (616)Time limit reached!
% 16.41/2.48  % (616)------------------------------
% 16.41/2.48  % (616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.41/2.48  % (604)Time limit reached!
% 16.41/2.48  % (604)------------------------------
% 16.41/2.48  % (604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.41/2.48  % (604)Termination reason: Time limit
% 16.41/2.48  % (604)Termination phase: Saturation
% 16.41/2.48  
% 16.41/2.48  % (604)Memory used [KB]: 26993
% 16.41/2.48  % (604)Time elapsed: 2.0000 s
% 16.41/2.48  % (604)------------------------------
% 16.41/2.48  % (604)------------------------------
% 16.41/2.49  % (616)Termination reason: Time limit
% 16.41/2.49  
% 16.41/2.49  % (616)Memory used [KB]: 17910
% 16.41/2.49  % (616)Time elapsed: 2.067 s
% 16.41/2.49  % (616)------------------------------
% 16.41/2.49  % (616)------------------------------
% 16.41/2.52  % (933)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 16.41/2.53  % (934)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.29/2.62  % (935)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 17.29/2.63  % (936)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.75/2.70  % (779)Time limit reached!
% 17.75/2.70  % (779)------------------------------
% 17.75/2.70  % (779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.75/2.71  % (779)Termination reason: Time limit
% 17.75/2.71  % (779)Termination phase: Saturation
% 17.75/2.71  
% 17.75/2.71  % (779)Memory used [KB]: 20596
% 17.75/2.71  % (779)Time elapsed: 1.725 s
% 17.75/2.71  % (779)------------------------------
% 17.75/2.71  % (779)------------------------------
% 18.96/2.76  % (933)Refutation found. Thanks to Tanya!
% 18.96/2.76  % SZS status Theorem for theBenchmark
% 18.96/2.77  % SZS output start Proof for theBenchmark
% 18.96/2.77  fof(f1094,plain,(
% 18.96/2.77    $false),
% 18.96/2.77    inference(avatar_sat_refutation,[],[f121,f126,f135,f141,f155,f160,f169,f176,f185,f204,f214,f219,f225,f232,f245,f254,f266,f289,f316,f323,f338,f346,f357,f366,f394,f411,f416,f432,f452,f457,f474,f491,f506,f514,f539,f549,f554,f570,f610,f615,f634,f673,f680,f715,f720,f725,f750,f755,f778,f783,f900,f907,f941,f949,f968,f969,f975,f1025,f1033,f1068,f1090])).
% 18.96/2.77  fof(f1090,plain,(
% 18.96/2.77    ~spl15_2 | spl15_29 | ~spl15_31),
% 18.96/2.77    inference(avatar_contradiction_clause,[],[f1075])).
% 18.96/2.77  fof(f1075,plain,(
% 18.96/2.77    $false | (~spl15_2 | spl15_29 | ~spl15_31)),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f431,f456,f1015])).
% 18.96/2.77  fof(f1015,plain,(
% 18.96/2.77    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | sK1 = X0) ) | ~spl15_2),
% 18.96/2.77    inference(superposition,[],[f307,f125])).
% 18.96/2.77  fof(f125,plain,(
% 18.96/2.77    sK2 = k1_tarski(k4_tarski(sK0,sK1)) | ~spl15_2),
% 18.96/2.77    inference(avatar_component_clause,[],[f123])).
% 18.96/2.77  fof(f123,plain,(
% 18.96/2.77    spl15_2 <=> sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).
% 18.96/2.77  fof(f307,plain,(
% 18.96/2.77    ( ! [X2,X3,X1] : (~r2_hidden(X1,k2_relat_1(k1_tarski(k4_tarski(X3,X2)))) | X1 = X2) )),
% 18.96/2.77    inference(forward_demodulation,[],[f300,f102])).
% 18.96/2.77  fof(f102,plain,(
% 18.96/2.77    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 18.96/2.77    inference(cnf_transformation,[],[f20])).
% 18.96/2.77  fof(f20,axiom,(
% 18.96/2.77    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 18.96/2.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 18.96/2.77  fof(f300,plain,(
% 18.96/2.77    ( ! [X2,X3,X1] : (X1 = X2 | ~r2_hidden(X1,k2_relat_1(k2_zfmisc_1(k1_tarski(X3),k1_tarski(X2))))) )),
% 18.96/2.77    inference(resolution,[],[f100,f108])).
% 18.96/2.77  fof(f108,plain,(
% 18.96/2.77    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 18.96/2.77    inference(equality_resolution,[],[f82])).
% 18.96/2.77  fof(f82,plain,(
% 18.96/2.77    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 18.96/2.77    inference(cnf_transformation,[],[f55])).
% 18.96/2.77  fof(f55,plain,(
% 18.96/2.77    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 18.96/2.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f51,f54,f53,f52])).
% 18.96/2.77  fof(f52,plain,(
% 18.96/2.77    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 18.96/2.77    introduced(choice_axiom,[])).
% 18.96/2.77  fof(f53,plain,(
% 18.96/2.77    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 18.96/2.77    introduced(choice_axiom,[])).
% 18.96/2.77  fof(f54,plain,(
% 18.96/2.77    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 18.96/2.77    introduced(choice_axiom,[])).
% 18.96/2.77  fof(f51,plain,(
% 18.96/2.77    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 18.96/2.77    inference(rectify,[],[f50])).
% 18.96/2.77  fof(f50,plain,(
% 18.96/2.77    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 18.96/2.77    inference(nnf_transformation,[],[f30])).
% 18.96/2.77  fof(f30,axiom,(
% 18.96/2.77    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 18.96/2.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 18.96/2.77  fof(f100,plain,(
% 18.96/2.77    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 = X3) )),
% 18.96/2.77    inference(cnf_transformation,[],[f74])).
% 18.96/2.77  fof(f74,plain,(
% 18.96/2.77    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 18.96/2.77    inference(flattening,[],[f73])).
% 18.96/2.77  fof(f73,plain,(
% 18.96/2.77    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | (X1 != X3 | X0 != X2)) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 18.96/2.77    inference(nnf_transformation,[],[f19])).
% 18.96/2.77  fof(f19,axiom,(
% 18.96/2.77    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 18.96/2.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 18.96/2.77  fof(f456,plain,(
% 18.96/2.77    r2_hidden(sK11(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | ~spl15_31),
% 18.96/2.77    inference(avatar_component_clause,[],[f454])).
% 18.96/2.77  fof(f454,plain,(
% 18.96/2.77    spl15_31 <=> r2_hidden(sK11(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_31])])).
% 18.96/2.77  fof(f431,plain,(
% 18.96/2.77    sK1 != sK11(sK1,k2_relat_1(sK2)) | spl15_29),
% 18.96/2.77    inference(avatar_component_clause,[],[f429])).
% 18.96/2.77  fof(f429,plain,(
% 18.96/2.77    spl15_29 <=> sK1 = sK11(sK1,k2_relat_1(sK2))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_29])])).
% 18.96/2.77  fof(f1068,plain,(
% 18.96/2.77    spl15_58 | ~spl15_3 | ~spl15_8),
% 18.96/2.77    inference(avatar_split_clause,[],[f914,f166,f128,f1065])).
% 18.96/2.77  fof(f1065,plain,(
% 18.96/2.77    spl15_58 <=> r1_tarski(sK2,k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK2)))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_58])])).
% 18.96/2.77  fof(f128,plain,(
% 18.96/2.77    spl15_3 <=> k1_tarski(sK0) = k1_relat_1(sK2)),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).
% 18.96/2.77  fof(f166,plain,(
% 18.96/2.77    spl15_8 <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).
% 18.96/2.77  fof(f914,plain,(
% 18.96/2.77    r1_tarski(sK2,k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK2))) | (~spl15_3 | ~spl15_8)),
% 18.96/2.77    inference(superposition,[],[f168,f129])).
% 18.96/2.77  fof(f129,plain,(
% 18.96/2.77    k1_tarski(sK0) = k1_relat_1(sK2) | ~spl15_3),
% 18.96/2.77    inference(avatar_component_clause,[],[f128])).
% 18.96/2.77  fof(f168,plain,(
% 18.96/2.77    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | ~spl15_8),
% 18.96/2.77    inference(avatar_component_clause,[],[f166])).
% 18.96/2.77  fof(f1033,plain,(
% 18.96/2.77    spl15_57 | ~spl15_35 | ~spl15_56),
% 18.96/2.77    inference(avatar_split_clause,[],[f1027,f1022,f511,f1030])).
% 18.96/2.77  fof(f1030,plain,(
% 18.96/2.77    spl15_57 <=> r2_hidden(k4_tarski(sK0,sK6(sK2)),sK2)),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_57])])).
% 18.96/2.77  fof(f511,plain,(
% 18.96/2.77    spl15_35 <=> r2_hidden(k4_tarski(sK5(sK2,sK6(sK2)),sK6(sK2)),sK2)),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_35])])).
% 18.96/2.77  fof(f1022,plain,(
% 18.96/2.77    spl15_56 <=> sK0 = sK5(sK2,sK6(sK2))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_56])])).
% 18.96/2.77  fof(f1027,plain,(
% 18.96/2.77    r2_hidden(k4_tarski(sK0,sK6(sK2)),sK2) | (~spl15_35 | ~spl15_56)),
% 18.96/2.77    inference(superposition,[],[f513,f1024])).
% 18.96/2.77  fof(f1024,plain,(
% 18.96/2.77    sK0 = sK5(sK2,sK6(sK2)) | ~spl15_56),
% 18.96/2.77    inference(avatar_component_clause,[],[f1022])).
% 18.96/2.77  fof(f513,plain,(
% 18.96/2.77    r2_hidden(k4_tarski(sK5(sK2,sK6(sK2)),sK6(sK2)),sK2) | ~spl15_35),
% 18.96/2.77    inference(avatar_component_clause,[],[f511])).
% 18.96/2.77  fof(f1025,plain,(
% 18.96/2.77    spl15_56 | ~spl15_2 | ~spl15_39),
% 18.96/2.77    inference(avatar_split_clause,[],[f882,f567,f123,f1022])).
% 18.96/2.77  fof(f567,plain,(
% 18.96/2.77    spl15_39 <=> r2_hidden(sK5(sK2,sK6(sK2)),k1_relat_1(sK2))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_39])])).
% 18.96/2.77  fof(f882,plain,(
% 18.96/2.77    sK0 = sK5(sK2,sK6(sK2)) | (~spl15_2 | ~spl15_39)),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f569,f875])).
% 18.96/2.77  fof(f875,plain,(
% 18.96/2.77    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | sK0 = X0) ) | ~spl15_2),
% 18.96/2.77    inference(superposition,[],[f284,f125])).
% 18.96/2.77  fof(f284,plain,(
% 18.96/2.77    ( ! [X6,X4,X5] : (~r2_hidden(X4,k1_relat_1(k1_tarski(k4_tarski(X5,X6)))) | X4 = X5) )),
% 18.96/2.77    inference(forward_demodulation,[],[f276,f102])).
% 18.96/2.77  fof(f276,plain,(
% 18.96/2.77    ( ! [X6,X4,X5] : (X4 = X5 | ~r2_hidden(X4,k1_relat_1(k2_zfmisc_1(k1_tarski(X5),k1_tarski(X6))))) )),
% 18.96/2.77    inference(resolution,[],[f99,f110])).
% 18.96/2.77  fof(f110,plain,(
% 18.96/2.77    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 18.96/2.77    inference(equality_resolution,[],[f89])).
% 18.96/2.77  fof(f89,plain,(
% 18.96/2.77    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 18.96/2.77    inference(cnf_transformation,[],[f65])).
% 18.96/2.77  fof(f65,plain,(
% 18.96/2.77    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK8(X0,X1),X3),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) | r2_hidden(sK8(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 18.96/2.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f61,f64,f63,f62])).
% 18.96/2.77  fof(f62,plain,(
% 18.96/2.77    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK8(X0,X1),X3),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0) | r2_hidden(sK8(X0,X1),X1))))),
% 18.96/2.77    introduced(choice_axiom,[])).
% 18.96/2.77  fof(f63,plain,(
% 18.96/2.77    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0))),
% 18.96/2.77    introduced(choice_axiom,[])).
% 18.96/2.77  fof(f64,plain,(
% 18.96/2.77    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0))),
% 18.96/2.77    introduced(choice_axiom,[])).
% 18.96/2.77  fof(f61,plain,(
% 18.96/2.77    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 18.96/2.77    inference(rectify,[],[f60])).
% 18.96/2.77  fof(f60,plain,(
% 18.96/2.77    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 18.96/2.77    inference(nnf_transformation,[],[f29])).
% 18.96/2.77  fof(f29,axiom,(
% 18.96/2.77    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 18.96/2.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 18.96/2.77  fof(f99,plain,(
% 18.96/2.77    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X0 = X2) )),
% 18.96/2.77    inference(cnf_transformation,[],[f74])).
% 18.96/2.77  fof(f569,plain,(
% 18.96/2.77    r2_hidden(sK5(sK2,sK6(sK2)),k1_relat_1(sK2)) | ~spl15_39),
% 18.96/2.77    inference(avatar_component_clause,[],[f567])).
% 18.96/2.77  fof(f975,plain,(
% 18.96/2.77    ~spl15_55 | ~spl15_3 | spl15_21),
% 18.96/2.77    inference(avatar_split_clause,[],[f918,f320,f128,f972])).
% 18.96/2.77  fof(f972,plain,(
% 18.96/2.77    spl15_55 <=> sK0 = sK11(sK0,k1_tarski(sK0))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_55])])).
% 18.96/2.77  fof(f320,plain,(
% 18.96/2.77    spl15_21 <=> sK0 = sK11(sK0,k1_relat_1(sK2))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_21])])).
% 18.96/2.77  fof(f918,plain,(
% 18.96/2.77    sK0 != sK11(sK0,k1_tarski(sK0)) | (~spl15_3 | spl15_21)),
% 18.96/2.77    inference(superposition,[],[f322,f129])).
% 18.96/2.77  fof(f322,plain,(
% 18.96/2.77    sK0 != sK11(sK0,k1_relat_1(sK2)) | spl15_21),
% 18.96/2.77    inference(avatar_component_clause,[],[f320])).
% 18.96/2.77  fof(f969,plain,(
% 18.96/2.77    spl15_54),
% 18.96/2.77    inference(avatar_contradiction_clause,[],[f966])).
% 18.96/2.77  fof(f966,plain,(
% 18.96/2.77    $false | spl15_54),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f112,f948])).
% 18.96/2.77  fof(f948,plain,(
% 18.96/2.77    ~r2_hidden(k1_tarski(sK0),k1_tarski(k1_tarski(sK0))) | spl15_54),
% 18.96/2.77    inference(avatar_component_clause,[],[f946])).
% 18.96/2.77  fof(f946,plain,(
% 18.96/2.77    spl15_54 <=> r2_hidden(k1_tarski(sK0),k1_tarski(k1_tarski(sK0)))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_54])])).
% 18.96/2.77  fof(f112,plain,(
% 18.96/2.77    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 18.96/2.77    inference(equality_resolution,[],[f111])).
% 18.96/2.77  fof(f111,plain,(
% 18.96/2.77    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 18.96/2.77    inference(equality_resolution,[],[f94])).
% 18.96/2.77  fof(f94,plain,(
% 18.96/2.77    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 18.96/2.77    inference(cnf_transformation,[],[f69])).
% 18.96/2.77  fof(f69,plain,(
% 18.96/2.77    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK11(X0,X1) != X0 | ~r2_hidden(sK11(X0,X1),X1)) & (sK11(X0,X1) = X0 | r2_hidden(sK11(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 18.96/2.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f67,f68])).
% 18.96/2.77  fof(f68,plain,(
% 18.96/2.77    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK11(X0,X1) != X0 | ~r2_hidden(sK11(X0,X1),X1)) & (sK11(X0,X1) = X0 | r2_hidden(sK11(X0,X1),X1))))),
% 18.96/2.77    introduced(choice_axiom,[])).
% 18.96/2.77  fof(f67,plain,(
% 18.96/2.77    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 18.96/2.77    inference(rectify,[],[f66])).
% 18.96/2.77  fof(f66,plain,(
% 18.96/2.77    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 18.96/2.77    inference(nnf_transformation,[],[f7])).
% 18.96/2.77  fof(f7,axiom,(
% 18.96/2.77    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 18.96/2.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 18.96/2.77  fof(f968,plain,(
% 18.96/2.77    spl15_54),
% 18.96/2.77    inference(avatar_contradiction_clause,[],[f967])).
% 18.96/2.77  fof(f967,plain,(
% 18.96/2.77    $false | spl15_54),
% 18.96/2.77    inference(resolution,[],[f948,f112])).
% 18.96/2.77  fof(f949,plain,(
% 18.96/2.77    ~spl15_54 | ~spl15_3 | spl15_6),
% 18.96/2.77    inference(avatar_split_clause,[],[f912,f152,f128,f946])).
% 18.96/2.77  fof(f152,plain,(
% 18.96/2.77    spl15_6 <=> r2_hidden(k1_relat_1(sK2),k1_tarski(k1_tarski(sK0)))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).
% 18.96/2.77  fof(f912,plain,(
% 18.96/2.77    ~r2_hidden(k1_tarski(sK0),k1_tarski(k1_tarski(sK0))) | (~spl15_3 | spl15_6)),
% 18.96/2.77    inference(superposition,[],[f154,f129])).
% 18.96/2.77  fof(f154,plain,(
% 18.96/2.77    ~r2_hidden(k1_relat_1(sK2),k1_tarski(k1_tarski(sK0))) | spl15_6),
% 18.96/2.77    inference(avatar_component_clause,[],[f152])).
% 18.96/2.77  fof(f941,plain,(
% 18.96/2.77    spl15_53 | ~spl15_2 | ~spl15_17),
% 18.96/2.77    inference(avatar_split_clause,[],[f881,f251,f123,f938])).
% 18.96/2.77  fof(f938,plain,(
% 18.96/2.77    spl15_53 <=> sK0 = sK5(sK2,sK1)),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_53])])).
% 18.96/2.77  fof(f251,plain,(
% 18.96/2.77    spl15_17 <=> r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_17])])).
% 18.96/2.77  fof(f881,plain,(
% 18.96/2.77    sK0 = sK5(sK2,sK1) | (~spl15_2 | ~spl15_17)),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f253,f875])).
% 18.96/2.77  fof(f253,plain,(
% 18.96/2.77    r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | ~spl15_17),
% 18.96/2.77    inference(avatar_component_clause,[],[f251])).
% 18.96/2.77  fof(f907,plain,(
% 18.96/2.77    spl15_52 | ~spl15_2 | ~spl15_15),
% 18.96/2.77    inference(avatar_split_clause,[],[f883,f229,f123,f904])).
% 18.96/2.77  fof(f904,plain,(
% 18.96/2.77    spl15_52 <=> sK0 = sK7(sK2)),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_52])])).
% 18.96/2.77  fof(f229,plain,(
% 18.96/2.77    spl15_15 <=> r2_hidden(sK7(sK2),k1_relat_1(sK2))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).
% 18.96/2.77  fof(f883,plain,(
% 18.96/2.77    sK0 = sK7(sK2) | (~spl15_2 | ~spl15_15)),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f231,f875])).
% 18.96/2.77  fof(f231,plain,(
% 18.96/2.77    r2_hidden(sK7(sK2),k1_relat_1(sK2)) | ~spl15_15),
% 18.96/2.77    inference(avatar_component_clause,[],[f229])).
% 18.96/2.77  fof(f900,plain,(
% 18.96/2.77    ~spl15_2 | spl15_21 | ~spl15_25),
% 18.96/2.77    inference(avatar_contradiction_clause,[],[f885])).
% 18.96/2.77  fof(f885,plain,(
% 18.96/2.77    $false | (~spl15_2 | spl15_21 | ~spl15_25)),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f322,f365,f875])).
% 18.96/2.77  fof(f365,plain,(
% 18.96/2.77    r2_hidden(sK11(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) | ~spl15_25),
% 18.96/2.77    inference(avatar_component_clause,[],[f363])).
% 18.96/2.77  fof(f363,plain,(
% 18.96/2.77    spl15_25 <=> r2_hidden(sK11(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_25])])).
% 18.96/2.77  fof(f783,plain,(
% 18.96/2.77    ~spl15_51 | ~spl15_2 | spl15_4),
% 18.96/2.77    inference(avatar_split_clause,[],[f689,f132,f123,f780])).
% 18.96/2.77  fof(f780,plain,(
% 18.96/2.77    spl15_51 <=> r2_hidden(k1_tarski(sK1),k1_relat_1(k2_zfmisc_1(k1_tarski(k2_relat_1(sK2)),sK2)))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_51])])).
% 18.96/2.77  fof(f132,plain,(
% 18.96/2.77    spl15_4 <=> k1_tarski(sK1) = k2_relat_1(sK2)),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).
% 18.96/2.77  fof(f689,plain,(
% 18.96/2.77    ~r2_hidden(k1_tarski(sK1),k1_relat_1(k2_zfmisc_1(k1_tarski(k2_relat_1(sK2)),sK2))) | (~spl15_2 | spl15_4)),
% 18.96/2.77    inference(superposition,[],[f617,f206])).
% 18.96/2.77  fof(f206,plain,(
% 18.96/2.77    ( ! [X0] : (k2_zfmisc_1(k1_tarski(X0),sK2) = k1_tarski(k4_tarski(X0,k4_tarski(sK0,sK1)))) ) | ~spl15_2),
% 18.96/2.77    inference(superposition,[],[f102,f125])).
% 18.96/2.77  fof(f617,plain,(
% 18.96/2.77    ( ! [X0] : (~r2_hidden(k1_tarski(sK1),k1_relat_1(k1_tarski(k4_tarski(k2_relat_1(sK2),X0))))) ) | spl15_4),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f485,f110])).
% 18.96/2.77  fof(f485,plain,(
% 18.96/2.77    ( ! [X0,X1] : (~r2_hidden(k4_tarski(k1_tarski(sK1),X0),k1_tarski(k4_tarski(k2_relat_1(sK2),X1)))) ) | spl15_4),
% 18.96/2.77    inference(forward_demodulation,[],[f478,f102])).
% 18.96/2.77  fof(f478,plain,(
% 18.96/2.77    ( ! [X0,X1] : (~r2_hidden(k4_tarski(k1_tarski(sK1),X0),k2_zfmisc_1(k1_tarski(k2_relat_1(sK2)),k1_tarski(X1)))) ) | spl15_4),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f134,f99])).
% 18.96/2.77  fof(f134,plain,(
% 18.96/2.77    k1_tarski(sK1) != k2_relat_1(sK2) | spl15_4),
% 18.96/2.77    inference(avatar_component_clause,[],[f132])).
% 18.96/2.77  fof(f778,plain,(
% 18.96/2.77    ~spl15_50 | ~spl15_2 | spl15_3),
% 18.96/2.77    inference(avatar_split_clause,[],[f687,f128,f123,f775])).
% 18.96/2.77  fof(f775,plain,(
% 18.96/2.77    spl15_50 <=> r2_hidden(k1_tarski(sK0),k1_relat_1(k2_zfmisc_1(k1_tarski(k1_relat_1(sK2)),sK2)))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_50])])).
% 18.96/2.77  fof(f687,plain,(
% 18.96/2.77    ~r2_hidden(k1_tarski(sK0),k1_relat_1(k2_zfmisc_1(k1_tarski(k1_relat_1(sK2)),sK2))) | (~spl15_2 | spl15_3)),
% 18.96/2.77    inference(superposition,[],[f555,f206])).
% 18.96/2.77  fof(f555,plain,(
% 18.96/2.77    ( ! [X0] : (~r2_hidden(k1_tarski(sK0),k1_relat_1(k1_tarski(k4_tarski(k1_relat_1(sK2),X0))))) ) | spl15_3),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f405,f110])).
% 18.96/2.77  fof(f405,plain,(
% 18.96/2.77    ( ! [X0,X1] : (~r2_hidden(k4_tarski(k1_tarski(sK0),X0),k1_tarski(k4_tarski(k1_relat_1(sK2),X1)))) ) | spl15_3),
% 18.96/2.77    inference(forward_demodulation,[],[f398,f102])).
% 18.96/2.77  fof(f398,plain,(
% 18.96/2.77    ( ! [X0,X1] : (~r2_hidden(k4_tarski(k1_tarski(sK0),X0),k2_zfmisc_1(k1_tarski(k1_relat_1(sK2)),k1_tarski(X1)))) ) | spl15_3),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f130,f99])).
% 18.96/2.77  fof(f130,plain,(
% 18.96/2.77    k1_tarski(sK0) != k1_relat_1(sK2) | spl15_3),
% 18.96/2.77    inference(avatar_component_clause,[],[f128])).
% 18.96/2.77  fof(f755,plain,(
% 18.96/2.77    ~spl15_49 | ~spl15_2 | spl15_4),
% 18.96/2.77    inference(avatar_split_clause,[],[f684,f132,f123,f752])).
% 18.96/2.77  fof(f752,plain,(
% 18.96/2.77    spl15_49 <=> r2_hidden(k2_relat_1(sK2),k1_relat_1(k2_zfmisc_1(k1_tarski(k1_tarski(sK1)),sK2)))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_49])])).
% 18.96/2.77  fof(f684,plain,(
% 18.96/2.77    ~r2_hidden(k2_relat_1(sK2),k1_relat_1(k2_zfmisc_1(k1_tarski(k1_tarski(sK1)),sK2))) | (~spl15_2 | spl15_4)),
% 18.96/2.77    inference(superposition,[],[f587,f206])).
% 18.96/2.77  fof(f587,plain,(
% 18.96/2.77    ( ! [X0] : (~r2_hidden(k2_relat_1(sK2),k1_relat_1(k1_tarski(k4_tarski(k1_tarski(sK1),X0))))) ) | spl15_4),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f483,f110])).
% 18.96/2.77  fof(f483,plain,(
% 18.96/2.77    ( ! [X0,X1] : (~r2_hidden(k4_tarski(k2_relat_1(sK2),X0),k1_tarski(k4_tarski(k1_tarski(sK1),X1)))) ) | spl15_4),
% 18.96/2.77    inference(forward_demodulation,[],[f481,f102])).
% 18.96/2.77  fof(f481,plain,(
% 18.96/2.77    ( ! [X0,X1] : (~r2_hidden(k4_tarski(k2_relat_1(sK2),X0),k2_zfmisc_1(k1_tarski(k1_tarski(sK1)),k1_tarski(X1)))) ) | spl15_4),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f134,f99])).
% 18.96/2.77  fof(f750,plain,(
% 18.96/2.77    ~spl15_48 | ~spl15_2 | spl15_3),
% 18.96/2.77    inference(avatar_split_clause,[],[f682,f128,f123,f747])).
% 18.96/2.77  fof(f747,plain,(
% 18.96/2.77    spl15_48 <=> r2_hidden(k1_relat_1(sK2),k1_relat_1(k2_zfmisc_1(k1_tarski(k1_tarski(sK0)),sK2)))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_48])])).
% 18.96/2.77  fof(f682,plain,(
% 18.96/2.77    ~r2_hidden(k1_relat_1(sK2),k1_relat_1(k2_zfmisc_1(k1_tarski(k1_tarski(sK0)),sK2))) | (~spl15_2 | spl15_3)),
% 18.96/2.77    inference(superposition,[],[f528,f206])).
% 18.96/2.77  fof(f528,plain,(
% 18.96/2.77    ( ! [X0] : (~r2_hidden(k1_relat_1(sK2),k1_relat_1(k1_tarski(k4_tarski(k1_tarski(sK0),X0))))) ) | spl15_3),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f403,f110])).
% 18.96/2.77  fof(f403,plain,(
% 18.96/2.77    ( ! [X0,X1] : (~r2_hidden(k4_tarski(k1_relat_1(sK2),X0),k1_tarski(k4_tarski(k1_tarski(sK0),X1)))) ) | spl15_3),
% 18.96/2.77    inference(forward_demodulation,[],[f401,f102])).
% 18.96/2.77  fof(f401,plain,(
% 18.96/2.77    ( ! [X0,X1] : (~r2_hidden(k4_tarski(k1_relat_1(sK2),X0),k2_zfmisc_1(k1_tarski(k1_tarski(sK0)),k1_tarski(X1)))) ) | spl15_3),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f130,f99])).
% 18.96/2.77  fof(f725,plain,(
% 18.96/2.77    ~spl15_47 | ~spl15_2 | spl15_4),
% 18.96/2.77    inference(avatar_split_clause,[],[f647,f132,f123,f722])).
% 18.96/2.77  fof(f722,plain,(
% 18.96/2.77    spl15_47 <=> r2_hidden(k1_tarski(sK1),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k2_relat_1(sK2)))))),
% 18.96/2.77    introduced(avatar_definition,[new_symbols(naming,[spl15_47])])).
% 18.96/2.77  fof(f647,plain,(
% 18.96/2.77    ~r2_hidden(k1_tarski(sK1),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k2_relat_1(sK2))))) | (~spl15_2 | spl15_4)),
% 18.96/2.77    inference(superposition,[],[f625,f205])).
% 18.96/2.77  fof(f205,plain,(
% 18.96/2.77    ( ! [X0] : (k2_zfmisc_1(sK2,k1_tarski(X0)) = k1_tarski(k4_tarski(k4_tarski(sK0,sK1),X0))) ) | ~spl15_2),
% 18.96/2.77    inference(superposition,[],[f102,f125])).
% 18.96/2.77  fof(f625,plain,(
% 18.96/2.77    ( ! [X0] : (~r2_hidden(k1_tarski(sK1),k2_relat_1(k1_tarski(k4_tarski(X0,k2_relat_1(sK2)))))) ) | spl15_4),
% 18.96/2.77    inference(unit_resulting_resolution,[],[f486,f108])).
% 18.96/2.77  fof(f486,plain,(
% 18.96/2.77    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,k1_tarski(sK1)),k1_tarski(k4_tarski(X1,k2_relat_1(sK2))))) ) | spl15_4),
% 18.96/2.77    inference(forward_demodulation,[],[f477,f102])).
% 18.96/2.78  fof(f477,plain,(
% 18.96/2.78    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,k1_tarski(sK1)),k2_zfmisc_1(k1_tarski(X1),k1_tarski(k2_relat_1(sK2))))) ) | spl15_4),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f134,f100])).
% 18.96/2.78  fof(f720,plain,(
% 18.96/2.78    ~spl15_46 | ~spl15_2 | spl15_3),
% 18.96/2.78    inference(avatar_split_clause,[],[f645,f128,f123,f717])).
% 18.96/2.78  fof(f717,plain,(
% 18.96/2.78    spl15_46 <=> r2_hidden(k1_tarski(sK0),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k1_relat_1(sK2)))))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_46])])).
% 18.96/2.78  fof(f645,plain,(
% 18.96/2.78    ~r2_hidden(k1_tarski(sK0),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k1_relat_1(sK2))))) | (~spl15_2 | spl15_3)),
% 18.96/2.78    inference(superposition,[],[f571,f205])).
% 18.96/2.78  fof(f571,plain,(
% 18.96/2.78    ( ! [X0] : (~r2_hidden(k1_tarski(sK0),k2_relat_1(k1_tarski(k4_tarski(X0,k1_relat_1(sK2)))))) ) | spl15_3),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f406,f108])).
% 18.96/2.78  fof(f406,plain,(
% 18.96/2.78    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,k1_tarski(sK0)),k1_tarski(k4_tarski(X1,k1_relat_1(sK2))))) ) | spl15_3),
% 18.96/2.78    inference(forward_demodulation,[],[f397,f102])).
% 18.96/2.78  fof(f397,plain,(
% 18.96/2.78    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,k1_tarski(sK0)),k2_zfmisc_1(k1_tarski(X1),k1_tarski(k1_relat_1(sK2))))) ) | spl15_3),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f130,f100])).
% 18.96/2.78  fof(f715,plain,(
% 18.96/2.78    ~spl15_45 | ~spl15_2 | spl15_4),
% 18.96/2.78    inference(avatar_split_clause,[],[f643,f132,f123,f712])).
% 18.96/2.78  fof(f712,plain,(
% 18.96/2.78    spl15_45 <=> r2_hidden(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k1_tarski(sK1)))))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_45])])).
% 18.96/2.78  fof(f643,plain,(
% 18.96/2.78    ~r2_hidden(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k1_tarski(sK1))))) | (~spl15_2 | spl15_4)),
% 18.96/2.78    inference(superposition,[],[f603,f205])).
% 18.96/2.78  fof(f603,plain,(
% 18.96/2.78    ( ! [X0] : (~r2_hidden(k2_relat_1(sK2),k2_relat_1(k1_tarski(k4_tarski(X0,k1_tarski(sK1)))))) ) | spl15_4),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f484,f108])).
% 18.96/2.78  fof(f484,plain,(
% 18.96/2.78    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,k2_relat_1(sK2)),k1_tarski(k4_tarski(X1,k1_tarski(sK1))))) ) | spl15_4),
% 18.96/2.78    inference(forward_demodulation,[],[f480,f102])).
% 18.96/2.78  fof(f480,plain,(
% 18.96/2.78    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,k2_relat_1(sK2)),k2_zfmisc_1(k1_tarski(X1),k1_tarski(k1_tarski(sK1))))) ) | spl15_4),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f134,f100])).
% 18.96/2.78  fof(f680,plain,(
% 18.96/2.78    ~spl15_44 | ~spl15_2 | spl15_3),
% 18.96/2.78    inference(avatar_split_clause,[],[f641,f128,f123,f677])).
% 18.96/2.78  fof(f677,plain,(
% 18.96/2.78    spl15_44 <=> r2_hidden(k1_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k1_tarski(sK0)))))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_44])])).
% 18.96/2.78  fof(f641,plain,(
% 18.96/2.78    ~r2_hidden(k1_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(k1_tarski(sK0))))) | (~spl15_2 | spl15_3)),
% 18.96/2.78    inference(superposition,[],[f540,f205])).
% 18.96/2.78  fof(f540,plain,(
% 18.96/2.78    ( ! [X0] : (~r2_hidden(k1_relat_1(sK2),k2_relat_1(k1_tarski(k4_tarski(X0,k1_tarski(sK0)))))) ) | spl15_3),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f404,f108])).
% 18.96/2.78  fof(f404,plain,(
% 18.96/2.78    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,k1_relat_1(sK2)),k1_tarski(k4_tarski(X1,k1_tarski(sK0))))) ) | spl15_3),
% 18.96/2.78    inference(forward_demodulation,[],[f400,f102])).
% 18.96/2.78  fof(f400,plain,(
% 18.96/2.78    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,k1_relat_1(sK2)),k2_zfmisc_1(k1_tarski(X1),k1_tarski(k1_tarski(sK0))))) ) | spl15_3),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f130,f100])).
% 18.96/2.78  fof(f673,plain,(
% 18.96/2.78    spl15_43 | ~spl15_42),
% 18.96/2.78    inference(avatar_split_clause,[],[f637,f631,f670])).
% 18.96/2.78  fof(f670,plain,(
% 18.96/2.78    spl15_43 <=> r2_hidden(sK10(sK2,sK7(sK2)),k2_relat_1(sK2))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_43])])).
% 18.96/2.78  fof(f631,plain,(
% 18.96/2.78    spl15_42 <=> r2_hidden(k4_tarski(sK7(sK2),sK10(sK2,sK7(sK2))),sK2)),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_42])])).
% 18.96/2.78  fof(f637,plain,(
% 18.96/2.78    r2_hidden(sK10(sK2,sK7(sK2)),k2_relat_1(sK2)) | ~spl15_42),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f633,f107])).
% 18.96/2.78  fof(f107,plain,(
% 18.96/2.78    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 18.96/2.78    inference(equality_resolution,[],[f83])).
% 18.96/2.78  fof(f83,plain,(
% 18.96/2.78    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 18.96/2.78    inference(cnf_transformation,[],[f55])).
% 18.96/2.78  fof(f633,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK7(sK2),sK10(sK2,sK7(sK2))),sK2) | ~spl15_42),
% 18.96/2.78    inference(avatar_component_clause,[],[f631])).
% 18.96/2.78  fof(f634,plain,(
% 18.96/2.78    spl15_42 | ~spl15_15),
% 18.96/2.78    inference(avatar_split_clause,[],[f257,f229,f631])).
% 18.96/2.78  fof(f257,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK7(sK2),sK10(sK2,sK7(sK2))),sK2) | ~spl15_15),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f231,f110])).
% 18.96/2.78  fof(f615,plain,(
% 18.96/2.78    spl15_41 | ~spl15_38),
% 18.96/2.78    inference(avatar_split_clause,[],[f602,f551,f612])).
% 18.96/2.78  fof(f612,plain,(
% 18.96/2.78    spl15_41 <=> r2_hidden(sK1,k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_41])])).
% 18.96/2.78  fof(f551,plain,(
% 18.96/2.78    spl15_38 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_38])])).
% 18.96/2.78  fof(f602,plain,(
% 18.96/2.78    r2_hidden(sK1,k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl15_38),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f553,f107])).
% 18.96/2.78  fof(f553,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | ~spl15_38),
% 18.96/2.78    inference(avatar_component_clause,[],[f551])).
% 18.96/2.78  fof(f610,plain,(
% 18.96/2.78    spl15_40 | ~spl15_38),
% 18.96/2.78    inference(avatar_split_clause,[],[f601,f551,f607])).
% 18.96/2.78  fof(f607,plain,(
% 18.96/2.78    spl15_40 <=> r2_hidden(sK0,k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_40])])).
% 18.96/2.78  fof(f601,plain,(
% 18.96/2.78    r2_hidden(sK0,k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl15_38),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f553,f109])).
% 18.96/2.78  fof(f109,plain,(
% 18.96/2.78    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 18.96/2.78    inference(equality_resolution,[],[f90])).
% 18.96/2.78  fof(f90,plain,(
% 18.96/2.78    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 18.96/2.78    inference(cnf_transformation,[],[f65])).
% 18.96/2.78  fof(f570,plain,(
% 18.96/2.78    spl15_39 | ~spl15_35),
% 18.96/2.78    inference(avatar_split_clause,[],[f561,f511,f567])).
% 18.96/2.78  fof(f561,plain,(
% 18.96/2.78    r2_hidden(sK5(sK2,sK6(sK2)),k1_relat_1(sK2)) | ~spl15_35),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f513,f109])).
% 18.96/2.78  fof(f554,plain,(
% 18.96/2.78    spl15_38 | ~spl15_1 | ~spl15_2 | ~spl15_8 | ~spl15_18),
% 18.96/2.78    inference(avatar_split_clause,[],[f424,f263,f166,f123,f118,f551])).
% 18.96/2.78  fof(f118,plain,(
% 18.96/2.78    spl15_1 <=> v1_relat_1(sK2)),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).
% 18.96/2.78  fof(f263,plain,(
% 18.96/2.78    spl15_18 <=> r2_hidden(k4_tarski(sK0,sK10(sK2,sK0)),sK2)),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).
% 18.96/2.78  fof(f424,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | (~spl15_1 | ~spl15_2 | ~spl15_8 | ~spl15_18)),
% 18.96/2.78    inference(forward_demodulation,[],[f419,f269])).
% 18.96/2.78  fof(f269,plain,(
% 18.96/2.78    k4_tarski(sK0,sK1) = k4_tarski(sK0,sK10(sK2,sK0)) | (~spl15_2 | ~spl15_18)),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f265,f150])).
% 18.96/2.78  fof(f150,plain,(
% 18.96/2.78    ( ! [X0] : (~r2_hidden(X0,sK2) | k4_tarski(sK0,sK1) = X0) ) | ~spl15_2),
% 18.96/2.78    inference(superposition,[],[f113,f125])).
% 18.96/2.78  fof(f113,plain,(
% 18.96/2.78    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 18.96/2.78    inference(equality_resolution,[],[f93])).
% 18.96/2.78  fof(f93,plain,(
% 18.96/2.78    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 18.96/2.78    inference(cnf_transformation,[],[f69])).
% 18.96/2.78  fof(f265,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK0,sK10(sK2,sK0)),sK2) | ~spl15_18),
% 18.96/2.78    inference(avatar_component_clause,[],[f263])).
% 18.96/2.78  fof(f419,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK0,sK10(sK2,sK0)),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | (~spl15_1 | ~spl15_8 | ~spl15_18)),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f120,f168,f265,f103])).
% 18.96/2.78  fof(f103,plain,(
% 18.96/2.78    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 18.96/2.78    inference(cnf_transformation,[],[f78])).
% 18.96/2.78  fof(f78,plain,(
% 18.96/2.78    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK13(X0,X1),sK14(X0,X1)),X1) & r2_hidden(k4_tarski(sK13(X0,X1),sK14(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 18.96/2.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f76,f77])).
% 18.96/2.78  fof(f77,plain,(
% 18.96/2.78    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK13(X0,X1),sK14(X0,X1)),X1) & r2_hidden(k4_tarski(sK13(X0,X1),sK14(X0,X1)),X0)))),
% 18.96/2.78    introduced(choice_axiom,[])).
% 18.96/2.78  fof(f76,plain,(
% 18.96/2.78    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 18.96/2.78    inference(rectify,[],[f75])).
% 18.96/2.78  fof(f75,plain,(
% 18.96/2.78    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 18.96/2.78    inference(nnf_transformation,[],[f46])).
% 18.96/2.78  fof(f46,plain,(
% 18.96/2.78    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 18.96/2.78    inference(ennf_transformation,[],[f28])).
% 18.96/2.78  fof(f28,axiom,(
% 18.96/2.78    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 18.96/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 18.96/2.78  fof(f120,plain,(
% 18.96/2.78    v1_relat_1(sK2) | ~spl15_1),
% 18.96/2.78    inference(avatar_component_clause,[],[f118])).
% 18.96/2.78  fof(f549,plain,(
% 18.96/2.78    spl15_37 | ~spl15_2 | ~spl15_18),
% 18.96/2.78    inference(avatar_split_clause,[],[f269,f263,f123,f546])).
% 18.96/2.78  fof(f546,plain,(
% 18.96/2.78    spl15_37 <=> k4_tarski(sK0,sK1) = k4_tarski(sK0,sK10(sK2,sK0))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_37])])).
% 18.96/2.78  fof(f539,plain,(
% 18.96/2.78    spl15_36 | ~spl15_2 | ~spl15_16),
% 18.96/2.78    inference(avatar_split_clause,[],[f248,f242,f123,f536])).
% 18.96/2.78  fof(f536,plain,(
% 18.96/2.78    spl15_36 <=> k4_tarski(sK0,sK1) = k4_tarski(sK5(sK2,sK1),sK1)),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_36])])).
% 18.96/2.78  fof(f242,plain,(
% 18.96/2.78    spl15_16 <=> r2_hidden(k4_tarski(sK5(sK2,sK1),sK1),sK2)),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).
% 18.96/2.78  fof(f248,plain,(
% 18.96/2.78    k4_tarski(sK0,sK1) = k4_tarski(sK5(sK2,sK1),sK1) | (~spl15_2 | ~spl15_16)),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f244,f150])).
% 18.96/2.78  fof(f244,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK5(sK2,sK1),sK1),sK2) | ~spl15_16),
% 18.96/2.78    inference(avatar_component_clause,[],[f242])).
% 18.96/2.78  fof(f514,plain,(
% 18.96/2.78    spl15_35 | ~spl15_14),
% 18.96/2.78    inference(avatar_split_clause,[],[f238,f222,f511])).
% 18.96/2.78  fof(f222,plain,(
% 18.96/2.78    spl15_14 <=> r2_hidden(sK6(sK2),k2_relat_1(sK2))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).
% 18.96/2.78  fof(f238,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK5(sK2,sK6(sK2)),sK6(sK2)),sK2) | ~spl15_14),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f224,f108])).
% 18.96/2.78  fof(f224,plain,(
% 18.96/2.78    r2_hidden(sK6(sK2),k2_relat_1(sK2)) | ~spl15_14),
% 18.96/2.78    inference(avatar_component_clause,[],[f222])).
% 18.96/2.78  fof(f506,plain,(
% 18.96/2.78    spl15_34 | ~spl15_2),
% 18.96/2.78    inference(avatar_split_clause,[],[f295,f123,f503])).
% 18.96/2.78  fof(f503,plain,(
% 18.96/2.78    spl15_34 <=> r2_hidden(k4_tarski(sK0,sK1),k1_relat_1(k2_zfmisc_1(sK2,sK2)))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_34])])).
% 18.96/2.78  fof(f295,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK0,sK1),k1_relat_1(k2_zfmisc_1(sK2,sK2))) | ~spl15_2),
% 18.96/2.78    inference(superposition,[],[f194,f125])).
% 18.96/2.78  fof(f194,plain,(
% 18.96/2.78    ( ! [X0] : (r2_hidden(k4_tarski(sK0,sK1),k1_relat_1(k2_zfmisc_1(sK2,k1_tarski(X0))))) ) | ~spl15_2),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f190,f109])).
% 18.96/2.78  fof(f190,plain,(
% 18.96/2.78    ( ! [X0] : (r2_hidden(k4_tarski(k4_tarski(sK0,sK1),X0),k2_zfmisc_1(sK2,k1_tarski(X0)))) ) | ~spl15_2),
% 18.96/2.78    inference(superposition,[],[f115,f125])).
% 18.96/2.78  fof(f115,plain,(
% 18.96/2.78    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 18.96/2.78    inference(equality_resolution,[],[f114])).
% 18.96/2.78  fof(f114,plain,(
% 18.96/2.78    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X0 != X2) )),
% 18.96/2.78    inference(equality_resolution,[],[f101])).
% 18.96/2.78  fof(f101,plain,(
% 18.96/2.78    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) )),
% 18.96/2.78    inference(cnf_transformation,[],[f74])).
% 18.96/2.78  fof(f491,plain,(
% 18.96/2.78    ~spl15_33 | spl15_29),
% 18.96/2.78    inference(avatar_split_clause,[],[f439,f429,f488])).
% 18.96/2.78  fof(f488,plain,(
% 18.96/2.78    spl15_33 <=> r2_hidden(sK1,k1_tarski(sK11(sK1,k2_relat_1(sK2))))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_33])])).
% 18.96/2.78  fof(f439,plain,(
% 18.96/2.78    ~r2_hidden(sK1,k1_tarski(sK11(sK1,k2_relat_1(sK2)))) | spl15_29),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f431,f113])).
% 18.96/2.78  fof(f474,plain,(
% 18.96/2.78    spl15_32 | ~spl15_4 | ~spl15_14),
% 18.96/2.78    inference(avatar_split_clause,[],[f460,f222,f132,f471])).
% 18.96/2.78  fof(f471,plain,(
% 18.96/2.78    spl15_32 <=> r2_hidden(sK6(sK2),k1_tarski(sK1))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_32])])).
% 18.96/2.78  fof(f460,plain,(
% 18.96/2.78    r2_hidden(sK6(sK2),k1_tarski(sK1)) | (~spl15_4 | ~spl15_14)),
% 18.96/2.78    inference(superposition,[],[f224,f133])).
% 18.96/2.78  fof(f133,plain,(
% 18.96/2.78    k1_tarski(sK1) = k2_relat_1(sK2) | ~spl15_4),
% 18.96/2.78    inference(avatar_component_clause,[],[f132])).
% 18.96/2.78  fof(f457,plain,(
% 18.96/2.78    spl15_31 | spl15_4 | spl15_29),
% 18.96/2.78    inference(avatar_split_clause,[],[f436,f429,f132,f454])).
% 18.96/2.78  fof(f436,plain,(
% 18.96/2.78    r2_hidden(sK11(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | (spl15_4 | spl15_29)),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f134,f431,f95])).
% 18.96/2.78  fof(f95,plain,(
% 18.96/2.78    ( ! [X0,X1] : (r2_hidden(sK11(X0,X1),X1) | sK11(X0,X1) = X0 | k1_tarski(X0) = X1) )),
% 18.96/2.78    inference(cnf_transformation,[],[f69])).
% 18.96/2.78  fof(f452,plain,(
% 18.96/2.78    ~spl15_30 | spl15_29),
% 18.96/2.78    inference(avatar_split_clause,[],[f435,f429,f449])).
% 18.96/2.78  fof(f449,plain,(
% 18.96/2.78    spl15_30 <=> r2_hidden(sK11(sK1,k2_relat_1(sK2)),k1_tarski(sK1))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_30])])).
% 18.96/2.78  fof(f435,plain,(
% 18.96/2.78    ~r2_hidden(sK11(sK1,k2_relat_1(sK2)),k1_tarski(sK1)) | spl15_29),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f431,f113])).
% 18.96/2.78  fof(f432,plain,(
% 18.96/2.78    ~spl15_29 | spl15_4 | ~spl15_9),
% 18.96/2.78    inference(avatar_split_clause,[],[f379,f173,f132,f429])).
% 18.96/2.78  fof(f173,plain,(
% 18.96/2.78    spl15_9 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_9])])).
% 18.96/2.78  fof(f379,plain,(
% 18.96/2.78    sK1 != sK11(sK1,k2_relat_1(sK2)) | (spl15_4 | ~spl15_9)),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f175,f134,f116])).
% 18.96/2.78  fof(f116,plain,(
% 18.96/2.78    ( ! [X0,X1] : (sK11(X0,X1) != X0 | k1_tarski(X0) = X1 | ~r2_hidden(X0,X1)) )),
% 18.96/2.78    inference(inner_rewriting,[],[f96])).
% 18.96/2.78  fof(f96,plain,(
% 18.96/2.78    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK11(X0,X1) != X0 | ~r2_hidden(sK11(X0,X1),X1)) )),
% 18.96/2.78    inference(cnf_transformation,[],[f69])).
% 18.96/2.78  fof(f175,plain,(
% 18.96/2.78    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl15_9),
% 18.96/2.78    inference(avatar_component_clause,[],[f173])).
% 18.96/2.78  fof(f416,plain,(
% 18.96/2.78    ~spl15_28 | spl15_4),
% 18.96/2.78    inference(avatar_split_clause,[],[f385,f132,f413])).
% 18.96/2.78  fof(f413,plain,(
% 18.96/2.78    spl15_28 <=> r2_hidden(k1_tarski(sK1),k1_tarski(k2_relat_1(sK2)))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_28])])).
% 18.96/2.78  fof(f385,plain,(
% 18.96/2.78    ~r2_hidden(k1_tarski(sK1),k1_tarski(k2_relat_1(sK2))) | spl15_4),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f134,f113])).
% 18.96/2.78  fof(f411,plain,(
% 18.96/2.78    ~spl15_27 | spl15_4),
% 18.96/2.78    inference(avatar_split_clause,[],[f382,f132,f408])).
% 18.96/2.78  fof(f408,plain,(
% 18.96/2.78    spl15_27 <=> r2_hidden(k2_relat_1(sK2),k1_tarski(k1_tarski(sK1)))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_27])])).
% 18.96/2.78  fof(f382,plain,(
% 18.96/2.78    ~r2_hidden(k2_relat_1(sK2),k1_tarski(k1_tarski(sK1))) | spl15_4),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f134,f113])).
% 18.96/2.78  fof(f394,plain,(
% 18.96/2.78    spl15_26 | ~spl15_3 | ~spl15_15),
% 18.96/2.78    inference(avatar_split_clause,[],[f371,f229,f128,f391])).
% 18.96/2.78  fof(f391,plain,(
% 18.96/2.78    spl15_26 <=> r2_hidden(sK7(sK2),k1_tarski(sK0))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_26])])).
% 18.96/2.78  fof(f371,plain,(
% 18.96/2.78    r2_hidden(sK7(sK2),k1_tarski(sK0)) | (~spl15_3 | ~spl15_15)),
% 18.96/2.78    inference(superposition,[],[f231,f129])).
% 18.96/2.78  fof(f366,plain,(
% 18.96/2.78    spl15_25 | spl15_3 | spl15_21),
% 18.96/2.78    inference(avatar_split_clause,[],[f359,f320,f128,f363])).
% 18.96/2.78  fof(f359,plain,(
% 18.96/2.78    r2_hidden(sK11(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) | (spl15_3 | spl15_21)),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f130,f322,f95])).
% 18.96/2.78  fof(f357,plain,(
% 18.96/2.78    spl15_24 | ~spl15_2),
% 18.96/2.78    inference(avatar_split_clause,[],[f352,f123,f354])).
% 18.96/2.78  fof(f354,plain,(
% 18.96/2.78    spl15_24 <=> r2_hidden(sK1,k2_relat_1(k1_relat_1(k2_zfmisc_1(sK2,sK2))))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_24])])).
% 18.96/2.78  fof(f352,plain,(
% 18.96/2.78    r2_hidden(sK1,k2_relat_1(k1_relat_1(k2_zfmisc_1(sK2,sK2)))) | ~spl15_2),
% 18.96/2.78    inference(superposition,[],[f293,f125])).
% 18.96/2.78  fof(f293,plain,(
% 18.96/2.78    ( ! [X0] : (r2_hidden(sK1,k2_relat_1(k1_relat_1(k2_zfmisc_1(sK2,k1_tarski(X0)))))) ) | ~spl15_2),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f194,f107])).
% 18.96/2.78  fof(f346,plain,(
% 18.96/2.78    ~spl15_23 | spl15_21),
% 18.96/2.78    inference(avatar_split_clause,[],[f329,f320,f343])).
% 18.96/2.78  fof(f343,plain,(
% 18.96/2.78    spl15_23 <=> r2_hidden(sK0,k1_tarski(sK11(sK0,k1_relat_1(sK2))))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_23])])).
% 18.96/2.78  fof(f329,plain,(
% 18.96/2.78    ~r2_hidden(sK0,k1_tarski(sK11(sK0,k1_relat_1(sK2)))) | spl15_21),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f322,f113])).
% 18.96/2.78  fof(f338,plain,(
% 18.96/2.78    ~spl15_22 | spl15_21),
% 18.96/2.78    inference(avatar_split_clause,[],[f326,f320,f335])).
% 18.96/2.78  fof(f335,plain,(
% 18.96/2.78    spl15_22 <=> r2_hidden(sK11(sK0,k1_relat_1(sK2)),k1_tarski(sK0))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).
% 18.96/2.78  fof(f326,plain,(
% 18.96/2.78    ~r2_hidden(sK11(sK0,k1_relat_1(sK2)),k1_tarski(sK0)) | spl15_21),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f322,f113])).
% 18.96/2.78  fof(f323,plain,(
% 18.96/2.78    ~spl15_21 | spl15_3 | ~spl15_10),
% 18.96/2.78    inference(avatar_split_clause,[],[f318,f182,f128,f320])).
% 18.96/2.78  fof(f182,plain,(
% 18.96/2.78    spl15_10 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_10])])).
% 18.96/2.78  fof(f318,plain,(
% 18.96/2.78    sK0 != sK11(sK0,k1_relat_1(sK2)) | (spl15_3 | ~spl15_10)),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f184,f130,f116])).
% 18.96/2.78  fof(f184,plain,(
% 18.96/2.78    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl15_10),
% 18.96/2.78    inference(avatar_component_clause,[],[f182])).
% 18.96/2.78  fof(f316,plain,(
% 18.96/2.78    spl15_20 | ~spl15_2),
% 18.96/2.78    inference(avatar_split_clause,[],[f311,f123,f313])).
% 18.96/2.78  fof(f313,plain,(
% 18.96/2.78    spl15_20 <=> r2_hidden(sK0,k1_relat_1(k1_relat_1(k2_zfmisc_1(sK2,sK2))))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).
% 18.96/2.78  fof(f311,plain,(
% 18.96/2.78    r2_hidden(sK0,k1_relat_1(k1_relat_1(k2_zfmisc_1(sK2,sK2)))) | ~spl15_2),
% 18.96/2.78    inference(superposition,[],[f292,f125])).
% 18.96/2.78  fof(f292,plain,(
% 18.96/2.78    ( ! [X0] : (r2_hidden(sK0,k1_relat_1(k1_relat_1(k2_zfmisc_1(sK2,k1_tarski(X0)))))) ) | ~spl15_2),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f194,f109])).
% 18.96/2.78  fof(f289,plain,(
% 18.96/2.78    spl15_19 | ~spl15_18),
% 18.96/2.78    inference(avatar_split_clause,[],[f268,f263,f286])).
% 18.96/2.78  fof(f286,plain,(
% 18.96/2.78    spl15_19 <=> r2_hidden(sK10(sK2,sK0),k2_relat_1(sK2))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).
% 18.96/2.78  fof(f268,plain,(
% 18.96/2.78    r2_hidden(sK10(sK2,sK0),k2_relat_1(sK2)) | ~spl15_18),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f265,f107])).
% 18.96/2.78  fof(f266,plain,(
% 18.96/2.78    spl15_18 | ~spl15_10),
% 18.96/2.78    inference(avatar_split_clause,[],[f255,f182,f263])).
% 18.96/2.78  fof(f255,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK0,sK10(sK2,sK0)),sK2) | ~spl15_10),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f184,f110])).
% 18.96/2.78  fof(f254,plain,(
% 18.96/2.78    spl15_17 | ~spl15_16),
% 18.96/2.78    inference(avatar_split_clause,[],[f246,f242,f251])).
% 18.96/2.78  fof(f246,plain,(
% 18.96/2.78    r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | ~spl15_16),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f244,f109])).
% 18.96/2.78  fof(f245,plain,(
% 18.96/2.78    spl15_16 | ~spl15_9),
% 18.96/2.78    inference(avatar_split_clause,[],[f236,f173,f242])).
% 18.96/2.78  fof(f236,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK5(sK2,sK1),sK1),sK2) | ~spl15_9),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f175,f108])).
% 18.96/2.78  fof(f232,plain,(
% 18.96/2.78    spl15_15 | ~spl15_1 | ~spl15_14),
% 18.96/2.78    inference(avatar_split_clause,[],[f227,f222,f118,f229])).
% 18.96/2.78  fof(f227,plain,(
% 18.96/2.78    r2_hidden(sK7(sK2),k1_relat_1(sK2)) | (~spl15_1 | ~spl15_14)),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f120,f224,f87])).
% 18.96/2.78  fof(f87,plain,(
% 18.96/2.78    ( ! [X0,X1] : (r2_hidden(sK7(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 18.96/2.78    inference(cnf_transformation,[],[f59])).
% 18.96/2.78  fof(f59,plain,(
% 18.96/2.78    ! [X0,X1] : (r2_hidden(sK7(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 18.96/2.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f58])).
% 18.96/2.78  fof(f58,plain,(
% 18.96/2.78    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK7(X1),k1_relat_1(X1)))),
% 18.96/2.78    introduced(choice_axiom,[])).
% 18.96/2.78  fof(f43,plain,(
% 18.96/2.78    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 18.96/2.78    inference(flattening,[],[f42])).
% 18.96/2.78  fof(f42,plain,(
% 18.96/2.78    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 18.96/2.78    inference(ennf_transformation,[],[f33])).
% 18.96/2.78  fof(f33,axiom,(
% 18.96/2.78    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 18.96/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 18.96/2.78  fof(f225,plain,(
% 18.96/2.78    spl15_14 | ~spl15_1 | ~spl15_10),
% 18.96/2.78    inference(avatar_split_clause,[],[f220,f182,f118,f222])).
% 18.96/2.78  fof(f220,plain,(
% 18.96/2.78    r2_hidden(sK6(sK2),k2_relat_1(sK2)) | (~spl15_1 | ~spl15_10)),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f120,f184,f86])).
% 18.96/2.78  fof(f86,plain,(
% 18.96/2.78    ( ! [X0,X1] : (r2_hidden(sK6(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 18.96/2.78    inference(cnf_transformation,[],[f57])).
% 18.96/2.78  fof(f57,plain,(
% 18.96/2.78    ! [X0,X1] : (r2_hidden(sK6(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 18.96/2.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f56])).
% 18.96/2.78  fof(f56,plain,(
% 18.96/2.78    ! [X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(sK6(X1),k2_relat_1(X1)))),
% 18.96/2.78    introduced(choice_axiom,[])).
% 18.96/2.78  fof(f41,plain,(
% 18.96/2.78    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 18.96/2.78    inference(flattening,[],[f40])).
% 18.96/2.78  fof(f40,plain,(
% 18.96/2.78    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 18.96/2.78    inference(ennf_transformation,[],[f32])).
% 18.96/2.78  fof(f32,axiom,(
% 18.96/2.78    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 18.96/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).
% 18.96/2.78  fof(f219,plain,(
% 18.96/2.78    spl15_13 | ~spl15_11),
% 18.96/2.78    inference(avatar_split_clause,[],[f209,f201,f216])).
% 18.96/2.78  fof(f216,plain,(
% 18.96/2.78    spl15_13 <=> r2_hidden(sK1,k2_relat_1(k2_relat_1(k2_zfmisc_1(sK2,sK2))))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).
% 18.96/2.78  fof(f201,plain,(
% 18.96/2.78    spl15_11 <=> r2_hidden(k4_tarski(sK0,sK1),k2_relat_1(k2_zfmisc_1(sK2,sK2)))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_11])])).
% 18.96/2.78  fof(f209,plain,(
% 18.96/2.78    r2_hidden(sK1,k2_relat_1(k2_relat_1(k2_zfmisc_1(sK2,sK2)))) | ~spl15_11),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f203,f107])).
% 18.96/2.78  fof(f203,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK0,sK1),k2_relat_1(k2_zfmisc_1(sK2,sK2))) | ~spl15_11),
% 18.96/2.78    inference(avatar_component_clause,[],[f201])).
% 18.96/2.78  fof(f214,plain,(
% 18.96/2.78    spl15_12 | ~spl15_11),
% 18.96/2.78    inference(avatar_split_clause,[],[f208,f201,f211])).
% 18.96/2.78  fof(f211,plain,(
% 18.96/2.78    spl15_12 <=> r2_hidden(sK0,k1_relat_1(k2_relat_1(k2_zfmisc_1(sK2,sK2))))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).
% 18.96/2.78  fof(f208,plain,(
% 18.96/2.78    r2_hidden(sK0,k1_relat_1(k2_relat_1(k2_zfmisc_1(sK2,sK2)))) | ~spl15_11),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f203,f109])).
% 18.96/2.78  fof(f204,plain,(
% 18.96/2.78    spl15_11 | ~spl15_2),
% 18.96/2.78    inference(avatar_split_clause,[],[f199,f123,f201])).
% 18.96/2.78  fof(f199,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK0,sK1),k2_relat_1(k2_zfmisc_1(sK2,sK2))) | ~spl15_2),
% 18.96/2.78    inference(superposition,[],[f195,f125])).
% 18.96/2.78  fof(f195,plain,(
% 18.96/2.78    ( ! [X0] : (r2_hidden(X0,k2_relat_1(k2_zfmisc_1(sK2,k1_tarski(X0))))) ) | ~spl15_2),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f190,f107])).
% 18.96/2.78  fof(f185,plain,(
% 18.96/2.78    spl15_10 | ~spl15_5),
% 18.96/2.78    inference(avatar_split_clause,[],[f179,f138,f182])).
% 18.96/2.78  fof(f138,plain,(
% 18.96/2.78    spl15_5 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).
% 18.96/2.78  fof(f179,plain,(
% 18.96/2.78    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl15_5),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f140,f109])).
% 18.96/2.78  fof(f140,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl15_5),
% 18.96/2.78    inference(avatar_component_clause,[],[f138])).
% 18.96/2.78  fof(f176,plain,(
% 18.96/2.78    spl15_9 | ~spl15_5),
% 18.96/2.78    inference(avatar_split_clause,[],[f170,f138,f173])).
% 18.96/2.78  fof(f170,plain,(
% 18.96/2.78    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl15_5),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f140,f107])).
% 18.96/2.78  fof(f169,plain,(
% 18.96/2.78    spl15_8 | ~spl15_1),
% 18.96/2.78    inference(avatar_split_clause,[],[f161,f118,f166])).
% 18.96/2.78  fof(f161,plain,(
% 18.96/2.78    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | ~spl15_1),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f120,f88])).
% 18.96/2.78  fof(f88,plain,(
% 18.96/2.78    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 18.96/2.78    inference(cnf_transformation,[],[f44])).
% 18.96/2.78  fof(f44,plain,(
% 18.96/2.78    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 18.96/2.78    inference(ennf_transformation,[],[f34])).
% 18.96/2.78  fof(f34,axiom,(
% 18.96/2.78    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 18.96/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 18.96/2.78  fof(f160,plain,(
% 18.96/2.78    ~spl15_7 | spl15_3),
% 18.96/2.78    inference(avatar_split_clause,[],[f147,f128,f157])).
% 18.96/2.78  fof(f157,plain,(
% 18.96/2.78    spl15_7 <=> r2_hidden(k1_tarski(sK0),k1_tarski(k1_relat_1(sK2)))),
% 18.96/2.78    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).
% 18.96/2.78  fof(f147,plain,(
% 18.96/2.78    ~r2_hidden(k1_tarski(sK0),k1_tarski(k1_relat_1(sK2))) | spl15_3),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f130,f113])).
% 18.96/2.78  fof(f155,plain,(
% 18.96/2.78    ~spl15_6 | spl15_3),
% 18.96/2.78    inference(avatar_split_clause,[],[f146,f128,f152])).
% 18.96/2.78  fof(f146,plain,(
% 18.96/2.78    ~r2_hidden(k1_relat_1(sK2),k1_tarski(k1_tarski(sK0))) | spl15_3),
% 18.96/2.78    inference(unit_resulting_resolution,[],[f130,f113])).
% 18.96/2.78  fof(f141,plain,(
% 18.96/2.78    spl15_5 | ~spl15_2),
% 18.96/2.78    inference(avatar_split_clause,[],[f136,f123,f138])).
% 18.96/2.78  fof(f136,plain,(
% 18.96/2.78    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl15_2),
% 18.96/2.78    inference(superposition,[],[f112,f125])).
% 18.96/2.78  fof(f135,plain,(
% 18.96/2.78    ~spl15_3 | ~spl15_4),
% 18.96/2.78    inference(avatar_split_clause,[],[f81,f132,f128])).
% 18.96/2.78  fof(f81,plain,(
% 18.96/2.78    k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 18.96/2.78    inference(cnf_transformation,[],[f49])).
% 18.96/2.78  fof(f49,plain,(
% 18.96/2.78    (k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2)),
% 18.96/2.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f48])).
% 18.96/2.78  fof(f48,plain,(
% 18.96/2.78    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2)) => ((k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2))),
% 18.96/2.78    introduced(choice_axiom,[])).
% 18.96/2.78  fof(f39,plain,(
% 18.96/2.78    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 18.96/2.78    inference(flattening,[],[f38])).
% 18.96/2.78  fof(f38,plain,(
% 18.96/2.78    ? [X0,X1,X2] : (((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 18.96/2.78    inference(ennf_transformation,[],[f37])).
% 18.96/2.78  fof(f37,negated_conjecture,(
% 18.96/2.78    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 18.96/2.78    inference(negated_conjecture,[],[f36])).
% 18.96/2.78  fof(f36,conjecture,(
% 18.96/2.78    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 18.96/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).
% 18.96/2.78  fof(f126,plain,(
% 18.96/2.78    spl15_2),
% 18.96/2.78    inference(avatar_split_clause,[],[f80,f123])).
% 18.96/2.78  fof(f80,plain,(
% 18.96/2.78    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 18.96/2.78    inference(cnf_transformation,[],[f49])).
% 18.96/2.78  fof(f121,plain,(
% 18.96/2.78    spl15_1),
% 18.96/2.78    inference(avatar_split_clause,[],[f79,f118])).
% 18.96/2.78  fof(f79,plain,(
% 18.96/2.78    v1_relat_1(sK2)),
% 18.96/2.78    inference(cnf_transformation,[],[f49])).
% 18.96/2.78  % SZS output end Proof for theBenchmark
% 18.96/2.78  % (933)------------------------------
% 18.96/2.78  % (933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.96/2.78  % (933)Termination reason: Refutation
% 18.96/2.78  
% 18.96/2.78  % (933)Memory used [KB]: 7036
% 18.96/2.78  % (933)Time elapsed: 0.362 s
% 18.96/2.78  % (933)------------------------------
% 18.96/2.78  % (933)------------------------------
% 18.96/2.79  % (596)Success in time 2.405 s
%------------------------------------------------------------------------------

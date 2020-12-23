%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0569+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:37 EST 2020

% Result     : Theorem 13.62s
% Output     : Refutation 14.49s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 234 expanded)
%              Number of leaves         :   34 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  458 ( 719 expanded)
%              Number of equality atoms :  102 ( 188 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12498,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1377,f1423,f1453,f1496,f1661,f1791,f2343,f5431,f6753,f10172,f11915,f12497])).

fof(f12497,plain,
    ( ~ spl27_1
    | ~ spl27_2
    | ~ spl27_4
    | ~ spl27_24
    | ~ spl27_71 ),
    inference(avatar_contradiction_clause,[],[f12496])).

fof(f12496,plain,
    ( $false
    | ~ spl27_1
    | ~ spl27_2
    | ~ spl27_4
    | ~ spl27_24
    | ~ spl27_71 ),
    inference(subsumption_resolution,[],[f12495,f1838])).

fof(f1838,plain,
    ( ! [X53] : ~ r2_hidden(X53,k1_xboole_0)
    | ~ spl27_4 ),
    inference(forward_demodulation,[],[f1819,f1813])).

fof(f1813,plain,
    ( ! [X46] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X46)
    | ~ spl27_4 ),
    inference(resolution,[],[f1619,f1125])).

fof(f1125,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1004])).

fof(f1004,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1619,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl27_4 ),
    inference(trivial_inequality_removal,[],[f1618])).

fof(f1618,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k1_xboole_0,X0) )
    | ~ spl27_4 ),
    inference(backward_demodulation,[],[f1613,f1617])).

fof(f1617,plain,
    ( ! [X2] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X2)
    | ~ spl27_4 ),
    inference(forward_demodulation,[],[f1616,f1325])).

fof(f1325,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f1616,plain,
    ( ! [X2] : k7_relat_1(k1_xboole_0,X2) = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl27_4 ),
    inference(forward_demodulation,[],[f1615,f1363])).

fof(f1363,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f1290])).

fof(f1290,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f1065])).

fof(f1065,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f1064])).

fof(f1064,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1615,plain,
    ( ! [X2] : k7_relat_1(k1_xboole_0,X2) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X2,k1_xboole_0))
    | ~ spl27_4 ),
    inference(forward_demodulation,[],[f1581,f1218])).

fof(f1218,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f795])).

fof(f795,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f1581,plain,
    ( ! [X2] : k7_relat_1(k1_xboole_0,X2) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X2,k2_relat_1(k1_xboole_0)))
    | ~ spl27_4 ),
    inference(resolution,[],[f1495,f1189])).

fof(f1189,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f918])).

fof(f918,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f824])).

fof(f824,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(f1495,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl27_4 ),
    inference(avatar_component_clause,[],[f1493])).

fof(f1493,plain,
    ( spl27_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_4])])).

fof(f1613,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) )
    | ~ spl27_4 ),
    inference(forward_demodulation,[],[f1579,f1217])).

fof(f1217,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f795])).

fof(f1579,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
        | r1_xboole_0(k1_relat_1(k1_xboole_0),X0) )
    | ~ spl27_4 ),
    inference(resolution,[],[f1495,f1149])).

fof(f1149,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f1014])).

fof(f1014,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f890])).

fof(f890,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f823])).

fof(f823,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f1819,plain,
    ( ! [X54,X53] : ~ r2_hidden(X53,k3_xboole_0(k1_xboole_0,X54))
    | ~ spl27_4 ),
    inference(resolution,[],[f1619,f1159])).

fof(f1159,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1019])).

fof(f1019,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK9(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f895,f1018])).

fof(f1018,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK9(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f895,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f829])).

fof(f829,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f12495,plain,
    ( r2_hidden(sK12(sK1,sK8(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ spl27_1
    | ~ spl27_2
    | ~ spl27_24
    | ~ spl27_71 ),
    inference(forward_demodulation,[],[f12494,f1418])).

fof(f1418,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl27_2 ),
    inference(avatar_component_clause,[],[f1416])).

fof(f1416,plain,
    ( spl27_2
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_2])])).

fof(f12494,plain,
    ( r2_hidden(sK12(sK1,sK8(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0))
    | ~ spl27_1
    | ~ spl27_24
    | ~ spl27_71 ),
    inference(subsumption_resolution,[],[f12493,f1376])).

fof(f1376,plain,
    ( v1_relat_1(sK1)
    | ~ spl27_1 ),
    inference(avatar_component_clause,[],[f1374])).

fof(f1374,plain,
    ( spl27_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_1])])).

fof(f12493,plain,
    ( r2_hidden(sK12(sK1,sK8(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl27_24
    | ~ spl27_71 ),
    inference(resolution,[],[f5425,f11914])).

fof(f11914,plain,
    ( r2_hidden(k4_tarski(sK12(sK1,sK8(k2_relat_1(sK1),sK0)),sK8(k2_relat_1(sK1),sK0)),sK1)
    | ~ spl27_71 ),
    inference(avatar_component_clause,[],[f11912])).

fof(f11912,plain,
    ( spl27_71
  <=> r2_hidden(k4_tarski(sK12(sK1,sK8(k2_relat_1(sK1),sK0)),sK8(k2_relat_1(sK1),sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_71])])).

fof(f5425,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_tarski(X1,sK8(k2_relat_1(sK1),sK0)),X2)
        | r2_hidden(X1,k10_relat_1(X2,sK0))
        | ~ v1_relat_1(X2) )
    | ~ spl27_24 ),
    inference(resolution,[],[f2342,f1348])).

fof(f1348,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ r2_hidden(X7,X1)
      | r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1233])).

fof(f1233,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1047])).

fof(f1047,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK17(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK17(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK18(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK17(X0,X1,X2),sK18(X0,X1,X2)),X0) )
                | r2_hidden(sK17(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK19(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK19(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18,sK19])],[f1043,f1046,f1045,f1044])).

fof(f1044,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK17(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK17(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK17(X0,X1,X2),X5),X0) )
          | r2_hidden(sK17(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1045,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK17(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK18(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK17(X0,X1,X2),sK18(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1046,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK19(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK19(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1043,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1042])).

fof(f1042,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f951])).

fof(f951,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f644])).

fof(f644,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f2342,plain,
    ( r2_hidden(sK8(k2_relat_1(sK1),sK0),sK0)
    | ~ spl27_24 ),
    inference(avatar_component_clause,[],[f2340])).

fof(f2340,plain,
    ( spl27_24
  <=> r2_hidden(sK8(k2_relat_1(sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_24])])).

fof(f11915,plain,
    ( spl27_71
    | ~ spl27_31 ),
    inference(avatar_split_clause,[],[f5944,f5428,f11912])).

fof(f5428,plain,
    ( spl27_31
  <=> r2_hidden(sK8(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_31])])).

fof(f5944,plain,
    ( r2_hidden(k4_tarski(sK12(sK1,sK8(k2_relat_1(sK1),sK0)),sK8(k2_relat_1(sK1),sK0)),sK1)
    | ~ spl27_31 ),
    inference(resolution,[],[f5430,f1345])).

fof(f1345,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK12(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f1179])).

fof(f1179,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK12(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1027])).

fof(f1027,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK10(X0,X1)),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK12(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f1023,f1026,f1025,f1024])).

fof(f1024,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK10(X0,X1)),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK10(X0,X1)),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1025,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK10(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1026,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK12(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1023,plain,(
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
    inference(rectify,[],[f1022])).

fof(f1022,plain,(
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
    inference(nnf_transformation,[],[f649])).

fof(f649,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f5430,plain,
    ( r2_hidden(sK8(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | ~ spl27_31 ),
    inference(avatar_component_clause,[],[f5428])).

fof(f10172,plain,
    ( ~ spl27_1
    | spl27_2
    | ~ spl27_8
    | ~ spl27_44 ),
    inference(avatar_contradiction_clause,[],[f10171])).

fof(f10171,plain,
    ( $false
    | ~ spl27_1
    | spl27_2
    | ~ spl27_8
    | ~ spl27_44 ),
    inference(subsumption_resolution,[],[f10170,f1417])).

fof(f1417,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl27_2 ),
    inference(avatar_component_clause,[],[f1416])).

fof(f10170,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl27_1
    | ~ spl27_8
    | ~ spl27_44 ),
    inference(forward_demodulation,[],[f10150,f1660])).

fof(f1660,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl27_8 ),
    inference(avatar_component_clause,[],[f1658])).

fof(f1658,plain,
    ( spl27_8
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_8])])).

fof(f10150,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl27_1
    | ~ spl27_44 ),
    inference(superposition,[],[f1413,f6752])).

fof(f6752,plain,
    ( k1_xboole_0 = k2_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl27_44 ),
    inference(avatar_component_clause,[],[f6750])).

fof(f6750,plain,
    ( spl27_44
  <=> k1_xboole_0 = k2_relat_1(k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_44])])).

fof(f1413,plain,
    ( ! [X13] : k10_relat_1(sK1,X13) = k10_relat_1(sK1,k2_relat_1(k8_relat_1(X13,sK1)))
    | ~ spl27_1 ),
    inference(forward_demodulation,[],[f1401,f1381])).

fof(f1381,plain,
    ( ! [X3] : k2_relat_1(k8_relat_1(X3,sK1)) = k3_xboole_0(k2_relat_1(sK1),X3)
    | ~ spl27_1 ),
    inference(resolution,[],[f1376,f1190])).

fof(f1190,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f919])).

fof(f919,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f706])).

fof(f706,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f1401,plain,
    ( ! [X13] : k10_relat_1(sK1,X13) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X13))
    | ~ spl27_1 ),
    inference(resolution,[],[f1376,f1228])).

fof(f1228,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f948])).

fof(f948,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f754])).

fof(f754,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f6753,plain,
    ( spl27_44
    | ~ spl27_1
    | ~ spl27_10 ),
    inference(avatar_split_clause,[],[f2242,f1788,f1374,f6750])).

fof(f1788,plain,
    ( spl27_10
  <=> k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_10])])).

fof(f2242,plain,
    ( k1_xboole_0 = k2_relat_1(k8_relat_1(sK0,sK1))
    | ~ spl27_1
    | ~ spl27_10 ),
    inference(superposition,[],[f1381,f1790])).

fof(f1790,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl27_10 ),
    inference(avatar_component_clause,[],[f1788])).

fof(f5431,plain,
    ( spl27_31
    | spl27_3 ),
    inference(avatar_split_clause,[],[f2320,f1420,f5428])).

fof(f1420,plain,
    ( spl27_3
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_3])])).

fof(f2320,plain,
    ( r2_hidden(sK8(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | spl27_3 ),
    inference(resolution,[],[f1421,f1155])).

fof(f1155,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1017])).

fof(f1017,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f894,f1016])).

fof(f1016,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f894,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f828])).

fof(f828,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,axiom,(
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

fof(f1421,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl27_3 ),
    inference(avatar_component_clause,[],[f1420])).

fof(f2343,plain,
    ( spl27_24
    | spl27_3 ),
    inference(avatar_split_clause,[],[f2321,f1420,f2340])).

fof(f2321,plain,
    ( r2_hidden(sK8(k2_relat_1(sK1),sK0),sK0)
    | spl27_3 ),
    inference(resolution,[],[f1421,f1156])).

fof(f1156,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1017])).

fof(f1791,plain,
    ( spl27_10
    | ~ spl27_3 ),
    inference(avatar_split_clause,[],[f1444,f1420,f1788])).

fof(f1444,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl27_3 ),
    inference(resolution,[],[f1422,f1125])).

fof(f1422,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl27_3 ),
    inference(avatar_component_clause,[],[f1420])).

fof(f1661,plain,
    ( spl27_8
    | ~ spl27_1 ),
    inference(avatar_split_clause,[],[f1407,f1374,f1658])).

fof(f1407,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl27_1 ),
    inference(resolution,[],[f1376,f1238])).

fof(f1238,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f953])).

fof(f953,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f757])).

fof(f757,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(f1496,plain,
    ( spl27_4
    | ~ spl27_1 ),
    inference(avatar_split_clause,[],[f1488,f1374,f1493])).

fof(f1488,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl27_1 ),
    inference(superposition,[],[f1410,f1325])).

fof(f1410,plain,
    ( ! [X21] : v1_relat_1(k3_xboole_0(sK1,X21))
    | ~ spl27_1 ),
    inference(resolution,[],[f1376,f1334])).

fof(f1334,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f992])).

fof(f992,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f679])).

fof(f679,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f1453,plain,
    ( ~ spl27_2
    | ~ spl27_3 ),
    inference(avatar_split_clause,[],[f1080,f1420,f1416])).

fof(f1080,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f999])).

fof(f999,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f997,f998])).

fof(f998,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f997,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f996])).

fof(f996,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f830])).

fof(f830,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f760])).

fof(f760,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f759])).

fof(f759,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f1423,plain,
    ( spl27_2
    | spl27_3 ),
    inference(avatar_split_clause,[],[f1079,f1420,f1416])).

fof(f1079,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f999])).

fof(f1377,plain,(
    spl27_1 ),
    inference(avatar_split_clause,[],[f1078,f1374])).

fof(f1078,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f999])).
%------------------------------------------------------------------------------

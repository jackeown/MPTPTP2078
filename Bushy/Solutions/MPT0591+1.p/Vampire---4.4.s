%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t195_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:57 EDT 2019

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 500 expanded)
%              Number of leaves         :   16 ( 166 expanded)
%              Depth                    :   18
%              Number of atoms          :  306 (2245 expanded)
%              Number of equality atoms :   82 ( 396 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14752,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f10643,f14751])).

fof(f14751,plain,(
    spl10_3 ),
    inference(avatar_contradiction_clause,[],[f14719])).

fof(f14719,plain,
    ( $false
    | ~ spl10_3 ),
    inference(resolution,[],[f14478,f13587])).

fof(f13587,plain,
    ( v1_xboole_0(k1_relat_1(sK0))
    | ~ spl10_3 ),
    inference(resolution,[],[f13216,f279])).

fof(f279,plain,(
    ! [X12] :
      ( ~ v1_xboole_0(k2_relat_1(X12))
      | v1_xboole_0(k1_relat_1(X12)) ) ),
    inference(resolution,[],[f169,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t195_relat_1.p',d1_xboole_0)).

fof(f169,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,k1_relat_1(X10))
      | ~ v1_xboole_0(k2_relat_1(X10)) ) ),
    inference(resolution,[],[f98,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f78,f79])).

fof(f79,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f46,f49,f48,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t195_relat_1.p',d5_relat_1)).

fof(f78,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f43,f42,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t195_relat_1.p',d4_relat_1)).

fof(f13216,plain,
    ( v1_xboole_0(k2_relat_1(sK0))
    | ~ spl10_3 ),
    inference(resolution,[],[f11895,f59])).

fof(f11895,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK0))
    | ~ spl10_3 ),
    inference(resolution,[],[f10656,f80])).

fof(f80,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10656,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl10_3 ),
    inference(trivial_inequality_removal,[],[f10644])).

fof(f10644,plain,
    ( ! [X0] :
        ( sK1 != sK1
        | ~ r2_hidden(X0,sK0) )
    | ~ spl10_3 ),
    inference(superposition,[],[f86,f1724])).

fof(f1724,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f1723,f422])).

fof(f422,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(k2_zfmisc_1(X0,X1),X1),X1)
      | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 ) ),
    inference(factoring,[],[f145])).

fof(f145,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK7(k2_zfmisc_1(X6,X7),X8),X8)
      | k2_relat_1(k2_zfmisc_1(X6,X7)) = X8
      | r2_hidden(sK7(k2_zfmisc_1(X6,X7),X8),X7) ) ),
    inference(resolution,[],[f70,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t195_relat_1.p',t106_zfmisc_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1723,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | ~ r2_hidden(sK7(k2_zfmisc_1(X0,X1),X1),X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f1697])).

fof(f1697,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | ~ r2_hidden(sK7(k2_zfmisc_1(X0,X1),X1),X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f422,f126])).

fof(f126,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(sK7(k2_zfmisc_1(X2,X3),X4),X4)
      | k2_relat_1(k2_zfmisc_1(X2,X3)) = X4
      | ~ r2_hidden(sK7(k2_zfmisc_1(X2,X3),X4),X3)
      | ~ r2_hidden(X5,X2) ) ),
    inference(resolution,[],[f71,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,
    ( k2_relat_1(k2_zfmisc_1(sK0,sK1)) != sK1
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl10_3
  <=> k2_relat_1(k2_zfmisc_1(sK0,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f14478,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f14469,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t195_relat_1.p',t6_boole)).

fof(f14469,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | ~ v1_xboole_0(X0) )
    | ~ spl10_3 ),
    inference(superposition,[],[f53,f11965])).

fof(f11965,plain,
    ( ! [X63] :
        ( sK0 = X63
        | ~ v1_xboole_0(X63) )
    | ~ spl10_3 ),
    inference(backward_demodulation,[],[f11933,f11936])).

fof(f11936,plain,
    ( ! [X62,X63] :
        ( k2_relat_1(k2_zfmisc_1(X62,sK0)) = X63
        | ~ v1_xboole_0(X63) )
    | ~ spl10_3 ),
    inference(resolution,[],[f10656,f411])).

fof(f411,plain,(
    ! [X10,X8,X9] :
      ( r2_hidden(sK7(k2_zfmisc_1(X8,X9),X10),X9)
      | k2_relat_1(k2_zfmisc_1(X8,X9)) = X10
      | ~ v1_xboole_0(X10) ) ),
    inference(resolution,[],[f145,f58])).

fof(f11933,plain,
    ( ! [X59] : k2_relat_1(k2_zfmisc_1(X59,sK0)) = sK0
    | ~ spl10_3 ),
    inference(resolution,[],[f10656,f422])).

fof(f53,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( k2_relat_1(k2_zfmisc_1(sK0,sK1)) != sK1
      | k1_relat_1(k2_zfmisc_1(sK0,sK1)) != sK0 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
          | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ( k2_relat_1(k2_zfmisc_1(sK0,sK1)) != sK1
        | k1_relat_1(k2_zfmisc_1(sK0,sK1)) != sK0 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t195_relat_1.p',t195_relat_1)).

fof(f10643,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f10613])).

fof(f10613,plain,
    ( $false
    | ~ spl10_1 ),
    inference(resolution,[],[f10090,f8740])).

fof(f8740,plain,
    ( v1_xboole_0(k1_relat_1(sK1))
    | ~ spl10_1 ),
    inference(resolution,[],[f7920,f279])).

fof(f7920,plain,
    ( v1_xboole_0(k2_relat_1(sK1))
    | ~ spl10_1 ),
    inference(resolution,[],[f6457,f59])).

fof(f6457,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK1))
    | ~ spl10_1 ),
    inference(resolution,[],[f6291,f80])).

fof(f6291,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl10_1 ),
    inference(trivial_inequality_removal,[],[f6283])).

fof(f6283,plain,
    ( ! [X0] :
        ( sK0 != sK0
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_1 ),
    inference(superposition,[],[f83,f1696])).

fof(f1696,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | ~ r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f1695,f406])).

fof(f406,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k2_zfmisc_1(X0,X1),X0),X0)
      | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 ) ),
    inference(factoring,[],[f131])).

fof(f131,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(sK4(k2_zfmisc_1(X9,X10),X11),X11)
      | k1_relat_1(k2_zfmisc_1(X9,X10)) = X11
      | r2_hidden(sK4(k2_zfmisc_1(X9,X10),X11),X9) ) ),
    inference(resolution,[],[f66,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1695,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(sK4(k2_zfmisc_1(X0,X1),X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f1669])).

fof(f1669,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(sK4(k2_zfmisc_1(X0,X1),X0),X0) ) ),
    inference(resolution,[],[f406,f124])).

fof(f124,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(sK4(k2_zfmisc_1(X2,X3),X4),X4)
      | k1_relat_1(k2_zfmisc_1(X2,X3)) = X4
      | ~ r2_hidden(X5,X3)
      | ~ r2_hidden(sK4(k2_zfmisc_1(X2,X3),X4),X2) ) ),
    inference(resolution,[],[f67,f76])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
      | k1_relat_1(X0) = X1
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,
    ( k1_relat_1(k2_zfmisc_1(sK0,sK1)) != sK0
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl10_1
  <=> k1_relat_1(k2_zfmisc_1(sK0,sK1)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f10090,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f10081,f57])).

fof(f10081,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | ~ v1_xboole_0(X0) )
    | ~ spl10_1 ),
    inference(superposition,[],[f54,f6527])).

fof(f6527,plain,
    ( ! [X13] :
        ( sK1 = X13
        | ~ v1_xboole_0(X13) )
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f6468,f6467])).

fof(f6467,plain,
    ( ! [X11] : k1_relat_1(k2_zfmisc_1(sK1,X11)) = sK1
    | ~ spl10_1 ),
    inference(resolution,[],[f6291,f406])).

fof(f6468,plain,
    ( ! [X12,X13] :
        ( k1_relat_1(k2_zfmisc_1(sK1,X12)) = X13
        | ~ v1_xboole_0(X13) )
    | ~ spl10_1 ),
    inference(resolution,[],[f6291,f395])).

fof(f395,plain,(
    ! [X10,X8,X9] :
      ( r2_hidden(sK4(k2_zfmisc_1(X8,X9),X10),X8)
      | k1_relat_1(k2_zfmisc_1(X8,X9)) = X10
      | ~ v1_xboole_0(X10) ) ),
    inference(resolution,[],[f131,f58])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f55,f85,f82])).

fof(f55,plain,
    ( k2_relat_1(k2_zfmisc_1(sK0,sK1)) != sK1
    | k1_relat_1(k2_zfmisc_1(sK0,sK1)) != sK0 ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------

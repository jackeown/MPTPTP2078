%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 332 expanded)
%              Number of leaves         :   47 ( 135 expanded)
%              Depth                    :   11
%              Number of atoms          :  392 ( 628 expanded)
%              Number of equality atoms :   77 ( 215 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f91,f95,f99,f103,f108,f116,f121,f126,f130,f142,f146,f155,f159,f165,f170,f174,f181,f190,f196,f202,f222,f231,f235])).

fof(f235,plain,
    ( ~ spl2_2
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f86,f150])).

fof(f150,plain,
    ( ! [X0] : ~ l1_orders_2(X0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl2_15
  <=> ! [X0] : ~ l1_orders_2(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f86,plain,
    ( l1_orders_2(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_2
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f231,plain,
    ( ~ spl2_8
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_16
    | spl2_19
    | ~ spl2_21
    | ~ spl2_25
    | ~ spl2_29 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_16
    | spl2_19
    | ~ spl2_21
    | ~ spl2_25
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f229,f169])).

fof(f169,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0)))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl2_19
  <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f229,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_25
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f228,f201])).

fof(f201,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl2_25
  <=> k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f228,plain,
    ( g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f227,f115])).

fof(f115,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl2_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f227,plain,
    ( g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f226,f180])).

fof(f180,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl2_21
  <=> v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f226,plain,
    ( g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f225,f120])).

fof(f120,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl2_9
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f225,plain,
    ( g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f224,f125])).

fof(f125,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl2_10
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f224,plain,
    ( g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl2_16
    | ~ spl2_29 ),
    inference(resolution,[],[f221,f154])).

fof(f154,plain,
    ( v1_yellow_1(k1_xboole_0)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl2_16
  <=> v1_yellow_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ v1_yellow_1(X0)
        | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0)))
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl2_29
  <=> ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0)))
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f222,plain,(
    spl2_29 ),
    inference(avatar_split_clause,[],[f77,f220])).

fof(f77,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f74,f71])).

fof(f71,plain,(
    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f42,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f74,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f68,f68])).

fof(f51,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f202,plain,
    ( spl2_25
    | ~ spl2_13
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f197,f194,f140,f199])).

fof(f140,plain,
    ( spl2_13
  <=> ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f194,plain,
    ( spl2_24
  <=> ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f197,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_13
    | ~ spl2_24 ),
    inference(superposition,[],[f195,f141])).

fof(f141,plain,
    ( ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f195,plain,
    ( ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f196,plain,
    ( spl2_24
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f191,f188,f79,f194])).

fof(f79,plain,
    ( spl2_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f188,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f191,plain,
    ( ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(resolution,[],[f189,f81])).

fof(f81,plain,
    ( l1_orders_2(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X1)
        | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f188])).

fof(f190,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f75,f188])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(definition_unfolding,[],[f55,f52])).

fof(f52,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f181,plain,
    ( spl2_21
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f176,f172,f162,f178])).

fof(f162,plain,
    ( spl2_18
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f172,plain,
    ( spl2_20
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f176,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(resolution,[],[f173,f164])).

fof(f164,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f162])).

fof(f173,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f172])).

fof(f174,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f57,f172])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f170,plain,(
    ~ spl2_19 ),
    inference(avatar_split_clause,[],[f76,f167])).

fof(f76,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) ),
    inference(backward_demodulation,[],[f69,f71])).

fof(f69,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f40,f68,f68])).

fof(f40,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f165,plain,
    ( spl2_18
    | ~ spl2_7
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f160,f157,f105,f162])).

fof(f105,plain,
    ( spl2_7
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f157,plain,
    ( spl2_17
  <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f160,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_7
    | ~ spl2_17 ),
    inference(superposition,[],[f158,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f158,plain,
    ( ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f157])).

fof(f159,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f49,f157])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f155,plain,
    ( spl2_15
    | spl2_16
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f147,f144,f140,f152,f149])).

fof(f144,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( v1_yellow_1(k2_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f147,plain,
    ( ! [X0] :
        ( v1_yellow_1(k1_xboole_0)
        | ~ l1_orders_2(X0) )
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(superposition,[],[f145,f141])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( v1_yellow_1(k2_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f54,f144])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

fof(f142,plain,
    ( spl2_13
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f131,f128,f97,f140])).

fof(f97,plain,
    ( spl2_5
  <=> ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f128,plain,
    ( spl2_11
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f131,plain,
    ( ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(resolution,[],[f129,f98])).

fof(f98,plain,
    ( ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f50,f128])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f126,plain,
    ( spl2_10
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f109,f105,f101,f123])).

fof(f101,plain,
    ( spl2_6
  <=> ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f109,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(superposition,[],[f102,f107])).

fof(f102,plain,
    ( ! [X0] : v1_partfun1(k6_partfun1(X0),X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f121,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f111,f105,f89,f118])).

fof(f89,plain,
    ( spl2_3
  <=> ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f111,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(superposition,[],[f90,f107])).

fof(f90,plain,
    ( ! [X0] : v1_funct_1(k6_partfun1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f116,plain,
    ( spl2_8
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f110,f105,f93,f113])).

fof(f93,plain,
    ( spl2_4
  <=> ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f110,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f94,f107])).

fof(f94,plain,
    ( ! [X0] : v1_relat_1(k6_partfun1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f108,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f70,f105])).

fof(f70,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f44,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f41,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f103,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f99,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f43,f97])).

fof(f43,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f95,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f73,f93])).

fof(f73,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f91,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f72,f89])).

fof(f72,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f47,f44])).

fof(f47,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f87,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f62,f84])).

fof(f62,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    l1_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f37])).

fof(f37,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK1) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] : l1_orders_2(X0) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ~ v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( v1_orders_2(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ? [X0] :
      ( v3_orders_2(X0)
      & v1_orders_2(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_0)).

fof(f82,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f39,f79])).

fof(f39,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:06:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (17006)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.44  % (17006)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f236,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f82,f87,f91,f95,f99,f103,f108,f116,f121,f126,f130,f142,f146,f155,f159,f165,f170,f174,f181,f190,f196,f202,f222,f231,f235])).
% 0.21/0.44  fof(f235,plain,(
% 0.21/0.44    ~spl2_2 | ~spl2_15),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.44  fof(f233,plain,(
% 0.21/0.44    $false | (~spl2_2 | ~spl2_15)),
% 0.21/0.44    inference(subsumption_resolution,[],[f86,f150])).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_orders_2(X0)) ) | ~spl2_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f149])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    spl2_15 <=> ! [X0] : ~l1_orders_2(X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    l1_orders_2(sK1) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f84])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    spl2_2 <=> l1_orders_2(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f231,plain,(
% 0.21/0.44    ~spl2_8 | ~spl2_9 | ~spl2_10 | ~spl2_16 | spl2_19 | ~spl2_21 | ~spl2_25 | ~spl2_29),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f230])).
% 0.21/0.44  fof(f230,plain,(
% 0.21/0.44    $false | (~spl2_8 | ~spl2_9 | ~spl2_10 | ~spl2_16 | spl2_19 | ~spl2_21 | ~spl2_25 | ~spl2_29)),
% 0.21/0.44    inference(subsumption_resolution,[],[f229,f169])).
% 0.21/0.44  fof(f169,plain,(
% 0.21/0.44    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) | spl2_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f167])).
% 0.21/0.44  fof(f167,plain,(
% 0.21/0.44    spl2_19 <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.44  fof(f229,plain,(
% 0.21/0.44    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) | (~spl2_8 | ~spl2_9 | ~spl2_10 | ~spl2_16 | ~spl2_21 | ~spl2_25 | ~spl2_29)),
% 0.21/0.44    inference(forward_demodulation,[],[f228,f201])).
% 0.21/0.44  fof(f201,plain,(
% 0.21/0.44    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~spl2_25),
% 0.21/0.44    inference(avatar_component_clause,[],[f199])).
% 0.21/0.44  fof(f199,plain,(
% 0.21/0.44    spl2_25 <=> k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.44  fof(f228,plain,(
% 0.21/0.44    g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | (~spl2_8 | ~spl2_9 | ~spl2_10 | ~spl2_16 | ~spl2_21 | ~spl2_29)),
% 0.21/0.44    inference(subsumption_resolution,[],[f227,f115])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    v1_relat_1(k1_xboole_0) | ~spl2_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f113])).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    spl2_8 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.44  fof(f227,plain,(
% 0.21/0.44    g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl2_9 | ~spl2_10 | ~spl2_16 | ~spl2_21 | ~spl2_29)),
% 0.21/0.44    inference(subsumption_resolution,[],[f226,f180])).
% 0.21/0.44  fof(f180,plain,(
% 0.21/0.44    v4_relat_1(k1_xboole_0,k1_xboole_0) | ~spl2_21),
% 0.21/0.44    inference(avatar_component_clause,[],[f178])).
% 0.21/0.44  fof(f178,plain,(
% 0.21/0.44    spl2_21 <=> v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.44  fof(f226,plain,(
% 0.21/0.44    g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl2_9 | ~spl2_10 | ~spl2_16 | ~spl2_29)),
% 0.21/0.44    inference(subsumption_resolution,[],[f225,f120])).
% 0.21/0.44  fof(f120,plain,(
% 0.21/0.44    v1_funct_1(k1_xboole_0) | ~spl2_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f118])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    spl2_9 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.44  fof(f225,plain,(
% 0.21/0.44    g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl2_10 | ~spl2_16 | ~spl2_29)),
% 0.21/0.44    inference(subsumption_resolution,[],[f224,f125])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl2_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f123])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    spl2_10 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.44  fof(f224,plain,(
% 0.21/0.44    g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl2_16 | ~spl2_29)),
% 0.21/0.44    inference(resolution,[],[f221,f154])).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    v1_yellow_1(k1_xboole_0) | ~spl2_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f152])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    spl2_16 <=> v1_yellow_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.44  fof(f221,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_yellow_1(X0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl2_29),
% 0.21/0.44    inference(avatar_component_clause,[],[f220])).
% 0.21/0.44  fof(f220,plain,(
% 0.21/0.44    spl2_29 <=> ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.44  fof(f222,plain,(
% 0.21/0.44    spl2_29),
% 0.21/0.44    inference(avatar_split_clause,[],[f77,f220])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(forward_demodulation,[],[f74,f71])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.44    inference(definition_unfolding,[],[f42,f68])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f45,f67])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f53,f66])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f56,f65])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f58,f64])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f59,f63])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f60,f61])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f51,f68,f68])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,axiom,(
% 0.21/0.44    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.21/0.44  fof(f202,plain,(
% 0.21/0.44    spl2_25 | ~spl2_13 | ~spl2_24),
% 0.21/0.44    inference(avatar_split_clause,[],[f197,f194,f140,f199])).
% 0.21/0.44  fof(f140,plain,(
% 0.21/0.44    spl2_13 <=> ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.44  fof(f194,plain,(
% 0.21/0.44    spl2_24 <=> ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.44  fof(f197,plain,(
% 0.21/0.44    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | (~spl2_13 | ~spl2_24)),
% 0.21/0.44    inference(superposition,[],[f195,f141])).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) ) | ~spl2_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f140])).
% 0.21/0.44  fof(f195,plain,(
% 0.21/0.44    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) ) | ~spl2_24),
% 0.21/0.44    inference(avatar_component_clause,[],[f194])).
% 0.21/0.44  fof(f196,plain,(
% 0.21/0.44    spl2_24 | ~spl2_1 | ~spl2_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f191,f188,f79,f194])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    spl2_1 <=> l1_orders_2(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f188,plain,(
% 0.21/0.44    spl2_23 <=> ! [X1,X0] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.44  fof(f191,plain,(
% 0.21/0.44    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) ) | (~spl2_1 | ~spl2_23)),
% 0.21/0.44    inference(resolution,[],[f189,f81])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    l1_orders_2(sK0) | ~spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f79])).
% 0.21/0.44  fof(f189,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))) ) | ~spl2_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f188])).
% 0.21/0.44  fof(f190,plain,(
% 0.21/0.44    spl2_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f75,f188])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f55,f52])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,axiom,(
% 0.21/0.44    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,axiom,(
% 0.21/0.44    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.21/0.44  fof(f181,plain,(
% 0.21/0.44    spl2_21 | ~spl2_18 | ~spl2_20),
% 0.21/0.44    inference(avatar_split_clause,[],[f176,f172,f162,f178])).
% 0.21/0.44  fof(f162,plain,(
% 0.21/0.44    spl2_18 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.44  fof(f172,plain,(
% 0.21/0.44    spl2_20 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.44  fof(f176,plain,(
% 0.21/0.44    v4_relat_1(k1_xboole_0,k1_xboole_0) | (~spl2_18 | ~spl2_20)),
% 0.21/0.44    inference(resolution,[],[f173,f164])).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl2_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f162])).
% 0.21/0.44  fof(f173,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl2_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f172])).
% 0.21/0.44  fof(f174,plain,(
% 0.21/0.44    spl2_20),
% 0.21/0.44    inference(avatar_split_clause,[],[f57,f172])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.44    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.44  fof(f170,plain,(
% 0.21/0.44    ~spl2_19),
% 0.21/0.44    inference(avatar_split_clause,[],[f76,f167])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_zfmisc_1(k1_xboole_0),k6_partfun1(k1_zfmisc_1(k1_xboole_0)))),
% 0.21/0.44    inference(backward_demodulation,[],[f69,f71])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.21/0.44    inference(definition_unfolding,[],[f40,f68,f68])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.21/0.44    inference(negated_conjecture,[],[f21])).
% 0.21/0.44  fof(f21,conjecture,(
% 0.21/0.44    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.21/0.44  fof(f165,plain,(
% 0.21/0.44    spl2_18 | ~spl2_7 | ~spl2_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f160,f157,f105,f162])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    spl2_7 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.44  fof(f157,plain,(
% 0.21/0.44    spl2_17 <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.44  fof(f160,plain,(
% 0.21/0.44    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl2_7 | ~spl2_17)),
% 0.21/0.44    inference(superposition,[],[f158,f107])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl2_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f105])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl2_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f157])).
% 0.21/0.44  fof(f159,plain,(
% 0.21/0.44    spl2_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f49,f157])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,axiom,(
% 0.21/0.44    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.44  fof(f155,plain,(
% 0.21/0.44    spl2_15 | spl2_16 | ~spl2_13 | ~spl2_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f147,f144,f140,f152,f149])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    spl2_14 <=> ! [X1,X0] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    ( ! [X0] : (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(X0)) ) | (~spl2_13 | ~spl2_14)),
% 0.21/0.44    inference(superposition,[],[f145,f141])).
% 0.21/0.44  fof(f145,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) ) | ~spl2_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f144])).
% 0.21/0.44  fof(f146,plain,(
% 0.21/0.44    spl2_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f54,f144])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,axiom,(
% 0.21/0.44    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).
% 0.21/0.44  fof(f142,plain,(
% 0.21/0.44    spl2_13 | ~spl2_5 | ~spl2_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f131,f128,f97,f140])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    spl2_5 <=> ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f128,plain,(
% 0.21/0.44    spl2_11 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) ) | (~spl2_5 | ~spl2_11)),
% 0.21/0.44    inference(resolution,[],[f129,f98])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) ) | ~spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f97])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl2_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f128])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    spl2_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f50,f128])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.44  fof(f126,plain,(
% 0.21/0.44    spl2_10 | ~spl2_6 | ~spl2_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f109,f105,f101,f123])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    spl2_6 <=> ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl2_6 | ~spl2_7)),
% 0.21/0.44    inference(superposition,[],[f102,f107])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) ) | ~spl2_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f101])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    spl2_9 | ~spl2_3 | ~spl2_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f111,f105,f89,f118])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    spl2_3 <=> ! [X0] : v1_funct_1(k6_partfun1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    v1_funct_1(k1_xboole_0) | (~spl2_3 | ~spl2_7)),
% 0.21/0.44    inference(superposition,[],[f90,f107])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) ) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f89])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    spl2_8 | ~spl2_4 | ~spl2_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f110,f105,f93,f113])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    spl2_4 <=> ! [X0] : v1_relat_1(k6_partfun1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    v1_relat_1(k1_xboole_0) | (~spl2_4 | ~spl2_7)),
% 0.21/0.44    inference(superposition,[],[f94,f107])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) ) | ~spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f93])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    spl2_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f70,f105])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.44    inference(definition_unfolding,[],[f41,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,axiom,(
% 0.21/0.44    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    spl2_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f48,f101])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f99,plain,(
% 0.21/0.44    spl2_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f43,f97])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,axiom,(
% 0.21/0.44    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f73,f93])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f46,f44])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    spl2_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f72,f89])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f47,f44])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f62,f84])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    l1_orders_2(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    l1_orders_2(sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ? [X0] : l1_orders_2(X0) => l1_orders_2(sK1)),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ? [X0] : l1_orders_2(X0)),
% 0.21/0.44    inference(pure_predicate_removal,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ? [X0] : (~v2_struct_0(X0) & l1_orders_2(X0))),
% 0.21/0.44    inference(pure_predicate_removal,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ? [X0] : (v7_struct_0(X0) & ~v2_struct_0(X0) & l1_orders_2(X0))),
% 0.21/0.44    inference(pure_predicate_removal,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ? [X0] : (v1_orders_2(X0) & v7_struct_0(X0) & ~v2_struct_0(X0) & l1_orders_2(X0))),
% 0.21/0.44    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.44  fof(f15,axiom,(
% 0.21/0.44    ? [X0] : (v3_orders_2(X0) & v1_orders_2(X0) & v7_struct_0(X0) & ~v2_struct_0(X0) & l1_orders_2(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_0)).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f39,f79])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    l1_orders_2(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f36])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (17006)------------------------------
% 0.21/0.44  % (17006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (17006)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (17006)Memory used [KB]: 6140
% 0.21/0.44  % (17006)Time elapsed: 0.034 s
% 0.21/0.44  % (17006)------------------------------
% 0.21/0.44  % (17006)------------------------------
% 0.21/0.45  % (16998)Success in time 0.086 s
%------------------------------------------------------------------------------

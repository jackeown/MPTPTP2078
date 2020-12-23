%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t68_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:26 EDT 2019

% Result     : Theorem 12.62s
% Output     : Refutation 12.62s
% Verified   : 
% Statistics : Number of formulae       : 1113 (6462 expanded)
%              Number of leaves         :  240 (2391 expanded)
%              Depth                    :   16
%              Number of atoms          : 3370 (30447 expanded)
%              Number of equality atoms :  242 (4282 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45063,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f124,f131,f138,f145,f152,f162,f171,f185,f206,f318,f417,f512,f519,f583,f586,f589,f597,f678,f774,f1597,f1612,f1771,f1799,f1810,f2042,f2068,f2109,f2113,f2148,f2162,f2187,f2194,f2399,f2534,f3262,f4304,f4355,f4371,f4397,f4488,f4519,f4523,f4541,f4543,f4562,f4684,f4756,f4961,f5002,f5035,f5135,f5220,f5227,f5272,f5281,f5288,f5295,f5444,f5493,f5517,f5524,f5753,f5760,f5767,f5774,f5803,f5810,f6084,f6091,f6207,f6214,f6221,f6228,f6465,f6579,f6631,f6632,f6633,f6635,f6637,f6639,f6641,f6643,f6645,f6647,f6649,f6651,f6653,f6655,f6657,f6744,f6793,f6830,f6902,f6928,f7087,f7163,f7237,f7344,f7351,f7600,f7737,f7997,f8048,f8090,f8097,f8270,f8347,f8420,f8444,f8446,f8448,f8452,f8457,f8459,f8461,f8463,f8465,f8467,f8469,f8474,f8476,f8534,f8538,f8544,f8551,f8558,f8683,f8691,f8897,f8904,f8973,f9079,f9086,f9093,f9273,f9311,f9419,f9502,f9549,f9556,f9558,f9595,f9870,f9872,f9874,f9875,f9993,f9998,f10452,f10459,f10466,f10566,f10951,f11027,f11073,f11080,f11246,f11419,f11505,f11597,f11683,f12178,f12185,f12192,f12199,f12206,f12222,f12229,f12316,f12541,f12548,f14471,f14652,f14751,f15269,f15418,f15526,f15915,f16023,f16324,f16452,f16459,f16466,f16494,f16501,f20586,f20673,f20821,f20977,f21125,f21281,f21437,f22518,f22525,f24713,f24720,f25267,f25274,f25281,f25471,f25478,f25593,f25615,f25653,f25660,f25910,f25917,f25924,f27017,f27221,f28374,f31973,f32226,f32489,f32514,f32521,f32554,f32855,f32941,f32950,f33122,f33142,f33917,f35758,f36118,f36324,f42251,f42308,f43116,f43123,f43130,f43213,f43456,f43623,f43630,f43637,f43644,f44249,f44326,f44333,f44360,f44367,f44910,f44974,f45055,f45060,f45062])).

fof(f45062,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | ~ spl10_62
    | ~ spl10_228
    | ~ spl10_378 ),
    inference(avatar_contradiction_clause,[],[f45061])).

fof(f45061,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_62
    | ~ spl10_228
    | ~ spl10_378 ),
    inference(subsumption_resolution,[],[f44248,f45003])).

fof(f45003,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_62
    | ~ spl10_228 ),
    inference(unit_resulting_resolution,[],[f116,f130,f151,f12177,f4303,f1681])).

fof(f1681,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3(X0,X1,X2),k3_xboole_0(X1,X3)) ) ),
    inference(resolution,[],[f76,f110])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
            | ~ r2_hidden(sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK9(X0,X1,X2),X0) )
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f58,f59])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
          | ~ r2_hidden(sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(sK9(X0,X1,X2),X0) )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',d4_xboole_0)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK3(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                    & r2_hidden(sK3(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',d11_relat_1)).

fof(f4303,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f4302])).

fof(f4302,plain,
    ( spl10_62
  <=> r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f12177,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_228 ),
    inference(avatar_component_clause,[],[f12176])).

fof(f12176,plain,
    ( spl10_228
  <=> r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_228])])).

fof(f151,plain,
    ( k7_relat_1(sK2,sK0) != sK1
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl10_11
  <=> k7_relat_1(sK2,sK0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f130,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl10_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f116,plain,
    ( v1_relat_1(sK1)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl10_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f44248,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1)
    | ~ spl10_378 ),
    inference(avatar_component_clause,[],[f44247])).

fof(f44247,plain,
    ( spl10_378
  <=> r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_378])])).

fof(f45060,plain,
    ( ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | spl10_11
    | ~ spl10_62
    | ~ spl10_70
    | ~ spl10_116
    | ~ spl10_228 ),
    inference(avatar_contradiction_clause,[],[f45059])).

fof(f45059,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_11
    | ~ spl10_62
    | ~ spl10_70
    | ~ spl10_116
    | ~ spl10_228 ),
    inference(subsumption_resolution,[],[f45044,f45003])).

fof(f45044,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_62
    | ~ spl10_70
    | ~ spl10_116 ),
    inference(backward_demodulation,[],[f45043,f8712])).

fof(f8712,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_funct_1(sK1,sK3(sK2,sK0,sK1))),sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_116 ),
    inference(resolution,[],[f6080,f367])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) )
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f365,f116])).

fof(f365,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl10_2 ),
    inference(resolution,[],[f105,f123])).

fof(f123,plain,
    ( v1_funct_1(sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl10_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',d4_funct_1)).

fof(f6080,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_116 ),
    inference(avatar_component_clause,[],[f6079])).

fof(f6079,plain,
    ( spl10_116
  <=> r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_116])])).

fof(f45043,plain,
    ( k1_funct_1(sK1,sK3(sK2,sK0,sK1)) = sK4(sK2,sK0,sK1)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_62
    | ~ spl10_70
    | ~ spl10_116 ),
    inference(backward_demodulation,[],[f45011,f8695])).

fof(f8695,plain,
    ( k1_funct_1(sK1,sK3(sK2,sK0,sK1)) = k1_funct_1(sK2,sK3(sK2,sK0,sK1))
    | ~ spl10_116 ),
    inference(unit_resulting_resolution,[],[f6080,f66])).

fof(f66,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
      | ~ r2_hidden(X3,k1_relat_1(sK1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k7_relat_1(sK2,sK0) != sK1
    & ! [X3] :
        ( k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
        | ~ r2_hidden(X3,k1_relat_1(sK1)) )
    & k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK2),sK0)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f40,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_relat_1(X2,X0) != X1
            & ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relat_1(X1)) )
            & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(X2,sK0) != sK1
          & ! [X3] :
              ( k1_funct_1(sK1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(sK1)) )
          & k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(X2),sK0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X2,X0) != X1
          & ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k7_relat_1(sK2,X0) != X1
        & ! [X3] :
            ( k1_funct_1(sK2,X3) = k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(sK2),X0)
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X2,X0) != X1
          & ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X2,X0) != X1
          & ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
                & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0) )
             => k7_relat_1(X2,X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0) )
           => k7_relat_1(X2,X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',t68_funct_1)).

fof(f45011,plain,
    ( k1_funct_1(sK2,sK3(sK2,sK0,sK1)) = sK4(sK2,sK0,sK1)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_62
    | ~ spl10_70 ),
    inference(unit_resulting_resolution,[],[f130,f137,f4487,f4303,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4487,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK2))
    | ~ spl10_70 ),
    inference(avatar_component_clause,[],[f4486])).

fof(f4486,plain,
    ( spl10_70
  <=> r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f137,plain,
    ( v1_funct_1(sK2)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl10_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f45055,plain,
    ( ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_62
    | ~ spl10_70
    | ~ spl10_116
    | spl10_379 ),
    inference(avatar_contradiction_clause,[],[f45054])).

fof(f45054,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_62
    | ~ spl10_70
    | ~ spl10_116
    | ~ spl10_379 ),
    inference(subsumption_resolution,[],[f45044,f44245])).

fof(f44245,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1)
    | ~ spl10_379 ),
    inference(avatar_component_clause,[],[f44244])).

fof(f44244,plain,
    ( spl10_379
  <=> ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_379])])).

fof(f44974,plain,
    ( ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | spl10_63
    | ~ spl10_70
    | ~ spl10_116
    | ~ spl10_378 ),
    inference(avatar_contradiction_clause,[],[f44973])).

fof(f44973,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_63
    | ~ spl10_70
    | ~ spl10_116
    | ~ spl10_378 ),
    inference(subsumption_resolution,[],[f44964,f4300])).

fof(f4300,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | ~ spl10_63 ),
    inference(avatar_component_clause,[],[f4299])).

fof(f4299,plain,
    ( spl10_63
  <=> ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).

fof(f44964,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_70
    | ~ spl10_116
    | ~ spl10_378 ),
    inference(backward_demodulation,[],[f44928,f9559])).

fof(f9559,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_funct_1(sK1,sK3(sK2,sK0,sK1))),sK2)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_70
    | ~ spl10_116 ),
    inference(backward_demodulation,[],[f8695,f8507])).

fof(f8507,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_funct_1(sK2,sK3(sK2,sK0,sK1))),sK2)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_70 ),
    inference(unit_resulting_resolution,[],[f130,f137,f4487,f105])).

fof(f44928,plain,
    ( k1_funct_1(sK1,sK3(sK2,sK0,sK1)) = sK4(sK2,sK0,sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_116
    | ~ spl10_378 ),
    inference(unit_resulting_resolution,[],[f116,f123,f6080,f44248,f78])).

fof(f44910,plain,
    ( spl10_388
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_158
    | ~ spl10_202
    | ~ spl10_374 ),
    inference(avatar_split_clause,[],[f44875,f43635,f10450,f8046,f122,f115,f44908])).

fof(f44908,plain,
    ( spl10_388
  <=> sK7(sK1,k1_xboole_0) = sK8(sK1,sK6(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_388])])).

fof(f8046,plain,
    ( spl10_158
  <=> r2_hidden(sK6(sK1,k1_xboole_0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_158])])).

fof(f10450,plain,
    ( spl10_202
  <=> k1_funct_1(sK1,sK6(sK1,k1_xboole_0)) = sK7(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_202])])).

fof(f43635,plain,
    ( spl10_374
  <=> r2_hidden(k4_tarski(sK6(sK1,k1_xboole_0),sK8(sK1,sK6(sK1,k1_xboole_0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_374])])).

fof(f44875,plain,
    ( sK7(sK1,k1_xboole_0) = sK8(sK1,sK6(sK1,k1_xboole_0))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_158
    | ~ spl10_202
    | ~ spl10_374 ),
    inference(forward_demodulation,[],[f44840,f10451])).

fof(f10451,plain,
    ( k1_funct_1(sK1,sK6(sK1,k1_xboole_0)) = sK7(sK1,k1_xboole_0)
    | ~ spl10_202 ),
    inference(avatar_component_clause,[],[f10450])).

fof(f44840,plain,
    ( k1_funct_1(sK1,sK6(sK1,k1_xboole_0)) = sK8(sK1,sK6(sK1,k1_xboole_0))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_158
    | ~ spl10_374 ),
    inference(unit_resulting_resolution,[],[f116,f123,f8047,f43636,f78])).

fof(f43636,plain,
    ( r2_hidden(k4_tarski(sK6(sK1,k1_xboole_0),sK8(sK1,sK6(sK1,k1_xboole_0))),sK1)
    | ~ spl10_374 ),
    inference(avatar_component_clause,[],[f43635])).

fof(f8047,plain,
    ( r2_hidden(sK6(sK1,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl10_158 ),
    inference(avatar_component_clause,[],[f8046])).

fof(f44367,plain,
    ( ~ spl10_387
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_40
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f32592,f8345,f1769,f183,f136,f129,f122,f115,f44365])).

fof(f44365,plain,
    ( spl10_387
  <=> ~ r2_hidden(sK2,k4_tarski(sK3(sK2,k1_xboole_0,sK1),sK4(sK2,k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_387])])).

fof(f183,plain,
    ( spl10_16
  <=> k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f1769,plain,
    ( spl10_40
  <=> r2_hidden(k4_tarski(sK3(sK2,k1_xboole_0,sK1),sK4(sK2,k1_xboole_0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f8345,plain,
    ( spl10_166
  <=> r2_hidden(sK3(sK2,k1_xboole_0,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_166])])).

fof(f32592,plain,
    ( ~ r2_hidden(sK2,k4_tarski(sK3(sK2,k1_xboole_0,sK1),sK4(sK2,k1_xboole_0,sK1)))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_40
    | ~ spl10_166 ),
    inference(forward_demodulation,[],[f32576,f32544])).

fof(f32544,plain,
    ( sK4(sK2,k1_xboole_0,sK1) = sK8(sK2,sK3(sK2,k1_xboole_0,sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_40
    | ~ spl10_166 ),
    inference(forward_demodulation,[],[f32523,f8378])).

fof(f8378,plain,
    ( k1_funct_1(sK2,sK3(sK2,k1_xboole_0,sK1)) = sK4(sK2,k1_xboole_0,sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_40
    | ~ spl10_166 ),
    inference(forward_demodulation,[],[f8350,f8271])).

fof(f8271,plain,
    ( k1_funct_1(sK1,sK3(sK2,k1_xboole_0,sK1)) = sK4(sK2,k1_xboole_0,sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f1770,f970])).

fof(f970,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f969,f106])).

fof(f106,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f51,f54,f53,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',d4_relat_1)).

fof(f969,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f967,f116])).

fof(f967,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = X1
        | ~ v1_relat_1(sK1) )
    | ~ spl10_2 ),
    inference(resolution,[],[f78,f123])).

fof(f1770,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k1_xboole_0,sK1),sK4(sK2,k1_xboole_0,sK1)),sK1)
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f1769])).

fof(f8350,plain,
    ( k1_funct_1(sK1,sK3(sK2,k1_xboole_0,sK1)) = k1_funct_1(sK2,sK3(sK2,k1_xboole_0,sK1))
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f8346,f66])).

fof(f8346,plain,
    ( r2_hidden(sK3(sK2,k1_xboole_0,sK1),k1_relat_1(sK1))
    | ~ spl10_166 ),
    inference(avatar_component_clause,[],[f8345])).

fof(f32523,plain,
    ( k1_funct_1(sK2,sK3(sK2,k1_xboole_0,sK1)) = sK8(sK2,sK3(sK2,k1_xboole_0,sK1))
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f8346,f8429])).

fof(f8429,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) = sK8(sK2,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16 ),
    inference(resolution,[],[f4794,f973])).

fof(f973,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | k1_funct_1(sK2,X2) = X3 )
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f972,f106])).

fof(f972,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | ~ r2_hidden(X2,k1_relat_1(sK2))
        | k1_funct_1(sK2,X2) = X3 )
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f968,f130])).

fof(f968,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | ~ r2_hidden(X2,k1_relat_1(sK2))
        | k1_funct_1(sK2,X2) = X3
        | ~ v1_relat_1(sK2) )
    | ~ spl10_6 ),
    inference(resolution,[],[f78,f137])).

fof(f4794,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK8(sK2,X0)),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl10_16 ),
    inference(superposition,[],[f287,f184])).

fof(f184,plain,
    ( k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK2),sK0)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f183])).

fof(f287,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X1),X2))
      | r2_hidden(k4_tarski(X0,sK8(X1,X0)),X1) ) ),
    inference(resolution,[],[f107,f110])).

fof(f107,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f32576,plain,
    ( ~ r2_hidden(sK2,k4_tarski(sK3(sK2,k1_xboole_0,sK1),sK8(sK2,sK3(sK2,k1_xboole_0,sK1))))
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f8346,f8436])).

fof(f8436,plain,
    ( ! [X9] :
        ( ~ r2_hidden(sK2,k4_tarski(X9,sK8(sK2,X9)))
        | ~ r2_hidden(X9,k1_relat_1(sK1)) )
    | ~ spl10_16 ),
    inference(resolution,[],[f4794,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',antisymmetry_r2_hidden)).

fof(f44360,plain,
    ( ~ spl10_385
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(avatar_split_clause,[],[f32591,f4959,f183,f136,f129,f44358])).

fof(f44358,plain,
    ( spl10_385
  <=> ~ r2_hidden(sK2,k4_tarski(sK5(k1_relat_1(sK1)),k1_funct_1(sK1,sK5(k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_385])])).

fof(f4959,plain,
    ( spl10_76
  <=> r2_hidden(sK5(k1_relat_1(sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f32591,plain,
    ( ~ r2_hidden(sK2,k4_tarski(sK5(k1_relat_1(sK1)),k1_funct_1(sK1,sK5(k1_relat_1(sK1)))))
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(forward_demodulation,[],[f32577,f32542])).

fof(f32542,plain,
    ( k1_funct_1(sK1,sK5(k1_relat_1(sK1))) = sK8(sK2,sK5(k1_relat_1(sK1)))
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(forward_demodulation,[],[f32524,f4991])).

fof(f4991,plain,
    ( k1_funct_1(sK1,sK5(k1_relat_1(sK1))) = k1_funct_1(sK2,sK5(k1_relat_1(sK1)))
    | ~ spl10_76 ),
    inference(unit_resulting_resolution,[],[f4960,f66])).

fof(f4960,plain,
    ( r2_hidden(sK5(k1_relat_1(sK1)),k1_relat_1(sK1))
    | ~ spl10_76 ),
    inference(avatar_component_clause,[],[f4959])).

fof(f32524,plain,
    ( k1_funct_1(sK2,sK5(k1_relat_1(sK1))) = sK8(sK2,sK5(k1_relat_1(sK1)))
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(unit_resulting_resolution,[],[f4960,f8429])).

fof(f32577,plain,
    ( ~ r2_hidden(sK2,k4_tarski(sK5(k1_relat_1(sK1)),sK8(sK2,sK5(k1_relat_1(sK1)))))
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(unit_resulting_resolution,[],[f4960,f8436])).

fof(f44333,plain,
    ( spl10_382
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_40
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f32544,f8345,f1769,f183,f136,f129,f122,f115,f44331])).

fof(f44331,plain,
    ( spl10_382
  <=> sK4(sK2,k1_xboole_0,sK1) = sK8(sK2,sK3(sK2,k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_382])])).

fof(f44326,plain,
    ( spl10_380
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(avatar_split_clause,[],[f32542,f4959,f183,f136,f129,f44324])).

fof(f44324,plain,
    ( spl10_380
  <=> k1_funct_1(sK1,sK5(k1_relat_1(sK1))) = sK8(sK2,sK5(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_380])])).

fof(f44249,plain,
    ( spl10_378
    | ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_63 ),
    inference(avatar_split_clause,[],[f32281,f4299,f150,f129,f115,f44247])).

fof(f32281,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK1)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_63 ),
    inference(unit_resulting_resolution,[],[f130,f116,f151,f4300,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f43644,plain,
    ( spl10_376
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_40
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f8378,f8345,f1769,f122,f115,f43642])).

fof(f43642,plain,
    ( spl10_376
  <=> k1_funct_1(sK2,sK3(sK2,k1_xboole_0,sK1)) = sK4(sK2,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_376])])).

fof(f43637,plain,
    ( spl10_374
    | ~ spl10_158 ),
    inference(avatar_split_clause,[],[f8056,f8046,f43635])).

fof(f8056,plain,
    ( r2_hidden(k4_tarski(sK6(sK1,k1_xboole_0),sK8(sK1,sK6(sK1,k1_xboole_0))),sK1)
    | ~ spl10_158 ),
    inference(unit_resulting_resolution,[],[f8047,f107])).

fof(f43630,plain,
    ( spl10_372
    | ~ spl10_102
    | ~ spl10_114 ),
    inference(avatar_split_clause,[],[f5945,f5808,f5522,f43628])).

fof(f43628,plain,
    ( spl10_372
  <=> r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_372])])).

fof(f5522,plain,
    ( spl10_102
  <=> r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f5808,plain,
    ( spl10_114
  <=> r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_114])])).

fof(f5945,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_102
    | ~ spl10_114 ),
    inference(unit_resulting_resolution,[],[f5523,f5809,f108])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f5809,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k1_relat_1(sK1))
    | ~ spl10_114 ),
    inference(avatar_component_clause,[],[f5808])).

fof(f5523,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k1_relat_1(sK2))
    | ~ spl10_102 ),
    inference(avatar_component_clause,[],[f5522])).

fof(f43623,plain,
    ( spl10_370
    | ~ spl10_100
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f5856,f5765,f5515,f43621])).

fof(f43621,plain,
    ( spl10_370
  <=> r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_370])])).

fof(f5515,plain,
    ( spl10_100
  <=> r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_100])])).

fof(f5765,plain,
    ( spl10_108
  <=> r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_108])])).

fof(f5856,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_100
    | ~ spl10_108 ),
    inference(unit_resulting_resolution,[],[f5516,f5766,f108])).

fof(f5766,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl10_108 ),
    inference(avatar_component_clause,[],[f5765])).

fof(f5516,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k1_relat_1(sK2))
    | ~ spl10_100 ),
    inference(avatar_component_clause,[],[f5515])).

fof(f43456,plain,
    ( ~ spl10_369
    | ~ spl10_4
    | spl10_93 ),
    inference(avatar_split_clause,[],[f43378,f5286,f129,f43454])).

fof(f43454,plain,
    ( spl10_369
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK9(sK0,k1_relat_1(sK2),k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_369])])).

fof(f5286,plain,
    ( spl10_93
  <=> ~ r2_hidden(sK0,sK9(sK0,k1_relat_1(sK2),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f43378,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK9(sK0,k1_relat_1(sK2),k1_xboole_0))))
    | ~ spl10_4
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f5346,f107])).

fof(f5346,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK2,sK9(sK0,k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl10_4
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f130,f174,f5287,f102])).

fof(f102,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5287,plain,
    ( ~ r2_hidden(sK0,sK9(sK0,k1_relat_1(sK2),k1_xboole_0))
    | ~ spl10_93 ),
    inference(avatar_component_clause,[],[f5286])).

fof(f174,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f130,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',dt_k7_relat_1)).

fof(f43213,plain,
    ( ~ spl10_367
    | ~ spl10_4
    | spl10_89 ),
    inference(avatar_split_clause,[],[f43135,f5270,f129,f43211])).

fof(f43211,plain,
    ( spl10_367
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK9(k1_relat_1(sK2),sK0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_367])])).

fof(f5270,plain,
    ( spl10_89
  <=> ~ r2_hidden(sK0,sK9(k1_relat_1(sK2),sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).

fof(f43135,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK9(k1_relat_1(sK2),sK0,k1_xboole_0))))
    | ~ spl10_4
    | ~ spl10_89 ),
    inference(unit_resulting_resolution,[],[f5296,f107])).

fof(f5296,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK2,sK9(k1_relat_1(sK2),sK0,k1_xboole_0)))
    | ~ spl10_4
    | ~ spl10_89 ),
    inference(unit_resulting_resolution,[],[f130,f174,f5271,f102])).

fof(f5271,plain,
    ( ~ r2_hidden(sK0,sK9(k1_relat_1(sK2),sK0,k1_xboole_0))
    | ~ spl10_89 ),
    inference(avatar_component_clause,[],[f5270])).

fof(f43130,plain,
    ( spl10_364
    | ~ spl10_76 ),
    inference(avatar_split_clause,[],[f4991,f4959,f43128])).

fof(f43128,plain,
    ( spl10_364
  <=> k1_funct_1(sK1,sK5(k1_relat_1(sK1))) = k1_funct_1(sK2,sK5(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_364])])).

fof(f43123,plain,
    ( spl10_362
    | ~ spl10_76 ),
    inference(avatar_split_clause,[],[f4963,f4959,f43121])).

fof(f43121,plain,
    ( spl10_362
  <=> r2_hidden(k4_tarski(sK5(k1_relat_1(sK1)),sK8(sK1,sK5(k1_relat_1(sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_362])])).

fof(f4963,plain,
    ( r2_hidden(k4_tarski(sK5(k1_relat_1(sK1)),sK8(sK1,sK5(k1_relat_1(sK1)))),sK1)
    | ~ spl10_76 ),
    inference(unit_resulting_resolution,[],[f4960,f107])).

fof(f43116,plain,
    ( spl10_360
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_76 ),
    inference(avatar_split_clause,[],[f4962,f4959,f122,f115,f43114])).

fof(f43114,plain,
    ( spl10_360
  <=> r2_hidden(k4_tarski(sK5(k1_relat_1(sK1)),k1_funct_1(sK1,sK5(k1_relat_1(sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_360])])).

fof(f4962,plain,
    ( r2_hidden(k4_tarski(sK5(k1_relat_1(sK1)),k1_funct_1(sK1,sK5(k1_relat_1(sK1)))),sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_76 ),
    inference(unit_resulting_resolution,[],[f116,f123,f4960,f105])).

fof(f42308,plain,
    ( spl10_28
    | spl10_358
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f322,f183,f42306,f517])).

fof(f517,plain,
    ( spl10_28
  <=> k1_relat_1(sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f42306,plain,
    ( spl10_358
  <=> ! [X6] : ~ r2_hidden(sK0,k3_xboole_0(X6,sK5(k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_358])])).

fof(f322,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK0,k3_xboole_0(X6,sK5(k1_relat_1(sK1))))
        | k1_relat_1(sK1) = k1_xboole_0 )
    | ~ spl10_16 ),
    inference(resolution,[],[f283,f241])).

fof(f241,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f209,f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',existence_m1_subset_1)).

fof(f209,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,X4)
      | r2_hidden(X3,X4)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f85,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',t6_boole)).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',t2_subset)).

fof(f283,plain,
    ( ! [X14,X15] :
        ( ~ r2_hidden(X14,k1_relat_1(sK1))
        | ~ r2_hidden(sK0,k3_xboole_0(X15,X14)) )
    | ~ spl10_16 ),
    inference(superposition,[],[f233,f184])).

fof(f233,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,k3_xboole_0(X5,X6))
      | ~ r2_hidden(X6,k3_xboole_0(X7,X4)) ) ),
    inference(resolution,[],[f211,f109])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f109,f86])).

fof(f42251,plain,
    ( spl10_28
    | spl10_356
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f275,f183,f42249,f517])).

fof(f42249,plain,
    ( spl10_356
  <=> ! [X6] : ~ r2_hidden(sK0,k3_xboole_0(sK5(k1_relat_1(sK1)),X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_356])])).

fof(f275,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK0,k3_xboole_0(sK5(k1_relat_1(sK1)),X6))
        | k1_relat_1(sK1) = k1_xboole_0 )
    | ~ spl10_16 ),
    inference(resolution,[],[f270,f241])).

fof(f270,plain,
    ( ! [X14,X15] :
        ( ~ r2_hidden(X14,k1_relat_1(sK1))
        | ~ r2_hidden(sK0,k3_xboole_0(X14,X15)) )
    | ~ spl10_16 ),
    inference(superposition,[],[f232,f184])).

fof(f232,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | ~ r2_hidden(X2,k3_xboole_0(X0,X3)) ) ),
    inference(resolution,[],[f211,f110])).

fof(f36324,plain,
    ( ~ spl10_355
    | ~ spl10_12
    | spl10_59
    | spl10_353 ),
    inference(avatar_split_clause,[],[f36140,f36116,f2529,f160,f36322])).

fof(f36322,plain,
    ( spl10_355
  <=> ~ m1_subset_1(sK0,k1_relat_1(k1_relat_1(k7_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_355])])).

fof(f160,plain,
    ( spl10_12
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f2529,plain,
    ( spl10_59
  <=> k1_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f36116,plain,
    ( spl10_353
  <=> ~ r2_hidden(sK0,k1_relat_1(k1_relat_1(k7_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_353])])).

fof(f36140,plain,
    ( ~ m1_subset_1(sK0,k1_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))))
    | ~ spl10_12
    | ~ spl10_59
    | ~ spl10_353 ),
    inference(unit_resulting_resolution,[],[f81,f172,f2530,f36117,f346])).

fof(f346,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X2,X3)
      | X3 = X4
      | r2_hidden(X2,X3)
      | r2_hidden(X5,X4)
      | ~ m1_subset_1(X5,X4) ) ),
    inference(resolution,[],[f208,f85])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X1)
      | X1 = X2
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f85,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',t8_boole)).

fof(f36117,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))))
    | ~ spl10_353 ),
    inference(avatar_component_clause,[],[f36116])).

fof(f2530,plain,
    ( k1_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))) != k1_xboole_0
    | ~ spl10_59 ),
    inference(avatar_component_clause,[],[f2529])).

fof(f172,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f161,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',t7_boole)).

fof(f161,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f36118,plain,
    ( ~ spl10_353
    | ~ spl10_4
    | spl10_339 ),
    inference(avatar_split_clause,[],[f36034,f32853,f129,f36116])).

fof(f32853,plain,
    ( spl10_339
  <=> ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_339])])).

fof(f36034,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))))
    | ~ spl10_4
    | ~ spl10_339 ),
    inference(unit_resulting_resolution,[],[f35962,f107])).

fof(f35962,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl10_4
    | ~ spl10_339 ),
    inference(unit_resulting_resolution,[],[f33039,f107])).

fof(f33039,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(k4_tarski(sK0,X0),X1),k7_relat_1(sK2,sK1))
    | ~ spl10_4
    | ~ spl10_339 ),
    inference(unit_resulting_resolution,[],[f32859,f9069])).

fof(f9069,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(k4_tarski(X4,X5),k7_relat_1(sK2,X3))
        | r2_hidden(X4,X3) )
    | ~ spl10_4 ),
    inference(superposition,[],[f2791,f82])).

fof(f82,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',idempotence_k3_xboole_0)).

fof(f2791,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r2_hidden(k4_tarski(X4,X6),k3_xboole_0(k7_relat_1(sK2,X5),X7))
        | r2_hidden(X4,X5) )
    | ~ spl10_4 ),
    inference(resolution,[],[f608,f130])).

fof(f608,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),k3_xboole_0(k7_relat_1(X2,X1),X4)) ) ),
    inference(subsumption_resolution,[],[f606,f84])).

fof(f606,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,X1)
      | ~ v1_relat_1(k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X3),k3_xboole_0(k7_relat_1(X2,X1),X4)) ) ),
    inference(resolution,[],[f102,f110])).

fof(f32859,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK1)
    | ~ spl10_339 ),
    inference(unit_resulting_resolution,[],[f32854,f106])).

fof(f32854,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl10_339 ),
    inference(avatar_component_clause,[],[f32853])).

fof(f35758,plain,
    ( ~ spl10_351
    | ~ spl10_0
    | spl10_339 ),
    inference(avatar_split_clause,[],[f35676,f32853,f115,f35756])).

fof(f35756,plain,
    ( spl10_351
  <=> ~ r2_hidden(sK0,k1_relat_1(k1_relat_1(k7_relat_1(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_351])])).

fof(f35676,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k1_relat_1(k7_relat_1(sK1,sK1))))
    | ~ spl10_0
    | ~ spl10_339 ),
    inference(unit_resulting_resolution,[],[f35604,f107])).

fof(f35604,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k1_relat_1(k7_relat_1(sK1,sK1)))
    | ~ spl10_0
    | ~ spl10_339 ),
    inference(unit_resulting_resolution,[],[f33038,f107])).

fof(f33038,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(k4_tarski(sK0,X0),X1),k7_relat_1(sK1,sK1))
    | ~ spl10_0
    | ~ spl10_339 ),
    inference(unit_resulting_resolution,[],[f32859,f8888])).

fof(f8888,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(k4_tarski(X4,X5),k7_relat_1(sK1,X3))
        | r2_hidden(X4,X3) )
    | ~ spl10_0 ),
    inference(superposition,[],[f2790,f82])).

fof(f2790,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X2),k3_xboole_0(k7_relat_1(sK1,X1),X3))
        | r2_hidden(X0,X1) )
    | ~ spl10_0 ),
    inference(resolution,[],[f608,f116])).

fof(f33917,plain,
    ( ~ spl10_349
    | ~ spl10_4
    | spl10_339 ),
    inference(avatar_split_clause,[],[f33839,f32853,f129,f33915])).

fof(f33915,plain,
    ( spl10_349
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_349])])).

fof(f33839,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,k1_relat_1(sK1))))
    | ~ spl10_4
    | ~ spl10_339 ),
    inference(unit_resulting_resolution,[],[f32932,f107])).

fof(f32932,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK2,k1_relat_1(sK1)))
    | ~ spl10_4
    | ~ spl10_339 ),
    inference(unit_resulting_resolution,[],[f32854,f9069])).

fof(f33142,plain,
    ( ~ spl10_347
    | ~ spl10_16
    | ~ spl10_18
    | spl10_219 ),
    inference(avatar_split_clause,[],[f32771,f11244,f204,f183,f33140])).

fof(f33140,plain,
    ( spl10_347
  <=> ~ m1_subset_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_347])])).

fof(f204,plain,
    ( spl10_18
  <=> k1_relat_1(sK1) = k3_xboole_0(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f11244,plain,
    ( spl10_219
  <=> ~ v1_xboole_0(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_219])])).

fof(f32771,plain,
    ( ~ m1_subset_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_219 ),
    inference(unit_resulting_resolution,[],[f11245,f32770,f85])).

fof(f32770,plain,
    ( ! [X13] : ~ r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK1),X13))
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f32769,f110])).

fof(f32769,plain,
    ( ! [X13] :
        ( ~ r2_hidden(sK0,k1_relat_1(sK1))
        | ~ r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK1),X13)) )
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(superposition,[],[f273,f205])).

fof(f205,plain,
    ( k1_relat_1(sK1) = k3_xboole_0(sK0,k1_relat_1(sK2))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f273,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK0,k3_xboole_0(X0,X1))
        | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(sK1),X2)) )
    | ~ spl10_16 ),
    inference(resolution,[],[f270,f110])).

fof(f11245,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_219 ),
    inference(avatar_component_clause,[],[f11244])).

fof(f33122,plain,
    ( ~ spl10_345
    | ~ spl10_16
    | ~ spl10_18
    | spl10_243 ),
    inference(avatar_split_clause,[],[f33049,f12314,f204,f183,f33120])).

fof(f33120,plain,
    ( spl10_345
  <=> ~ m1_subset_1(sK0,k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_345])])).

fof(f12314,plain,
    ( spl10_243
  <=> ~ v1_xboole_0(k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_243])])).

fof(f33049,plain,
    ( ~ m1_subset_1(sK0,k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_243 ),
    inference(unit_resulting_resolution,[],[f12315,f32836,f85])).

fof(f32836,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k3_xboole_0(X0,k1_relat_1(sK1)))
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(superposition,[],[f32770,f83])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',commutativity_k3_xboole_0)).

fof(f12315,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_243 ),
    inference(avatar_component_clause,[],[f12314])).

fof(f32950,plain,
    ( spl10_342
    | ~ spl10_0
    | ~ spl10_2
    | spl10_339 ),
    inference(avatar_split_clause,[],[f32858,f32853,f122,f115,f32948])).

fof(f32948,plain,
    ( spl10_342
  <=> k1_funct_1(sK1,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_342])])).

fof(f32858,plain,
    ( k1_funct_1(sK1,sK0) = k1_xboole_0
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_339 ),
    inference(unit_resulting_resolution,[],[f116,f123,f32854,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f32941,plain,
    ( ~ spl10_341
    | ~ spl10_12
    | spl10_29
    | spl10_339 ),
    inference(avatar_split_clause,[],[f32882,f32853,f514,f160,f32939])).

fof(f32939,plain,
    ( spl10_341
  <=> ~ m1_subset_1(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_341])])).

fof(f514,plain,
    ( spl10_29
  <=> k1_relat_1(sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f32882,plain,
    ( ~ m1_subset_1(sK0,k1_relat_1(sK1))
    | ~ spl10_12
    | ~ spl10_29
    | ~ spl10_339 ),
    inference(unit_resulting_resolution,[],[f81,f172,f515,f32854,f346])).

fof(f515,plain,
    ( k1_relat_1(sK1) != k1_xboole_0
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f514])).

fof(f32855,plain,
    ( ~ spl10_339
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f32835,f204,f183,f32853])).

fof(f32835,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(superposition,[],[f32770,f82])).

fof(f32554,plain,
    ( spl10_336
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_158
    | ~ spl10_208 ),
    inference(avatar_split_clause,[],[f32538,f10564,f8046,f183,f136,f129,f32552])).

fof(f32552,plain,
    ( spl10_336
  <=> sK7(sK1,k1_xboole_0) = sK8(sK2,sK6(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_336])])).

fof(f10564,plain,
    ( spl10_208
  <=> k1_funct_1(sK2,sK6(sK1,k1_xboole_0)) = sK7(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_208])])).

fof(f32538,plain,
    ( sK7(sK1,k1_xboole_0) = sK8(sK2,sK6(sK1,k1_xboole_0))
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_158
    | ~ spl10_208 ),
    inference(forward_demodulation,[],[f32526,f10565])).

fof(f10565,plain,
    ( k1_funct_1(sK2,sK6(sK1,k1_xboole_0)) = sK7(sK1,k1_xboole_0)
    | ~ spl10_208 ),
    inference(avatar_component_clause,[],[f10564])).

fof(f32526,plain,
    ( k1_funct_1(sK2,sK6(sK1,k1_xboole_0)) = sK8(sK2,sK6(sK1,k1_xboole_0))
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_158 ),
    inference(unit_resulting_resolution,[],[f8047,f8429])).

fof(f32521,plain,
    ( spl10_334
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f8276,f1769,f32519])).

fof(f32519,plain,
    ( spl10_334
  <=> m1_subset_1(k4_tarski(sK3(sK2,k1_xboole_0,sK1),sK4(sK2,k1_xboole_0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_334])])).

fof(f8276,plain,
    ( m1_subset_1(k4_tarski(sK3(sK2,k1_xboole_0,sK1),sK4(sK2,k1_xboole_0,sK1)),sK1)
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f1770,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',t1_subset)).

fof(f32514,plain,
    ( ~ spl10_333
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f8275,f1769,f32512])).

fof(f32512,plain,
    ( spl10_333
  <=> ~ r2_hidden(sK1,k4_tarski(sK3(sK2,k1_xboole_0,sK1),sK4(sK2,k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_333])])).

fof(f8275,plain,
    ( ~ r2_hidden(sK1,k4_tarski(sK3(sK2,k1_xboole_0,sK1),sK4(sK2,k1_xboole_0,sK1)))
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f1770,f86])).

fof(f32489,plain,
    ( spl10_330
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f8271,f1769,f122,f115,f32487])).

fof(f32487,plain,
    ( spl10_330
  <=> k1_funct_1(sK1,sK3(sK2,k1_xboole_0,sK1)) = sK4(sK2,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_330])])).

fof(f32226,plain,
    ( spl10_328
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f32114,f160,f129,f115,f32224])).

fof(f32224,plain,
    ( spl10_328
  <=> k1_relat_1(k1_relat_1(k7_relat_1(sK2,k7_relat_1(sK1,k1_xboole_0)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_328])])).

fof(f32114,plain,
    ( k1_relat_1(k1_relat_1(k7_relat_1(sK2,k7_relat_1(sK1,k1_xboole_0)))) = k1_xboole_0
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f32015,f6548])).

fof(f6548,plain,
    ( ! [X88,X89] :
        ( r2_hidden(k4_tarski(sK9(X89,k1_xboole_0,k1_relat_1(X88)),sK8(X88,sK9(X89,k1_xboole_0,k1_relat_1(X88)))),X88)
        | k1_relat_1(X88) = k1_xboole_0 )
    | ~ spl10_12 ),
    inference(forward_demodulation,[],[f6535,f69])).

fof(f69,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',t2_boole)).

fof(f6535,plain,
    ( ! [X88,X89] :
        ( k1_relat_1(X88) = k3_xboole_0(X89,k1_xboole_0)
        | r2_hidden(k4_tarski(sK9(X89,k1_xboole_0,k1_relat_1(X88)),sK8(X88,sK9(X89,k1_xboole_0,k1_relat_1(X88)))),X88) )
    | ~ spl10_12 ),
    inference(resolution,[],[f797,f172])).

fof(f797,plain,(
    ! [X24,X23,X25] :
      ( r2_hidden(sK9(X23,X24,k1_relat_1(X25)),X24)
      | k1_relat_1(X25) = k3_xboole_0(X23,X24)
      | r2_hidden(k4_tarski(sK9(X23,X24,k1_relat_1(X25)),sK8(X25,sK9(X23,X24,k1_relat_1(X25)))),X25) ) ),
    inference(resolution,[],[f98,f107])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X2)
      | r2_hidden(sK9(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f32015,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k1_relat_1(k7_relat_1(sK2,k7_relat_1(sK1,k1_xboole_0))))
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f612,f107])).

fof(f612,plain,
    ( ! [X2,X0,X1] : ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k7_relat_1(sK2,k7_relat_1(sK1,k1_xboole_0)))
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f130,f174,f598,f102])).

fof(f598,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(sK1,k1_xboole_0))
    | ~ spl10_0
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f172,f116,f173,f102])).

fof(f173,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl10_0 ),
    inference(unit_resulting_resolution,[],[f116,f84])).

fof(f31973,plain,
    ( spl10_326
    | ~ spl10_0
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f31839,f160,f115,f31971])).

fof(f31971,plain,
    ( spl10_326
  <=> k1_relat_1(k1_relat_1(k7_relat_1(sK1,k7_relat_1(sK1,k1_xboole_0)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_326])])).

fof(f31839,plain,
    ( k1_relat_1(k1_relat_1(k7_relat_1(sK1,k7_relat_1(sK1,k1_xboole_0)))) = k1_xboole_0
    | ~ spl10_0
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f31742,f6548])).

fof(f31742,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k1_relat_1(k7_relat_1(sK1,k7_relat_1(sK1,k1_xboole_0))))
    | ~ spl10_0
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f611,f107])).

fof(f611,plain,
    ( ! [X2,X0,X1] : ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k7_relat_1(sK1,k7_relat_1(sK1,k1_xboole_0)))
    | ~ spl10_0
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f116,f173,f598,f102])).

fof(f28374,plain,
    ( ~ spl10_325
    | ~ spl10_296 ),
    inference(avatar_split_clause,[],[f25424,f25265,f28372])).

fof(f28372,plain,
    ( spl10_325
  <=> ~ r2_hidden(k3_xboole_0(sK0,k1_relat_1(sK1)),sK5(k3_xboole_0(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_325])])).

fof(f25265,plain,
    ( spl10_296
  <=> r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_296])])).

fof(f25424,plain,
    ( ~ r2_hidden(k3_xboole_0(sK0,k1_relat_1(sK1)),sK5(k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ spl10_296 ),
    inference(unit_resulting_resolution,[],[f25266,f86])).

fof(f25266,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_296 ),
    inference(avatar_component_clause,[],[f25265])).

fof(f27221,plain,
    ( ~ spl10_323
    | ~ spl10_0
    | spl10_83 ),
    inference(avatar_split_clause,[],[f27143,f5133,f115,f27219])).

fof(f27219,plain,
    ( spl10_323
  <=> ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK1,sK5(k1_relat_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_323])])).

fof(f5133,plain,
    ( spl10_83
  <=> ~ r2_hidden(k1_relat_1(sK2),sK5(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).

fof(f27143,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK1,sK5(k1_relat_1(sK2)))))
    | ~ spl10_0
    | ~ spl10_83 ),
    inference(unit_resulting_resolution,[],[f5137,f107])).

fof(f5137,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_relat_1(sK2),X0),k7_relat_1(sK1,sK5(k1_relat_1(sK2))))
    | ~ spl10_0
    | ~ spl10_83 ),
    inference(unit_resulting_resolution,[],[f116,f173,f5134,f102])).

fof(f5134,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK5(k1_relat_1(sK2)))
    | ~ spl10_83 ),
    inference(avatar_component_clause,[],[f5133])).

fof(f27017,plain,
    ( ~ spl10_321
    | ~ spl10_4
    | spl10_83 ),
    inference(avatar_split_clause,[],[f26939,f5133,f129,f27015])).

fof(f27015,plain,
    ( spl10_321
  <=> ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK5(k1_relat_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_321])])).

fof(f26939,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK5(k1_relat_1(sK2)))))
    | ~ spl10_4
    | ~ spl10_83 ),
    inference(unit_resulting_resolution,[],[f5136,f107])).

fof(f5136,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_relat_1(sK2),X0),k7_relat_1(sK2,sK5(k1_relat_1(sK2))))
    | ~ spl10_4
    | ~ spl10_83 ),
    inference(unit_resulting_resolution,[],[f130,f174,f5134,f102])).

fof(f25924,plain,
    ( spl10_318
    | ~ spl10_312 ),
    inference(avatar_split_clause,[],[f25772,f25658,f25922])).

fof(f25922,plain,
    ( spl10_318
  <=> m1_subset_1(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_318])])).

fof(f25658,plain,
    ( spl10_312
  <=> r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_312])])).

fof(f25772,plain,
    ( m1_subset_1(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl10_312 ),
    inference(unit_resulting_resolution,[],[f25659,f87])).

fof(f25659,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl10_312 ),
    inference(avatar_component_clause,[],[f25658])).

fof(f25917,plain,
    ( spl10_316
    | ~ spl10_308 ),
    inference(avatar_split_clause,[],[f25666,f25613,f25915])).

fof(f25915,plain,
    ( spl10_316
  <=> m1_subset_1(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_316])])).

fof(f25613,plain,
    ( spl10_308
  <=> r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_308])])).

fof(f25666,plain,
    ( m1_subset_1(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK2))
    | ~ spl10_308 ),
    inference(unit_resulting_resolution,[],[f25614,f87])).

fof(f25614,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK2))
    | ~ spl10_308 ),
    inference(avatar_component_clause,[],[f25613])).

fof(f25910,plain,
    ( ~ spl10_315
    | ~ spl10_308 ),
    inference(avatar_split_clause,[],[f25665,f25613,f25908])).

fof(f25908,plain,
    ( spl10_315
  <=> ~ r2_hidden(k1_relat_1(sK2),sK5(k3_xboole_0(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_315])])).

fof(f25665,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK5(k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ spl10_308 ),
    inference(unit_resulting_resolution,[],[f25614,f86])).

fof(f25660,plain,
    ( spl10_312
    | ~ spl10_296 ),
    inference(avatar_split_clause,[],[f25457,f25265,f25658])).

fof(f25457,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl10_296 ),
    inference(forward_demodulation,[],[f25422,f82])).

fof(f25422,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)))
    | ~ spl10_296 ),
    inference(unit_resulting_resolution,[],[f25266,f25266,f2412])).

fof(f2412,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(X5,k3_xboole_0(X8,X7))
      | r2_hidden(X5,k3_xboole_0(X6,X7))
      | ~ r2_hidden(X5,k3_xboole_0(X9,X6)) ) ),
    inference(resolution,[],[f334,f109])).

fof(f334,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,X5)
      | r2_hidden(X4,k3_xboole_0(X5,X6))
      | ~ r2_hidden(X4,k3_xboole_0(X7,X6)) ) ),
    inference(resolution,[],[f108,f109])).

fof(f25653,plain,
    ( ~ spl10_311
    | ~ spl10_296 ),
    inference(avatar_split_clause,[],[f25391,f25265,f25651])).

fof(f25651,plain,
    ( spl10_311
  <=> ~ r2_hidden(k1_relat_1(sK1),sK5(k3_xboole_0(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_311])])).

fof(f25391,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK5(k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ spl10_296 ),
    inference(unit_resulting_resolution,[],[f25266,f211])).

fof(f25615,plain,
    ( spl10_308
    | ~ spl10_16
    | ~ spl10_296 ),
    inference(avatar_split_clause,[],[f25386,f25265,f183,f25613])).

fof(f25386,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK2))
    | ~ spl10_16
    | ~ spl10_296 ),
    inference(unit_resulting_resolution,[],[f25266,f8772])).

fof(f8772,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k3_xboole_0(X3,k1_relat_1(sK1)))
        | r2_hidden(X2,k1_relat_1(sK2)) )
    | ~ spl10_16 ),
    inference(resolution,[],[f8431,f109])).

fof(f8431,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK1))
        | r2_hidden(X3,k1_relat_1(sK2)) )
    | ~ spl10_16 ),
    inference(resolution,[],[f4794,f106])).

fof(f25593,plain,
    ( spl10_306
    | ~ spl10_304 ),
    inference(avatar_split_clause,[],[f25564,f25476,f25591])).

fof(f25591,plain,
    ( spl10_306
  <=> m1_subset_1(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_306])])).

fof(f25476,plain,
    ( spl10_304
  <=> r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_304])])).

fof(f25564,plain,
    ( m1_subset_1(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),sK0)
    | ~ spl10_304 ),
    inference(unit_resulting_resolution,[],[f25477,f87])).

fof(f25477,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),sK0)
    | ~ spl10_304 ),
    inference(avatar_component_clause,[],[f25476])).

fof(f25478,plain,
    ( spl10_304
    | ~ spl10_296 ),
    inference(avatar_split_clause,[],[f25461,f25265,f25476])).

fof(f25461,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),sK0)
    | ~ spl10_296 ),
    inference(forward_demodulation,[],[f25416,f82])).

fof(f25416,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,sK0))
    | ~ spl10_296 ),
    inference(unit_resulting_resolution,[],[f25266,f25266,f2343])).

fof(f2343,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X2,X3))
      | r2_hidden(X0,k3_xboole_0(X1,X2))
      | ~ r2_hidden(X0,k3_xboole_0(X1,X4)) ) ),
    inference(resolution,[],[f333,f110])).

fof(f333,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k3_xboole_0(X1,X2))
      | ~ r2_hidden(X0,k3_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f108,f110])).

fof(f25471,plain,
    ( ~ spl10_303
    | ~ spl10_296 ),
    inference(avatar_split_clause,[],[f25399,f25265,f25469])).

fof(f25469,plain,
    ( spl10_303
  <=> ~ r2_hidden(sK0,sK5(k3_xboole_0(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_303])])).

fof(f25399,plain,
    ( ~ r2_hidden(sK0,sK5(k3_xboole_0(sK0,k1_relat_1(sK1))))
    | ~ spl10_296 ),
    inference(unit_resulting_resolution,[],[f25266,f222])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f110,f86])).

fof(f25281,plain,
    ( spl10_300
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f22586,f20584,f25279])).

fof(f25279,plain,
    ( spl10_300
  <=> m1_subset_1(sK3(sK2,sK0,sK1),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_300])])).

fof(f20584,plain,
    ( spl10_274
  <=> r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_274])])).

fof(f22586,plain,
    ( m1_subset_1(sK3(sK2,sK0,sK1),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f20585,f87])).

fof(f20585,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_274 ),
    inference(avatar_component_clause,[],[f20584])).

fof(f25274,plain,
    ( ~ spl10_299
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f22585,f20584,f25272])).

fof(f25272,plain,
    ( spl10_299
  <=> ~ r2_hidden(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)),sK3(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_299])])).

fof(f22585,plain,
    ( ~ r2_hidden(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)),sK3(sK2,sK0,sK1))
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f20585,f86])).

fof(f25267,plain,
    ( spl10_296
    | ~ spl10_228 ),
    inference(avatar_split_clause,[],[f12280,f12176,f25265])).

fof(f12280,plain,
    ( r2_hidden(sK5(k3_xboole_0(sK0,k1_relat_1(sK1))),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_228 ),
    inference(unit_resulting_resolution,[],[f12177,f397])).

fof(f397,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | r2_hidden(sK5(X2),X2) ) ),
    inference(superposition,[],[f387,f82])).

fof(f387,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_xboole_0(X2,X0))
      | r2_hidden(sK5(X0),X0) ) ),
    inference(resolution,[],[f218,f81])).

fof(f218,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X5,X4)
      | r2_hidden(X5,X4)
      | ~ r2_hidden(X2,k3_xboole_0(X3,X4)) ) ),
    inference(resolution,[],[f212,f85])).

fof(f212,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_xboole_0(X5)
      | ~ r2_hidden(X3,k3_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f109,f93])).

fof(f24720,plain,
    ( ~ spl10_295
    | ~ spl10_12
    | spl10_59 ),
    inference(avatar_split_clause,[],[f11058,f2529,f160,f24718])).

fof(f24718,plain,
    ( spl10_295
  <=> ~ r2_hidden(k1_relat_1(k7_relat_1(sK2,sK1)),sK5(k1_relat_1(k7_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_295])])).

fof(f11058,plain,
    ( ~ r2_hidden(k1_relat_1(k7_relat_1(sK2,sK1)),sK5(k1_relat_1(k7_relat_1(sK2,sK1))))
    | ~ spl10_12
    | ~ spl10_59 ),
    inference(unit_resulting_resolution,[],[f2530,f11034])).

fof(f11034,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK5(X0))
        | k1_relat_1(X0) = k1_xboole_0 )
    | ~ spl10_12 ),
    inference(resolution,[],[f10993,f86])).

fof(f10993,plain,
    ( ! [X56] :
        ( r2_hidden(sK5(X56),X56)
        | k1_relat_1(X56) = k1_xboole_0 )
    | ~ spl10_12 ),
    inference(resolution,[],[f1179,f397])).

fof(f1179,plain,
    ( ! [X36] :
        ( r2_hidden(k4_tarski(sK6(X36,k1_xboole_0),sK7(X36,k1_xboole_0)),X36)
        | k1_relat_1(X36) = k1_xboole_0 )
    | ~ spl10_12 ),
    inference(resolution,[],[f90,f172])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f24713,plain,
    ( spl10_292
    | spl10_213 ),
    inference(avatar_split_clause,[],[f11028,f11025,f24711])).

fof(f24711,plain,
    ( spl10_292
  <=> r2_hidden(sK5(k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_292])])).

fof(f11025,plain,
    ( spl10_213
  <=> ~ v1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_213])])).

fof(f11028,plain,
    ( r2_hidden(sK5(k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl10_213 ),
    inference(unit_resulting_resolution,[],[f81,f11026,f85])).

fof(f11026,plain,
    ( ~ v1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl10_213 ),
    inference(avatar_component_clause,[],[f11025])).

fof(f22525,plain,
    ( spl10_290
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f16550,f16322,f22523])).

fof(f22523,plain,
    ( spl10_290
  <=> m1_subset_1(sK3(sK2,k1_xboole_0,sK1),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_290])])).

fof(f16322,plain,
    ( spl10_262
  <=> r2_hidden(sK3(sK2,k1_xboole_0,sK1),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_262])])).

fof(f16550,plain,
    ( m1_subset_1(sK3(sK2,k1_xboole_0,sK1),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f16323,f87])).

fof(f16323,plain,
    ( r2_hidden(sK3(sK2,k1_xboole_0,sK1),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_262 ),
    inference(avatar_component_clause,[],[f16322])).

fof(f22518,plain,
    ( ~ spl10_289
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f16549,f16322,f22516])).

fof(f22516,plain,
    ( spl10_289
  <=> ~ r2_hidden(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)),sK3(sK2,k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_289])])).

fof(f16549,plain,
    ( ~ r2_hidden(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)),sK3(sK2,k1_xboole_0,sK1))
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f16323,f86])).

fof(f21437,plain,
    ( ~ spl10_287
    | ~ spl10_0
    | spl10_195 ),
    inference(avatar_split_clause,[],[f21351,f9500,f115,f21435])).

fof(f21435,plain,
    ( spl10_287
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,sK3(sK2,k1_xboole_0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_287])])).

fof(f9500,plain,
    ( spl10_195
  <=> ~ r2_hidden(sK0,sK3(sK2,k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_195])])).

fof(f21351,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,sK3(sK2,k1_xboole_0,sK1))))
    | ~ spl10_0
    | ~ spl10_195 ),
    inference(unit_resulting_resolution,[],[f9511,f107])).

fof(f9511,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK1,sK3(sK2,k1_xboole_0,sK1)))
    | ~ spl10_0
    | ~ spl10_195 ),
    inference(unit_resulting_resolution,[],[f116,f173,f9501,f102])).

fof(f9501,plain,
    ( ~ r2_hidden(sK0,sK3(sK2,k1_xboole_0,sK1))
    | ~ spl10_195 ),
    inference(avatar_component_clause,[],[f9500])).

fof(f21281,plain,
    ( ~ spl10_285
    | ~ spl10_4
    | spl10_195 ),
    inference(avatar_split_clause,[],[f21203,f9500,f129,f21279])).

fof(f21279,plain,
    ( spl10_285
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK3(sK2,k1_xboole_0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_285])])).

fof(f21203,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK3(sK2,k1_xboole_0,sK1))))
    | ~ spl10_4
    | ~ spl10_195 ),
    inference(unit_resulting_resolution,[],[f9510,f107])).

fof(f9510,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK2,sK3(sK2,k1_xboole_0,sK1)))
    | ~ spl10_4
    | ~ spl10_195 ),
    inference(unit_resulting_resolution,[],[f130,f174,f9501,f102])).

fof(f21125,plain,
    ( ~ spl10_283
    | ~ spl10_0
    | spl10_185 ),
    inference(avatar_split_clause,[],[f21047,f9084,f115,f21123])).

fof(f21123,plain,
    ( spl10_283
  <=> ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK1,sK6(sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_283])])).

fof(f9084,plain,
    ( spl10_185
  <=> ~ r2_hidden(k1_relat_1(sK2),sK6(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_185])])).

fof(f21047,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK1,sK6(sK1,k1_xboole_0))))
    | ~ spl10_0
    | ~ spl10_185 ),
    inference(unit_resulting_resolution,[],[f9230,f107])).

fof(f9230,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_relat_1(sK2),X0),k7_relat_1(sK1,sK6(sK1,k1_xboole_0)))
    | ~ spl10_0
    | ~ spl10_185 ),
    inference(unit_resulting_resolution,[],[f116,f173,f9085,f102])).

fof(f9085,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK6(sK1,k1_xboole_0))
    | ~ spl10_185 ),
    inference(avatar_component_clause,[],[f9084])).

fof(f20977,plain,
    ( ~ spl10_281
    | ~ spl10_4
    | spl10_185 ),
    inference(avatar_split_clause,[],[f20899,f9084,f129,f20975])).

fof(f20975,plain,
    ( spl10_281
  <=> ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK6(sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_281])])).

fof(f20899,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK6(sK1,k1_xboole_0))))
    | ~ spl10_4
    | ~ spl10_185 ),
    inference(unit_resulting_resolution,[],[f9229,f107])).

fof(f9229,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_relat_1(sK2),X0),k7_relat_1(sK2,sK6(sK1,k1_xboole_0)))
    | ~ spl10_4
    | ~ spl10_185 ),
    inference(unit_resulting_resolution,[],[f130,f174,f9085,f102])).

fof(f20821,plain,
    ( ~ spl10_279
    | ~ spl10_0
    | spl10_181 ),
    inference(avatar_split_clause,[],[f20743,f8971,f115,f20819])).

fof(f20819,plain,
    ( spl10_279
  <=> ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK1,sK5(k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_279])])).

fof(f8971,plain,
    ( spl10_181
  <=> ~ r2_hidden(k1_relat_1(sK2),sK5(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_181])])).

fof(f20743,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK1,sK5(k1_relat_1(sK1)))))
    | ~ spl10_0
    | ~ spl10_181 ),
    inference(unit_resulting_resolution,[],[f9095,f107])).

fof(f9095,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_relat_1(sK2),X0),k7_relat_1(sK1,sK5(k1_relat_1(sK1))))
    | ~ spl10_0
    | ~ spl10_181 ),
    inference(unit_resulting_resolution,[],[f116,f173,f8972,f102])).

fof(f8972,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK5(k1_relat_1(sK1)))
    | ~ spl10_181 ),
    inference(avatar_component_clause,[],[f8971])).

fof(f20673,plain,
    ( ~ spl10_277
    | ~ spl10_4
    | spl10_181 ),
    inference(avatar_split_clause,[],[f20587,f8971,f129,f20671])).

fof(f20671,plain,
    ( spl10_277
  <=> ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK5(k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_277])])).

fof(f20587,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK5(k1_relat_1(sK1)))))
    | ~ spl10_4
    | ~ spl10_181 ),
    inference(unit_resulting_resolution,[],[f9094,f107])).

fof(f9094,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_relat_1(sK2),X0),k7_relat_1(sK2,sK5(k1_relat_1(sK1))))
    | ~ spl10_4
    | ~ spl10_181 ),
    inference(unit_resulting_resolution,[],[f130,f174,f8972,f102])).

fof(f20586,plain,
    ( spl10_274
    | ~ spl10_70
    | ~ spl10_116 ),
    inference(avatar_split_clause,[],[f8706,f6079,f4486,f20584])).

fof(f8706,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_70
    | ~ spl10_116 ),
    inference(unit_resulting_resolution,[],[f4487,f6080,f108])).

fof(f16501,plain,
    ( spl10_272
    | ~ spl10_250 ),
    inference(avatar_split_clause,[],[f15007,f14749,f16499])).

fof(f16499,plain,
    ( spl10_272
  <=> m1_subset_1(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_272])])).

fof(f14749,plain,
    ( spl10_250
  <=> r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_250])])).

fof(f15007,plain,
    ( m1_subset_1(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_250 ),
    inference(unit_resulting_resolution,[],[f14750,f87])).

fof(f14750,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_250 ),
    inference(avatar_component_clause,[],[f14749])).

fof(f16494,plain,
    ( ~ spl10_271
    | ~ spl10_250 ),
    inference(avatar_split_clause,[],[f15006,f14749,f16492])).

fof(f16492,plain,
    ( spl10_271
  <=> ~ r2_hidden(k3_xboole_0(sK0,k1_relat_1(sK1)),sK9(sK0,k1_relat_1(sK2),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_271])])).

fof(f15006,plain,
    ( ~ r2_hidden(k3_xboole_0(sK0,k1_relat_1(sK1)),sK9(sK0,k1_relat_1(sK2),k1_xboole_0))
    | ~ spl10_250 ),
    inference(unit_resulting_resolution,[],[f14750,f86])).

fof(f16466,plain,
    ( spl10_268
    | ~ spl10_248 ),
    inference(avatar_split_clause,[],[f14923,f14650,f16464])).

fof(f16464,plain,
    ( spl10_268
  <=> m1_subset_1(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_268])])).

fof(f14650,plain,
    ( spl10_248
  <=> r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_248])])).

fof(f14923,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_248 ),
    inference(unit_resulting_resolution,[],[f14651,f87])).

fof(f14651,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_248 ),
    inference(avatar_component_clause,[],[f14650])).

fof(f16459,plain,
    ( ~ spl10_267
    | ~ spl10_248 ),
    inference(avatar_split_clause,[],[f14922,f14650,f16457])).

fof(f16457,plain,
    ( spl10_267
  <=> ~ r2_hidden(k3_xboole_0(sK0,k1_relat_1(sK1)),sK9(k1_relat_1(sK2),sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_267])])).

fof(f14922,plain,
    ( ~ r2_hidden(k3_xboole_0(sK0,k1_relat_1(sK1)),sK9(k1_relat_1(sK2),sK0,k1_xboole_0))
    | ~ spl10_248 ),
    inference(unit_resulting_resolution,[],[f14651,f86])).

fof(f16452,plain,
    ( spl10_138
    | spl10_264
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f9805,f122,f115,f16450,f6900])).

fof(f6900,plain,
    ( spl10_138
  <=> r2_hidden(sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_138])])).

fof(f16450,plain,
    ( spl10_264
  <=> ! [X36,X37] : ~ r2_hidden(X36,k3_xboole_0(k1_relat_1(sK1),X37)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_264])])).

fof(f9805,plain,
    ( ! [X37,X36] :
        ( ~ r2_hidden(X36,k3_xboole_0(k1_relat_1(sK1),X37))
        | r2_hidden(sK5(sK1),sK1) )
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(resolution,[],[f369,f397])).

fof(f369,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(sK1),X1)) )
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(resolution,[],[f367,f110])).

fof(f16324,plain,
    ( spl10_262
    | ~ spl10_166
    | ~ spl10_188 ),
    inference(avatar_split_clause,[],[f9300,f9271,f8345,f16322])).

fof(f9271,plain,
    ( spl10_188
  <=> r2_hidden(sK3(sK2,k1_xboole_0,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_188])])).

fof(f9300,plain,
    ( r2_hidden(sK3(sK2,k1_xboole_0,sK1),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_166
    | ~ spl10_188 ),
    inference(forward_demodulation,[],[f9284,f83])).

fof(f9284,plain,
    ( r2_hidden(sK3(sK2,k1_xboole_0,sK1),k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK1)))
    | ~ spl10_166
    | ~ spl10_188 ),
    inference(unit_resulting_resolution,[],[f8346,f9272,f108])).

fof(f9272,plain,
    ( r2_hidden(sK3(sK2,k1_xboole_0,sK1),k1_relat_1(sK2))
    | ~ spl10_188 ),
    inference(avatar_component_clause,[],[f9271])).

fof(f16023,plain,
    ( ~ spl10_261
    | ~ spl10_0
    | spl10_161 ),
    inference(avatar_split_clause,[],[f15965,f8088,f115,f16021])).

fof(f16021,plain,
    ( spl10_261
  <=> ~ r2_hidden(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK6(sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_261])])).

fof(f8088,plain,
    ( spl10_161
  <=> ~ r2_hidden(k1_relat_1(sK1),sK6(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_161])])).

fof(f15965,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK6(sK1,k1_xboole_0))))
    | ~ spl10_0
    | ~ spl10_161 ),
    inference(unit_resulting_resolution,[],[f8099,f107])).

fof(f8099,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_relat_1(sK1),X0),k7_relat_1(sK1,sK6(sK1,k1_xboole_0)))
    | ~ spl10_0
    | ~ spl10_161 ),
    inference(unit_resulting_resolution,[],[f116,f173,f8089,f102])).

fof(f8089,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK6(sK1,k1_xboole_0))
    | ~ spl10_161 ),
    inference(avatar_component_clause,[],[f8088])).

fof(f15915,plain,
    ( ~ spl10_259
    | ~ spl10_4
    | spl10_161 ),
    inference(avatar_split_clause,[],[f15821,f8088,f129,f15913])).

fof(f15913,plain,
    ( spl10_259
  <=> ~ r2_hidden(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK6(sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_259])])).

fof(f15821,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK6(sK1,k1_xboole_0))))
    | ~ spl10_4
    | ~ spl10_161 ),
    inference(unit_resulting_resolution,[],[f8098,f107])).

fof(f8098,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_relat_1(sK1),X0),k7_relat_1(sK2,sK6(sK1,k1_xboole_0)))
    | ~ spl10_4
    | ~ spl10_161 ),
    inference(unit_resulting_resolution,[],[f130,f174,f8089,f102])).

fof(f15526,plain,
    ( ~ spl10_257
    | ~ spl10_0
    | spl10_79 ),
    inference(avatar_split_clause,[],[f15468,f5000,f115,f15524])).

fof(f15524,plain,
    ( spl10_257
  <=> ~ r2_hidden(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK5(k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_257])])).

fof(f5000,plain,
    ( spl10_79
  <=> ~ r2_hidden(k1_relat_1(sK1),sK5(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f15468,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK5(k1_relat_1(sK1)))))
    | ~ spl10_0
    | ~ spl10_79 ),
    inference(unit_resulting_resolution,[],[f5004,f107])).

fof(f5004,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_relat_1(sK1),X0),k7_relat_1(sK1,sK5(k1_relat_1(sK1))))
    | ~ spl10_0
    | ~ spl10_79 ),
    inference(unit_resulting_resolution,[],[f116,f173,f5001,f102])).

fof(f5001,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK5(k1_relat_1(sK1)))
    | ~ spl10_79 ),
    inference(avatar_component_clause,[],[f5000])).

fof(f15418,plain,
    ( ~ spl10_255
    | ~ spl10_4
    | spl10_79 ),
    inference(avatar_split_clause,[],[f15319,f5000,f129,f15416])).

fof(f15416,plain,
    ( spl10_255
  <=> ~ r2_hidden(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK5(k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_255])])).

fof(f15319,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK5(k1_relat_1(sK1)))))
    | ~ spl10_4
    | ~ spl10_79 ),
    inference(unit_resulting_resolution,[],[f5003,f107])).

fof(f5003,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(k1_relat_1(sK1),X0),k7_relat_1(sK2,sK5(k1_relat_1(sK1))))
    | ~ spl10_4
    | ~ spl10_79 ),
    inference(unit_resulting_resolution,[],[f130,f174,f5001,f102])).

fof(f15269,plain,
    ( ~ spl10_253
    | ~ spl10_0
    | spl10_53 ),
    inference(avatar_split_clause,[],[f15211,f2185,f115,f15267])).

fof(f15267,plain,
    ( spl10_253
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,sK3(sK2,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_253])])).

fof(f2185,plain,
    ( spl10_53
  <=> ~ r2_hidden(sK0,sK3(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f15211,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,sK3(sK2,sK0,sK1))))
    | ~ spl10_0
    | ~ spl10_53 ),
    inference(unit_resulting_resolution,[],[f4598,f107])).

fof(f4598,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK1,sK3(sK2,sK0,sK1)))
    | ~ spl10_0
    | ~ spl10_53 ),
    inference(unit_resulting_resolution,[],[f2186,f116,f173,f102])).

fof(f2186,plain,
    ( ~ r2_hidden(sK0,sK3(sK2,sK0,sK1))
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f2185])).

fof(f14751,plain,
    ( spl10_250
    | ~ spl10_86
    | ~ spl10_114 ),
    inference(avatar_split_clause,[],[f5963,f5808,f5225,f14749])).

fof(f5225,plain,
    ( spl10_86
  <=> r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f5963,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_86
    | ~ spl10_114 ),
    inference(forward_demodulation,[],[f5944,f83])).

fof(f5944,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k3_xboole_0(k1_relat_1(sK1),sK0))
    | ~ spl10_86
    | ~ spl10_114 ),
    inference(unit_resulting_resolution,[],[f5226,f5809,f108])).

fof(f5226,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),sK0)
    | ~ spl10_86 ),
    inference(avatar_component_clause,[],[f5225])).

fof(f14652,plain,
    ( spl10_248
    | ~ spl10_84
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f5873,f5765,f5218,f14650])).

fof(f5218,plain,
    ( spl10_84
  <=> r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f5873,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_84
    | ~ spl10_108 ),
    inference(forward_demodulation,[],[f5855,f83])).

fof(f5855,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k3_xboole_0(k1_relat_1(sK1),sK0))
    | ~ spl10_84
    | ~ spl10_108 ),
    inference(unit_resulting_resolution,[],[f5219,f5766,f108])).

fof(f5219,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),sK0)
    | ~ spl10_84 ),
    inference(avatar_component_clause,[],[f5218])).

fof(f14471,plain,
    ( spl10_80
    | spl10_24
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f402,f204,f415,f5033])).

fof(f5033,plain,
    ( spl10_80
  <=> r2_hidden(sK5(k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f415,plain,
    ( spl10_24
  <=> ! [X10] : ~ r2_hidden(X10,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f402,plain,
    ( ! [X13] :
        ( ~ r2_hidden(X13,k1_relat_1(sK1))
        | r2_hidden(sK5(k1_relat_1(sK2)),k1_relat_1(sK2)) )
    | ~ spl10_18 ),
    inference(superposition,[],[f387,f205])).

fof(f12548,plain,
    ( spl10_246
    | ~ spl10_228 ),
    inference(avatar_split_clause,[],[f12266,f12176,f12546])).

fof(f12546,plain,
    ( spl10_246
  <=> m1_subset_1(sK3(sK2,sK0,sK1),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_246])])).

fof(f12266,plain,
    ( m1_subset_1(sK3(sK2,sK0,sK1),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_228 ),
    inference(unit_resulting_resolution,[],[f12177,f87])).

fof(f12541,plain,
    ( ~ spl10_245
    | ~ spl10_228 ),
    inference(avatar_split_clause,[],[f12265,f12176,f12539])).

fof(f12539,plain,
    ( spl10_245
  <=> ~ r2_hidden(k3_xboole_0(sK0,k1_relat_1(sK1)),sK3(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_245])])).

fof(f12265,plain,
    ( ~ r2_hidden(k3_xboole_0(sK0,k1_relat_1(sK1)),sK3(sK2,sK0,sK1))
    | ~ spl10_228 ),
    inference(unit_resulting_resolution,[],[f12177,f86])).

fof(f12316,plain,
    ( ~ spl10_243
    | ~ spl10_228 ),
    inference(avatar_split_clause,[],[f12267,f12176,f12314])).

fof(f12267,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_228 ),
    inference(unit_resulting_resolution,[],[f12177,f93])).

fof(f12229,plain,
    ( spl10_240
    | ~ spl10_216 ),
    inference(avatar_split_clause,[],[f11339,f11078,f12227])).

fof(f12227,plain,
    ( spl10_240
  <=> m1_subset_1(k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_240])])).

fof(f11078,plain,
    ( spl10_216
  <=> r2_hidden(k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_216])])).

fof(f11339,plain,
    ( m1_subset_1(k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0)),sK2)
    | ~ spl10_216 ),
    inference(unit_resulting_resolution,[],[f11079,f87])).

fof(f11079,plain,
    ( r2_hidden(k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0)),sK2)
    | ~ spl10_216 ),
    inference(avatar_component_clause,[],[f11078])).

fof(f12222,plain,
    ( ~ spl10_239
    | ~ spl10_216 ),
    inference(avatar_split_clause,[],[f11338,f11078,f12220])).

fof(f12220,plain,
    ( spl10_239
  <=> ~ r2_hidden(sK2,k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_239])])).

fof(f11338,plain,
    ( ~ r2_hidden(sK2,k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0)))
    | ~ spl10_216 ),
    inference(unit_resulting_resolution,[],[f11079,f86])).

fof(f12206,plain,
    ( spl10_236
    | ~ spl10_214 ),
    inference(avatar_split_clause,[],[f11288,f11071,f12204])).

fof(f12204,plain,
    ( spl10_236
  <=> m1_subset_1(sK6(sK1,k1_xboole_0),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_236])])).

fof(f11071,plain,
    ( spl10_214
  <=> r2_hidden(sK6(sK1,k1_xboole_0),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_214])])).

fof(f11288,plain,
    ( m1_subset_1(sK6(sK1,k1_xboole_0),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_214 ),
    inference(unit_resulting_resolution,[],[f11072,f87])).

fof(f11072,plain,
    ( r2_hidden(sK6(sK1,k1_xboole_0),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_214 ),
    inference(avatar_component_clause,[],[f11071])).

fof(f12199,plain,
    ( ~ spl10_235
    | ~ spl10_214 ),
    inference(avatar_split_clause,[],[f11287,f11071,f12197])).

fof(f12197,plain,
    ( spl10_235
  <=> ~ r2_hidden(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)),sK6(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_235])])).

fof(f11287,plain,
    ( ~ r2_hidden(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)),sK6(sK1,k1_xboole_0))
    | ~ spl10_214 ),
    inference(unit_resulting_resolution,[],[f11072,f86])).

fof(f12192,plain,
    ( spl10_232
    | ~ spl10_210 ),
    inference(avatar_split_clause,[],[f11194,f10949,f12190])).

fof(f12190,plain,
    ( spl10_232
  <=> m1_subset_1(sK5(k1_relat_1(sK1)),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_232])])).

fof(f10949,plain,
    ( spl10_210
  <=> r2_hidden(sK5(k1_relat_1(sK1)),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_210])])).

fof(f11194,plain,
    ( m1_subset_1(sK5(k1_relat_1(sK1)),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_210 ),
    inference(unit_resulting_resolution,[],[f10950,f87])).

fof(f10950,plain,
    ( r2_hidden(sK5(k1_relat_1(sK1)),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_210 ),
    inference(avatar_component_clause,[],[f10949])).

fof(f12185,plain,
    ( ~ spl10_231
    | ~ spl10_210 ),
    inference(avatar_split_clause,[],[f11193,f10949,f12183])).

fof(f12183,plain,
    ( spl10_231
  <=> ~ r2_hidden(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)),sK5(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_231])])).

fof(f11193,plain,
    ( ~ r2_hidden(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)),sK5(k1_relat_1(sK1)))
    | ~ spl10_210 ),
    inference(unit_resulting_resolution,[],[f10950,f86])).

fof(f12178,plain,
    ( spl10_228
    | ~ spl10_50
    | ~ spl10_116 ),
    inference(avatar_split_clause,[],[f8723,f6079,f2160,f12176])).

fof(f2160,plain,
    ( spl10_50
  <=> r2_hidden(sK3(sK2,sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f8723,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(sK0,k1_relat_1(sK1)))
    | ~ spl10_50
    | ~ spl10_116 ),
    inference(forward_demodulation,[],[f8705,f83])).

fof(f8705,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(k1_relat_1(sK1),sK0))
    | ~ spl10_50
    | ~ spl10_116 ),
    inference(unit_resulting_resolution,[],[f2161,f6080,f108])).

fof(f2161,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f2160])).

fof(f11683,plain,
    ( ~ spl10_227
    | ~ spl10_0
    | spl10_169 ),
    inference(avatar_split_clause,[],[f11640,f8418,f115,f11681])).

fof(f11681,plain,
    ( spl10_227
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,sK6(sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_227])])).

fof(f8418,plain,
    ( spl10_169
  <=> ~ r2_hidden(sK0,sK6(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_169])])).

fof(f11640,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,sK6(sK1,k1_xboole_0))))
    | ~ spl10_0
    | ~ spl10_169 ),
    inference(unit_resulting_resolution,[],[f8478,f107])).

fof(f8478,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK1,sK6(sK1,k1_xboole_0)))
    | ~ spl10_0
    | ~ spl10_169 ),
    inference(unit_resulting_resolution,[],[f116,f173,f8419,f102])).

fof(f8419,plain,
    ( ~ r2_hidden(sK0,sK6(sK1,k1_xboole_0))
    | ~ spl10_169 ),
    inference(avatar_component_clause,[],[f8418])).

fof(f11597,plain,
    ( ~ spl10_225
    | ~ spl10_4
    | spl10_169 ),
    inference(avatar_split_clause,[],[f11554,f8418,f129,f11595])).

fof(f11595,plain,
    ( spl10_225
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK6(sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_225])])).

fof(f11554,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK6(sK1,k1_xboole_0))))
    | ~ spl10_4
    | ~ spl10_169 ),
    inference(unit_resulting_resolution,[],[f8477,f107])).

fof(f8477,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK2,sK6(sK1,k1_xboole_0)))
    | ~ spl10_4
    | ~ spl10_169 ),
    inference(unit_resulting_resolution,[],[f130,f174,f8419,f102])).

fof(f11505,plain,
    ( ~ spl10_223
    | ~ spl10_0
    | spl10_165 ),
    inference(avatar_split_clause,[],[f11462,f8268,f115,f11503])).

fof(f11503,plain,
    ( spl10_223
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,sK5(k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_223])])).

fof(f8268,plain,
    ( spl10_165
  <=> ~ r2_hidden(sK0,sK5(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_165])])).

fof(f11462,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,sK5(k1_relat_1(sK1)))))
    | ~ spl10_0
    | ~ spl10_165 ),
    inference(unit_resulting_resolution,[],[f8313,f107])).

fof(f8313,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK1,sK5(k1_relat_1(sK1))))
    | ~ spl10_0
    | ~ spl10_165 ),
    inference(unit_resulting_resolution,[],[f116,f173,f8269,f102])).

fof(f8269,plain,
    ( ~ r2_hidden(sK0,sK5(k1_relat_1(sK1)))
    | ~ spl10_165 ),
    inference(avatar_component_clause,[],[f8268])).

fof(f11419,plain,
    ( ~ spl10_221
    | ~ spl10_4
    | spl10_165 ),
    inference(avatar_split_clause,[],[f11370,f8268,f129,f11417])).

fof(f11417,plain,
    ( spl10_221
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK5(k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_221])])).

fof(f11370,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK5(k1_relat_1(sK1)))))
    | ~ spl10_4
    | ~ spl10_165 ),
    inference(unit_resulting_resolution,[],[f8312,f107])).

fof(f8312,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK2,sK5(k1_relat_1(sK1))))
    | ~ spl10_4
    | ~ spl10_165 ),
    inference(unit_resulting_resolution,[],[f130,f174,f8269,f102])).

fof(f11246,plain,
    ( ~ spl10_219
    | ~ spl10_210 ),
    inference(avatar_split_clause,[],[f11195,f10949,f11244])).

fof(f11195,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_210 ),
    inference(unit_resulting_resolution,[],[f10950,f93])).

fof(f11080,plain,
    ( spl10_216
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_156
    | ~ spl10_158
    | ~ spl10_178 ),
    inference(avatar_split_clause,[],[f8964,f8902,f8046,f7995,f136,f129,f122,f115,f11078])).

fof(f7995,plain,
    ( spl10_156
  <=> r2_hidden(k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_156])])).

fof(f8902,plain,
    ( spl10_178
  <=> r2_hidden(sK6(sK1,k1_xboole_0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_178])])).

fof(f8964,plain,
    ( r2_hidden(k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0)),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_156
    | ~ spl10_158
    | ~ spl10_178 ),
    inference(forward_demodulation,[],[f8936,f8081])).

fof(f8081,plain,
    ( k1_funct_1(sK2,sK6(sK1,k1_xboole_0)) = sK7(sK1,k1_xboole_0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_156
    | ~ spl10_158 ),
    inference(forward_demodulation,[],[f8053,f8002])).

fof(f8002,plain,
    ( k1_funct_1(sK1,sK6(sK1,k1_xboole_0)) = sK7(sK1,k1_xboole_0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_156 ),
    inference(unit_resulting_resolution,[],[f7996,f970])).

fof(f7996,plain,
    ( r2_hidden(k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0)),sK1)
    | ~ spl10_156 ),
    inference(avatar_component_clause,[],[f7995])).

fof(f8053,plain,
    ( k1_funct_1(sK1,sK6(sK1,k1_xboole_0)) = k1_funct_1(sK2,sK6(sK1,k1_xboole_0))
    | ~ spl10_158 ),
    inference(unit_resulting_resolution,[],[f8047,f66])).

fof(f8936,plain,
    ( r2_hidden(k4_tarski(sK6(sK1,k1_xboole_0),k1_funct_1(sK2,sK6(sK1,k1_xboole_0))),sK2)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_178 ),
    inference(unit_resulting_resolution,[],[f130,f137,f8903,f105])).

fof(f8903,plain,
    ( r2_hidden(sK6(sK1,k1_xboole_0),k1_relat_1(sK2))
    | ~ spl10_178 ),
    inference(avatar_component_clause,[],[f8902])).

fof(f11073,plain,
    ( spl10_214
    | ~ spl10_158
    | ~ spl10_178 ),
    inference(avatar_split_clause,[],[f8962,f8902,f8046,f11071])).

fof(f8962,plain,
    ( r2_hidden(sK6(sK1,k1_xboole_0),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_158
    | ~ spl10_178 ),
    inference(forward_demodulation,[],[f8945,f83])).

fof(f8945,plain,
    ( r2_hidden(sK6(sK1,k1_xboole_0),k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK1)))
    | ~ spl10_158
    | ~ spl10_178 ),
    inference(unit_resulting_resolution,[],[f8047,f8903,f108])).

fof(f11027,plain,
    ( ~ spl10_213
    | ~ spl10_12
    | spl10_59 ),
    inference(avatar_split_clause,[],[f11018,f2529,f160,f11025])).

fof(f11018,plain,
    ( ~ v1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl10_12
    | ~ spl10_59 ),
    inference(unit_resulting_resolution,[],[f2530,f10987])).

fof(f10987,plain,
    ( ! [X43] :
        ( ~ v1_xboole_0(X43)
        | k1_relat_1(X43) = k1_xboole_0 )
    | ~ spl10_12 ),
    inference(resolution,[],[f1179,f93])).

fof(f10951,plain,
    ( spl10_210
    | ~ spl10_76
    | ~ spl10_176 ),
    inference(avatar_split_clause,[],[f8930,f8895,f4959,f10949])).

fof(f8895,plain,
    ( spl10_176
  <=> r2_hidden(sK5(k1_relat_1(sK1)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_176])])).

fof(f8930,plain,
    ( r2_hidden(sK5(k1_relat_1(sK1)),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK2)))
    | ~ spl10_76
    | ~ spl10_176 ),
    inference(forward_demodulation,[],[f8914,f83])).

fof(f8914,plain,
    ( r2_hidden(sK5(k1_relat_1(sK1)),k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK1)))
    | ~ spl10_76
    | ~ spl10_176 ),
    inference(unit_resulting_resolution,[],[f4960,f8896,f108])).

fof(f8896,plain,
    ( r2_hidden(sK5(k1_relat_1(sK1)),k1_relat_1(sK2))
    | ~ spl10_176 ),
    inference(avatar_component_clause,[],[f8895])).

fof(f10566,plain,
    ( spl10_208
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_156
    | ~ spl10_158 ),
    inference(avatar_split_clause,[],[f8081,f8046,f7995,f122,f115,f10564])).

fof(f10466,plain,
    ( spl10_206
    | ~ spl10_156 ),
    inference(avatar_split_clause,[],[f8007,f7995,f10464])).

fof(f10464,plain,
    ( spl10_206
  <=> m1_subset_1(k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_206])])).

fof(f8007,plain,
    ( m1_subset_1(k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0)),sK1)
    | ~ spl10_156 ),
    inference(unit_resulting_resolution,[],[f7996,f87])).

fof(f10459,plain,
    ( ~ spl10_205
    | ~ spl10_156 ),
    inference(avatar_split_clause,[],[f8006,f7995,f10457])).

fof(f10457,plain,
    ( spl10_205
  <=> ~ r2_hidden(sK1,k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_205])])).

fof(f8006,plain,
    ( ~ r2_hidden(sK1,k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0)))
    | ~ spl10_156 ),
    inference(unit_resulting_resolution,[],[f7996,f86])).

fof(f10452,plain,
    ( spl10_202
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_156 ),
    inference(avatar_split_clause,[],[f8002,f7995,f122,f115,f10450])).

fof(f9998,plain,
    ( ~ spl10_135
    | ~ spl10_0
    | ~ spl10_2
    | spl10_131 ),
    inference(avatar_split_clause,[],[f9853,f6574,f122,f115,f6788])).

fof(f6788,plain,
    ( spl10_135
  <=> ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_135])])).

fof(f6574,plain,
    ( spl10_131
  <=> k1_funct_1(sK1,sK3(sK2,sK0,sK1)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_131])])).

fof(f9853,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_131 ),
    inference(unit_resulting_resolution,[],[f6575,f970])).

fof(f6575,plain,
    ( k1_funct_1(sK1,sK3(sK2,sK0,sK1)) != k1_xboole_0
    | ~ spl10_131 ),
    inference(avatar_component_clause,[],[f6574])).

fof(f9993,plain,
    ( ~ spl10_201
    | spl10_65
    | spl10_197 ),
    inference(avatar_split_clause,[],[f9814,f9544,f4353,f9991])).

fof(f9991,plain,
    ( spl10_201
  <=> ~ m1_subset_1(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_201])])).

fof(f4353,plain,
    ( spl10_65
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f9544,plain,
    ( spl10_197
  <=> ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_197])])).

fof(f9814,plain,
    ( ~ m1_subset_1(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK2)
    | ~ spl10_65
    | ~ spl10_197 ),
    inference(unit_resulting_resolution,[],[f4354,f9545,f85])).

fof(f9545,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK2)
    | ~ spl10_197 ),
    inference(avatar_component_clause,[],[f9544])).

fof(f4354,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_65 ),
    inference(avatar_component_clause,[],[f4353])).

fof(f9875,plain,
    ( spl10_138
    | spl10_137 ),
    inference(avatar_split_clause,[],[f6831,f6828,f6900])).

fof(f6828,plain,
    ( spl10_137
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_137])])).

fof(f6831,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl10_137 ),
    inference(unit_resulting_resolution,[],[f81,f6829,f85])).

fof(f6829,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl10_137 ),
    inference(avatar_component_clause,[],[f6828])).

fof(f9874,plain,
    ( spl10_137
    | spl10_139 ),
    inference(avatar_contradiction_clause,[],[f9873])).

fof(f9873,plain,
    ( $false
    | ~ spl10_137
    | ~ spl10_139 ),
    inference(subsumption_resolution,[],[f6898,f6831])).

fof(f6898,plain,
    ( ~ r2_hidden(sK5(sK1),sK1)
    | ~ spl10_139 ),
    inference(avatar_component_clause,[],[f6897])).

fof(f6897,plain,
    ( spl10_139
  <=> ~ r2_hidden(sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_139])])).

fof(f9872,plain,
    ( ~ spl10_0
    | ~ spl10_2
    | spl10_131
    | ~ spl10_134 ),
    inference(avatar_contradiction_clause,[],[f9871])).

fof(f9871,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_131
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f9853,f6792])).

fof(f6792,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ spl10_134 ),
    inference(avatar_component_clause,[],[f6791])).

fof(f6791,plain,
    ( spl10_134
  <=> r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_134])])).

fof(f9870,plain,
    ( ~ spl10_0
    | ~ spl10_2
    | ~ spl10_116
    | spl10_131
    | ~ spl10_134 ),
    inference(avatar_contradiction_clause,[],[f9869])).

fof(f9869,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_116
    | ~ spl10_131
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f9854,f6792])).

fof(f9854,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_116
    | ~ spl10_131 ),
    inference(unit_resulting_resolution,[],[f116,f123,f6080,f6575,f78])).

fof(f9595,plain,
    ( ~ spl10_199
    | ~ spl10_12
    | ~ spl10_116
    | spl10_129 ),
    inference(avatar_split_clause,[],[f9579,f6460,f6079,f160,f9593])).

fof(f9593,plain,
    ( spl10_199
  <=> ~ v1_xboole_0(k1_funct_1(sK1,sK3(sK2,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_199])])).

fof(f6460,plain,
    ( spl10_129
  <=> k1_funct_1(sK2,sK3(sK2,sK0,sK1)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_129])])).

fof(f9579,plain,
    ( ~ v1_xboole_0(k1_funct_1(sK1,sK3(sK2,sK0,sK1)))
    | ~ spl10_12
    | ~ spl10_116
    | ~ spl10_129 ),
    inference(forward_demodulation,[],[f9575,f8695])).

fof(f9575,plain,
    ( ~ v1_xboole_0(k1_funct_1(sK2,sK3(sK2,sK0,sK1)))
    | ~ spl10_12
    | ~ spl10_129 ),
    inference(unit_resulting_resolution,[],[f161,f6461,f92])).

fof(f6461,plain,
    ( k1_funct_1(sK2,sK3(sK2,sK0,sK1)) != k1_xboole_0
    | ~ spl10_129 ),
    inference(avatar_component_clause,[],[f6460])).

fof(f9558,plain,
    ( ~ spl10_116
    | spl10_129
    | ~ spl10_130 ),
    inference(avatar_contradiction_clause,[],[f9557])).

fof(f9557,plain,
    ( $false
    | ~ spl10_116
    | ~ spl10_129
    | ~ spl10_130 ),
    inference(subsumption_resolution,[],[f6461,f9550])).

fof(f9550,plain,
    ( k1_funct_1(sK2,sK3(sK2,sK0,sK1)) = k1_xboole_0
    | ~ spl10_116
    | ~ spl10_130 ),
    inference(backward_demodulation,[],[f6578,f8695])).

fof(f6578,plain,
    ( k1_funct_1(sK1,sK3(sK2,sK0,sK1)) = k1_xboole_0
    | ~ spl10_130 ),
    inference(avatar_component_clause,[],[f6577])).

fof(f6577,plain,
    ( spl10_130
  <=> k1_funct_1(sK1,sK3(sK2,sK0,sK1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_130])])).

fof(f9556,plain,
    ( ~ spl10_4
    | ~ spl10_6
    | ~ spl10_70
    | ~ spl10_116
    | ~ spl10_130
    | spl10_197 ),
    inference(avatar_contradiction_clause,[],[f9555])).

fof(f9555,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_70
    | ~ spl10_116
    | ~ spl10_130
    | ~ spl10_197 ),
    inference(subsumption_resolution,[],[f9545,f9552])).

fof(f9552,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK2)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_70
    | ~ spl10_116
    | ~ spl10_130 ),
    inference(forward_demodulation,[],[f8520,f9550])).

fof(f8520,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_funct_1(sK2,sK3(sK2,sK0,sK1))),sK2)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_70 ),
    inference(resolution,[],[f4487,f368])).

fof(f368,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2) )
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f366,f130])).

fof(f366,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_6 ),
    inference(resolution,[],[f105,f137])).

fof(f9549,plain,
    ( spl10_196
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_70
    | ~ spl10_128 ),
    inference(avatar_split_clause,[],[f8539,f6463,f4486,f136,f129,f9547])).

fof(f9547,plain,
    ( spl10_196
  <=> r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_196])])).

fof(f6463,plain,
    ( spl10_128
  <=> k1_funct_1(sK2,sK3(sK2,sK0,sK1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_128])])).

fof(f8539,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK2)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_70
    | ~ spl10_128 ),
    inference(forward_demodulation,[],[f8507,f6464])).

fof(f6464,plain,
    ( k1_funct_1(sK2,sK3(sK2,sK0,sK1)) = k1_xboole_0
    | ~ spl10_128 ),
    inference(avatar_component_clause,[],[f6463])).

fof(f9502,plain,
    ( ~ spl10_195
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f9493,f8345,f183,f9500])).

fof(f9493,plain,
    ( ~ r2_hidden(sK0,sK3(sK2,k1_xboole_0,sK1))
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(superposition,[],[f8348,f82])).

fof(f8348,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k3_xboole_0(sK3(sK2,k1_xboole_0,sK1),X0))
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f8346,f270])).

fof(f9419,plain,
    ( spl10_192
    | ~ spl10_188 ),
    inference(avatar_split_clause,[],[f9279,f9271,f9417])).

fof(f9417,plain,
    ( spl10_192
  <=> m1_subset_1(sK3(sK2,k1_xboole_0,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_192])])).

fof(f9279,plain,
    ( m1_subset_1(sK3(sK2,k1_xboole_0,sK1),k1_relat_1(sK2))
    | ~ spl10_188 ),
    inference(unit_resulting_resolution,[],[f9272,f87])).

fof(f9311,plain,
    ( ~ spl10_191
    | ~ spl10_188 ),
    inference(avatar_split_clause,[],[f9278,f9271,f9309])).

fof(f9309,plain,
    ( spl10_191
  <=> ~ r2_hidden(k1_relat_1(sK2),sK3(sK2,k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_191])])).

fof(f9278,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK3(sK2,k1_xboole_0,sK1))
    | ~ spl10_188 ),
    inference(unit_resulting_resolution,[],[f9272,f86])).

fof(f9273,plain,
    ( spl10_188
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f8766,f8345,f183,f9271])).

fof(f8766,plain,
    ( r2_hidden(sK3(sK2,k1_xboole_0,sK1),k1_relat_1(sK2))
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f8346,f8431])).

fof(f9093,plain,
    ( spl10_186
    | ~ spl10_178 ),
    inference(avatar_split_clause,[],[f8940,f8902,f9091])).

fof(f9091,plain,
    ( spl10_186
  <=> m1_subset_1(sK6(sK1,k1_xboole_0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_186])])).

fof(f8940,plain,
    ( m1_subset_1(sK6(sK1,k1_xboole_0),k1_relat_1(sK2))
    | ~ spl10_178 ),
    inference(unit_resulting_resolution,[],[f8903,f87])).

fof(f9086,plain,
    ( ~ spl10_185
    | ~ spl10_178 ),
    inference(avatar_split_clause,[],[f8939,f8902,f9084])).

fof(f8939,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK6(sK1,k1_xboole_0))
    | ~ spl10_178 ),
    inference(unit_resulting_resolution,[],[f8903,f86])).

fof(f9079,plain,
    ( spl10_182
    | ~ spl10_176 ),
    inference(avatar_split_clause,[],[f8910,f8895,f9077])).

fof(f9077,plain,
    ( spl10_182
  <=> m1_subset_1(sK5(k1_relat_1(sK1)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_182])])).

fof(f8910,plain,
    ( m1_subset_1(sK5(k1_relat_1(sK1)),k1_relat_1(sK2))
    | ~ spl10_176 ),
    inference(unit_resulting_resolution,[],[f8896,f87])).

fof(f8973,plain,
    ( ~ spl10_181
    | ~ spl10_176 ),
    inference(avatar_split_clause,[],[f8909,f8895,f8971])).

fof(f8909,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK5(k1_relat_1(sK1)))
    | ~ spl10_176 ),
    inference(unit_resulting_resolution,[],[f8896,f86])).

fof(f8904,plain,
    ( spl10_178
    | ~ spl10_16
    | ~ spl10_158 ),
    inference(avatar_split_clause,[],[f8768,f8046,f183,f8902])).

fof(f8768,plain,
    ( r2_hidden(sK6(sK1,k1_xboole_0),k1_relat_1(sK2))
    | ~ spl10_16
    | ~ spl10_158 ),
    inference(unit_resulting_resolution,[],[f8047,f8431])).

fof(f8897,plain,
    ( spl10_176
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(avatar_split_clause,[],[f8767,f4959,f183,f8895])).

fof(f8767,plain,
    ( r2_hidden(sK5(k1_relat_1(sK1)),k1_relat_1(sK2))
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(unit_resulting_resolution,[],[f4960,f8431])).

fof(f8691,plain,
    ( spl10_116
    | ~ spl10_18
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(avatar_split_clause,[],[f8536,f4486,f2160,f204,f6079])).

fof(f8536,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_18
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(forward_demodulation,[],[f8513,f205])).

fof(f8513,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(sK0,k1_relat_1(sK2)))
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(unit_resulting_resolution,[],[f2161,f4487,f108])).

fof(f8683,plain,
    ( ~ spl10_175
    | ~ spl10_70 ),
    inference(avatar_split_clause,[],[f8510,f4486,f8681])).

fof(f8681,plain,
    ( spl10_175
  <=> ~ r2_hidden(k1_relat_1(sK2),sK3(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_175])])).

fof(f8510,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK3(sK2,sK0,sK1))
    | ~ spl10_70 ),
    inference(unit_resulting_resolution,[],[f4487,f86])).

fof(f8558,plain,
    ( spl10_172
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f8356,f8345,f8556])).

fof(f8556,plain,
    ( spl10_172
  <=> m1_subset_1(sK3(sK2,k1_xboole_0,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_172])])).

fof(f8356,plain,
    ( m1_subset_1(sK3(sK2,k1_xboole_0,sK1),k1_relat_1(sK1))
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f8346,f87])).

fof(f8551,plain,
    ( ~ spl10_171
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f8355,f8345,f8549])).

fof(f8549,plain,
    ( spl10_171
  <=> ~ r2_hidden(k1_relat_1(sK1),sK3(sK2,k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_171])])).

fof(f8355,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK3(sK2,k1_xboole_0,sK1))
    | ~ spl10_166 ),
    inference(unit_resulting_resolution,[],[f8346,f86])).

fof(f8544,plain,
    ( ~ spl10_18
    | ~ spl10_50
    | ~ spl10_70
    | ~ spl10_128
    | spl10_131 ),
    inference(avatar_contradiction_clause,[],[f8543])).

fof(f8543,plain,
    ( $false
    | ~ spl10_18
    | ~ spl10_50
    | ~ spl10_70
    | ~ spl10_128
    | ~ spl10_131 ),
    inference(subsumption_resolution,[],[f6575,f8542])).

fof(f8542,plain,
    ( k1_funct_1(sK1,sK3(sK2,sK0,sK1)) = k1_xboole_0
    | ~ spl10_18
    | ~ spl10_50
    | ~ spl10_70
    | ~ spl10_128 ),
    inference(subsumption_resolution,[],[f6506,f8536])).

fof(f6506,plain,
    ( k1_funct_1(sK1,sK3(sK2,sK0,sK1)) = k1_xboole_0
    | ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_128 ),
    inference(superposition,[],[f6464,f66])).

fof(f8538,plain,
    ( ~ spl10_18
    | ~ spl10_50
    | ~ spl10_70
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f8537])).

fof(f8537,plain,
    ( $false
    | ~ spl10_18
    | ~ spl10_50
    | ~ spl10_70
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f8536,f6083])).

fof(f6083,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_117 ),
    inference(avatar_component_clause,[],[f6082])).

fof(f6082,plain,
    ( spl10_117
  <=> ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_117])])).

fof(f8534,plain,
    ( ~ spl10_18
    | ~ spl10_50
    | ~ spl10_70
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f8533])).

fof(f8533,plain,
    ( $false
    | ~ spl10_18
    | ~ spl10_50
    | ~ spl10_70
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f8532,f6083])).

fof(f8532,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_18
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(forward_demodulation,[],[f8531,f205])).

fof(f8531,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(sK0,k1_relat_1(sK2)))
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(forward_demodulation,[],[f8515,f83])).

fof(f8515,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(k1_relat_1(sK2),sK0))
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(unit_resulting_resolution,[],[f2161,f4487,f108])).

fof(f8476,plain,
    ( spl10_135
    | spl10_137
    | ~ spl10_150 ),
    inference(avatar_contradiction_clause,[],[f8475])).

fof(f8475,plain,
    ( $false
    | ~ spl10_135
    | ~ spl10_137
    | ~ spl10_150 ),
    inference(subsumption_resolution,[],[f6789,f7394])).

fof(f7394,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ spl10_137
    | ~ spl10_150 ),
    inference(resolution,[],[f7350,f6832])).

fof(f6832,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl10_137 ),
    inference(resolution,[],[f6829,f85])).

fof(f7350,plain,
    ( m1_subset_1(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ spl10_150 ),
    inference(avatar_component_clause,[],[f7349])).

fof(f7349,plain,
    ( spl10_150
  <=> m1_subset_1(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_150])])).

fof(f6789,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ spl10_135 ),
    inference(avatar_component_clause,[],[f6788])).

fof(f8474,plain,
    ( spl10_29
    | spl10_117
    | ~ spl10_118 ),
    inference(avatar_contradiction_clause,[],[f8473])).

fof(f8473,plain,
    ( $false
    | ~ spl10_29
    | ~ spl10_117
    | ~ spl10_118 ),
    inference(subsumption_resolution,[],[f8472,f515])).

fof(f8472,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | ~ spl10_117
    | ~ spl10_118 ),
    inference(subsumption_resolution,[],[f6737,f6083])).

fof(f6737,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | k1_relat_1(sK1) = k1_xboole_0
    | ~ spl10_118 ),
    inference(resolution,[],[f6087,f209])).

fof(f6087,plain,
    ( m1_subset_1(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_118 ),
    inference(avatar_component_clause,[],[f6086])).

fof(f6086,plain,
    ( spl10_118
  <=> m1_subset_1(sK3(sK2,sK0,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_118])])).

fof(f8469,plain,
    ( spl10_73
    | spl10_117
    | ~ spl10_118 ),
    inference(avatar_contradiction_clause,[],[f8468])).

fof(f8468,plain,
    ( $false
    | ~ spl10_73
    | ~ spl10_117
    | ~ spl10_118 ),
    inference(subsumption_resolution,[],[f6734,f6083])).

fof(f6734,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_73
    | ~ spl10_118 ),
    inference(resolution,[],[f6087,f4564])).

fof(f4564,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK1))
        | r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl10_73 ),
    inference(resolution,[],[f4561,f85])).

fof(f4561,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl10_73 ),
    inference(avatar_component_clause,[],[f4560])).

fof(f4560,plain,
    ( spl10_73
  <=> ~ v1_xboole_0(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f8467,plain,
    ( spl10_73
    | spl10_117
    | ~ spl10_118 ),
    inference(avatar_contradiction_clause,[],[f8466])).

fof(f8466,plain,
    ( $false
    | ~ spl10_73
    | ~ spl10_117
    | ~ spl10_118 ),
    inference(subsumption_resolution,[],[f6730,f6083])).

fof(f6730,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_73
    | ~ spl10_118 ),
    inference(unit_resulting_resolution,[],[f6087,f4564])).

fof(f8465,plain,
    ( ~ spl10_12
    | spl10_29
    | spl10_117
    | ~ spl10_118 ),
    inference(avatar_contradiction_clause,[],[f8464])).

fof(f8464,plain,
    ( $false
    | ~ spl10_12
    | ~ spl10_29
    | ~ spl10_117
    | ~ spl10_118 ),
    inference(subsumption_resolution,[],[f6731,f6083])).

fof(f6731,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_12
    | ~ spl10_29
    | ~ spl10_118 ),
    inference(unit_resulting_resolution,[],[f161,f515,f6087,f208])).

fof(f8463,plain,
    ( spl10_29
    | spl10_117
    | ~ spl10_118 ),
    inference(avatar_contradiction_clause,[],[f8462])).

fof(f8462,plain,
    ( $false
    | ~ spl10_29
    | ~ spl10_117
    | ~ spl10_118 ),
    inference(subsumption_resolution,[],[f6732,f6083])).

fof(f6732,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_29
    | ~ spl10_118 ),
    inference(unit_resulting_resolution,[],[f515,f6087,f209])).

fof(f8461,plain,
    ( spl10_73
    | spl10_117
    | ~ spl10_118 ),
    inference(avatar_contradiction_clause,[],[f8460])).

fof(f8460,plain,
    ( $false
    | ~ spl10_73
    | ~ spl10_117
    | ~ spl10_118 ),
    inference(subsumption_resolution,[],[f6733,f6083])).

fof(f6733,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_73
    | ~ spl10_118 ),
    inference(unit_resulting_resolution,[],[f4561,f6087,f85])).

fof(f8459,plain,
    ( ~ spl10_70
    | spl10_99 ),
    inference(avatar_contradiction_clause,[],[f8458])).

fof(f8458,plain,
    ( $false
    | ~ spl10_70
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f4487,f5495])).

fof(f5495,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK2))
    | ~ spl10_99 ),
    inference(resolution,[],[f5492,f87])).

fof(f5492,plain,
    ( ~ m1_subset_1(sK3(sK2,sK0,sK1),k1_relat_1(sK2))
    | ~ spl10_99 ),
    inference(avatar_component_clause,[],[f5491])).

fof(f5491,plain,
    ( spl10_99
  <=> ~ m1_subset_1(sK3(sK2,sK0,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).

fof(f8457,plain,
    ( spl10_117
    | ~ spl10_134 ),
    inference(avatar_contradiction_clause,[],[f8456])).

fof(f8456,plain,
    ( $false
    | ~ spl10_117
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f6083,f6811])).

fof(f6811,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_134 ),
    inference(resolution,[],[f6792,f106])).

fof(f8452,plain,
    ( ~ spl10_16
    | spl10_71
    | ~ spl10_116 ),
    inference(avatar_contradiction_clause,[],[f8451])).

fof(f8451,plain,
    ( $false
    | ~ spl10_16
    | ~ spl10_71
    | ~ spl10_116 ),
    inference(subsumption_resolution,[],[f8432,f6080])).

fof(f8432,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_16
    | ~ spl10_71 ),
    inference(resolution,[],[f4794,f5396])).

fof(f5396,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),X0),sK2)
    | ~ spl10_71 ),
    inference(unit_resulting_resolution,[],[f4484,f106])).

fof(f4484,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK2))
    | ~ spl10_71 ),
    inference(avatar_component_clause,[],[f4483])).

fof(f4483,plain,
    ( spl10_71
  <=> ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f8448,plain,
    ( ~ spl10_16
    | spl10_71
    | ~ spl10_116 ),
    inference(avatar_contradiction_clause,[],[f8447])).

fof(f8447,plain,
    ( $false
    | ~ spl10_16
    | ~ spl10_71
    | ~ spl10_116 ),
    inference(subsumption_resolution,[],[f8421,f5396])).

fof(f8421,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK8(sK2,sK3(sK2,sK0,sK1))),sK2)
    | ~ spl10_16
    | ~ spl10_116 ),
    inference(unit_resulting_resolution,[],[f6080,f4794])).

fof(f8446,plain,
    ( ~ spl10_16
    | spl10_71
    | ~ spl10_116 ),
    inference(avatar_contradiction_clause,[],[f8445])).

fof(f8445,plain,
    ( $false
    | ~ spl10_16
    | ~ spl10_71
    | ~ spl10_116 ),
    inference(subsumption_resolution,[],[f8427,f6080])).

fof(f8427,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_16
    | ~ spl10_71 ),
    inference(unit_resulting_resolution,[],[f5396,f4794])).

fof(f8444,plain,
    ( ~ spl10_16
    | spl10_71
    | ~ spl10_116 ),
    inference(avatar_contradiction_clause,[],[f8428])).

fof(f8428,plain,
    ( $false
    | ~ spl10_16
    | ~ spl10_71
    | ~ spl10_116 ),
    inference(unit_resulting_resolution,[],[f6080,f5396,f4794])).

fof(f8420,plain,
    ( ~ spl10_169
    | ~ spl10_16
    | ~ spl10_158 ),
    inference(avatar_split_clause,[],[f8411,f8046,f183,f8418])).

fof(f8411,plain,
    ( ~ r2_hidden(sK0,sK6(sK1,k1_xboole_0))
    | ~ spl10_16
    | ~ spl10_158 ),
    inference(superposition,[],[f8206,f82])).

fof(f8206,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k3_xboole_0(sK6(sK1,k1_xboole_0),X0))
    | ~ spl10_16
    | ~ spl10_158 ),
    inference(unit_resulting_resolution,[],[f8047,f270])).

fof(f8347,plain,
    ( spl10_166
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f8273,f1769,f8345])).

fof(f8273,plain,
    ( r2_hidden(sK3(sK2,k1_xboole_0,sK1),k1_relat_1(sK1))
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f1770,f106])).

fof(f8270,plain,
    ( ~ spl10_165
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(avatar_split_clause,[],[f8261,f4959,f183,f8268])).

fof(f8261,plain,
    ( ~ r2_hidden(sK0,sK5(k1_relat_1(sK1)))
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(superposition,[],[f8205,f82])).

fof(f8205,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k3_xboole_0(sK5(k1_relat_1(sK1)),X0))
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(unit_resulting_resolution,[],[f4960,f270])).

fof(f8097,plain,
    ( spl10_162
    | ~ spl10_158 ),
    inference(avatar_split_clause,[],[f8059,f8046,f8095])).

fof(f8095,plain,
    ( spl10_162
  <=> m1_subset_1(sK6(sK1,k1_xboole_0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_162])])).

fof(f8059,plain,
    ( m1_subset_1(sK6(sK1,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl10_158 ),
    inference(unit_resulting_resolution,[],[f8047,f87])).

fof(f8090,plain,
    ( ~ spl10_161
    | ~ spl10_158 ),
    inference(avatar_split_clause,[],[f8058,f8046,f8088])).

fof(f8058,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK6(sK1,k1_xboole_0))
    | ~ spl10_158 ),
    inference(unit_resulting_resolution,[],[f8047,f86])).

fof(f8048,plain,
    ( spl10_158
    | ~ spl10_156 ),
    inference(avatar_split_clause,[],[f8004,f7995,f8046])).

fof(f8004,plain,
    ( r2_hidden(sK6(sK1,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl10_156 ),
    inference(unit_resulting_resolution,[],[f7996,f106])).

fof(f7997,plain,
    ( spl10_156
    | ~ spl10_12
    | spl10_29 ),
    inference(avatar_split_clause,[],[f4545,f514,f160,f7995])).

fof(f4545,plain,
    ( r2_hidden(k4_tarski(sK6(sK1,k1_xboole_0),sK7(sK1,k1_xboole_0)),sK1)
    | ~ spl10_12
    | ~ spl10_29 ),
    inference(unit_resulting_resolution,[],[f172,f515,f90])).

fof(f7737,plain,
    ( ~ spl10_155
    | ~ spl10_0
    | spl10_141 ),
    inference(avatar_split_clause,[],[f7698,f6926,f115,f7735])).

fof(f7735,plain,
    ( spl10_155
  <=> ~ r2_hidden(sK1,k1_relat_1(k7_relat_1(sK1,sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_155])])).

fof(f6926,plain,
    ( spl10_141
  <=> ~ r2_hidden(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_141])])).

fof(f7698,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(k7_relat_1(sK1,sK5(sK1))))
    | ~ spl10_0
    | ~ spl10_141 ),
    inference(unit_resulting_resolution,[],[f6930,f107])).

fof(f6930,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK1,X0),k7_relat_1(sK1,sK5(sK1)))
    | ~ spl10_0
    | ~ spl10_141 ),
    inference(unit_resulting_resolution,[],[f116,f173,f6927,f102])).

fof(f6927,plain,
    ( ~ r2_hidden(sK1,sK5(sK1))
    | ~ spl10_141 ),
    inference(avatar_component_clause,[],[f6926])).

fof(f7600,plain,
    ( ~ spl10_153
    | ~ spl10_4
    | spl10_141 ),
    inference(avatar_split_clause,[],[f7561,f6926,f129,f7598])).

fof(f7598,plain,
    ( spl10_153
  <=> ~ r2_hidden(sK1,k1_relat_1(k7_relat_1(sK2,sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_153])])).

fof(f7561,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(k7_relat_1(sK2,sK5(sK1))))
    | ~ spl10_4
    | ~ spl10_141 ),
    inference(unit_resulting_resolution,[],[f6929,f107])).

fof(f6929,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK1,X0),k7_relat_1(sK2,sK5(sK1)))
    | ~ spl10_4
    | ~ spl10_141 ),
    inference(unit_resulting_resolution,[],[f130,f174,f6927,f102])).

fof(f7351,plain,
    ( spl10_150
    | ~ spl10_134 ),
    inference(avatar_split_clause,[],[f6802,f6791,f7349])).

fof(f6802,plain,
    ( m1_subset_1(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ spl10_134 ),
    inference(unit_resulting_resolution,[],[f6792,f87])).

fof(f7344,plain,
    ( ~ spl10_149
    | ~ spl10_134 ),
    inference(avatar_split_clause,[],[f6801,f6791,f7342])).

fof(f7342,plain,
    ( spl10_149
  <=> ~ r2_hidden(sK1,k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_149])])).

fof(f6801,plain,
    ( ~ r2_hidden(sK1,k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0))
    | ~ spl10_134 ),
    inference(unit_resulting_resolution,[],[f6792,f86])).

fof(f7237,plain,
    ( ~ spl10_147
    | ~ spl10_0
    | spl10_69 ),
    inference(avatar_split_clause,[],[f7198,f4395,f115,f7235])).

fof(f7235,plain,
    ( spl10_147
  <=> ~ r2_hidden(sK2,k1_relat_1(k7_relat_1(sK1,sK5(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_147])])).

fof(f4395,plain,
    ( spl10_69
  <=> ~ r2_hidden(sK2,sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f7198,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k7_relat_1(sK1,sK5(sK2))))
    | ~ spl10_0
    | ~ spl10_69 ),
    inference(unit_resulting_resolution,[],[f4600,f107])).

fof(f4600,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK2,X0),k7_relat_1(sK1,sK5(sK2)))
    | ~ spl10_0
    | ~ spl10_69 ),
    inference(unit_resulting_resolution,[],[f4396,f116,f173,f102])).

fof(f4396,plain,
    ( ~ r2_hidden(sK2,sK5(sK2))
    | ~ spl10_69 ),
    inference(avatar_component_clause,[],[f4395])).

fof(f7163,plain,
    ( ~ spl10_145
    | ~ spl10_0
    | spl10_45 ),
    inference(avatar_split_clause,[],[f7124,f2066,f115,f7161])).

fof(f7161,plain,
    ( spl10_145
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_145])])).

fof(f2066,plain,
    ( spl10_45
  <=> ~ r2_hidden(sK0,sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f7124,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,sK5(sK0))))
    | ~ spl10_0
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f4599,f107])).

fof(f4599,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK1,sK5(sK0)))
    | ~ spl10_0
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f2067,f116,f173,f102])).

fof(f2067,plain,
    ( ~ r2_hidden(sK0,sK5(sK0))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f2066])).

fof(f7087,plain,
    ( ~ spl10_143
    | ~ spl10_4
    | spl10_69 ),
    inference(avatar_split_clause,[],[f7048,f4395,f129,f7085])).

fof(f7085,plain,
    ( spl10_143
  <=> ~ r2_hidden(sK2,k1_relat_1(k7_relat_1(sK2,sK5(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_143])])).

fof(f7048,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k7_relat_1(sK2,sK5(sK2))))
    | ~ spl10_4
    | ~ spl10_69 ),
    inference(unit_resulting_resolution,[],[f4398,f107])).

fof(f4398,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK2,X0),k7_relat_1(sK2,sK5(sK2)))
    | ~ spl10_4
    | ~ spl10_69 ),
    inference(unit_resulting_resolution,[],[f130,f174,f4396,f102])).

fof(f6928,plain,
    ( ~ spl10_141
    | ~ spl10_138 ),
    inference(avatar_split_clause,[],[f6904,f6900,f6926])).

fof(f6904,plain,
    ( ~ r2_hidden(sK1,sK5(sK1))
    | ~ spl10_138 ),
    inference(unit_resulting_resolution,[],[f6901,f86])).

fof(f6901,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl10_138 ),
    inference(avatar_component_clause,[],[f6900])).

fof(f6902,plain,
    ( spl10_138
    | ~ spl10_134 ),
    inference(avatar_split_clause,[],[f6808,f6791,f6900])).

fof(f6808,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl10_134 ),
    inference(unit_resulting_resolution,[],[f6792,f397])).

fof(f6830,plain,
    ( ~ spl10_137
    | ~ spl10_134 ),
    inference(avatar_split_clause,[],[f6803,f6791,f6828])).

fof(f6803,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl10_134 ),
    inference(unit_resulting_resolution,[],[f6792,f93])).

fof(f6793,plain,
    ( spl10_134
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_116
    | ~ spl10_130 ),
    inference(avatar_split_clause,[],[f6726,f6577,f6079,f122,f115,f6791])).

fof(f6726,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_xboole_0),sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_116
    | ~ spl10_130 ),
    inference(forward_demodulation,[],[f6700,f6578])).

fof(f6700,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),k1_funct_1(sK1,sK3(sK2,sK0,sK1))),sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_116 ),
    inference(unit_resulting_resolution,[],[f116,f123,f6080,f105])).

fof(f6744,plain,
    ( ~ spl10_133
    | ~ spl10_116 ),
    inference(avatar_split_clause,[],[f6703,f6079,f6742])).

fof(f6742,plain,
    ( spl10_133
  <=> ~ r2_hidden(k1_relat_1(sK1),sK3(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_133])])).

fof(f6703,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK3(sK2,sK0,sK1))
    | ~ spl10_116 ),
    inference(unit_resulting_resolution,[],[f6080,f86])).

fof(f6657,plain,
    ( ~ spl10_116
    | spl10_119 ),
    inference(avatar_contradiction_clause,[],[f6656])).

fof(f6656,plain,
    ( $false
    | ~ spl10_116
    | ~ spl10_119 ),
    inference(subsumption_resolution,[],[f6080,f6131])).

fof(f6131,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_119 ),
    inference(resolution,[],[f6090,f87])).

fof(f6090,plain,
    ( ~ m1_subset_1(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_119 ),
    inference(avatar_component_clause,[],[f6089])).

fof(f6089,plain,
    ( spl10_119
  <=> ~ m1_subset_1(sK3(sK2,sK0,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_119])])).

fof(f6655,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_51
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6654])).

fof(f6654,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f6580,f2158])).

fof(f2158,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f2157])).

fof(f2157,plain,
    ( spl10_51
  <=> ~ r2_hidden(sK3(sK2,sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f6580,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f130,f151,f6097,f1433])).

fof(f1433,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK3(X0,X1,sK1),sK4(X0,X1,sK1)),sK1)
        | k7_relat_1(X0,X1) = sK1
        | r2_hidden(sK3(X0,X1,sK1),X1) )
    | ~ spl10_0 ),
    inference(resolution,[],[f74,f116])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6097,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),X0),sK1)
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f6083,f106])).

fof(f6653,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_51
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6652])).

fof(f6652,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f6581,f151])).

fof(f6581,plain,
    ( k7_relat_1(sK2,sK0) = sK1
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f130,f2158,f6097,f1433])).

fof(f6651,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_51
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6650])).

fof(f6650,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f6582,f130])).

fof(f6582,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl10_0
    | ~ spl10_11
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f151,f2158,f6097,f1433])).

fof(f6649,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_63
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6648])).

fof(f6648,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_63
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f6584,f4300])).

fof(f6584,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f130,f116,f151,f6097,f75])).

fof(f6647,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_71
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6646])).

fof(f6646,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_71
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f6585,f151])).

fof(f6585,plain,
    ( k7_relat_1(sK2,sK0) = sK1
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_71
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f130,f116,f5396,f6097,f75])).

fof(f6645,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_71
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6644])).

fof(f6644,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_71
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f6586,f116])).

fof(f6586,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_71
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f130,f151,f5396,f6097,f75])).

fof(f6643,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_71
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6642])).

fof(f6642,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_71
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f6587,f130])).

fof(f6587,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl10_0
    | ~ spl10_11
    | ~ spl10_71
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f116,f151,f5396,f6097,f75])).

fof(f6641,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_51
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6640])).

fof(f6640,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f6589,f2158])).

fof(f6589,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f130,f116,f151,f6097,f74])).

fof(f6639,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_51
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6638])).

fof(f6638,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f6590,f151])).

fof(f6590,plain,
    ( k7_relat_1(sK2,sK0) = sK1
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f130,f116,f2158,f6097,f74])).

fof(f6637,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_51
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6636])).

fof(f6636,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f6591,f116])).

fof(f6591,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f130,f151,f2158,f6097,f74])).

fof(f6635,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_51
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6634])).

fof(f6634,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(subsumption_resolution,[],[f6592,f130])).

fof(f6592,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl10_0
    | ~ spl10_11
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f116,f151,f2158,f6097,f74])).

fof(f6633,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_51
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6593])).

fof(f6593,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f130,f116,f151,f2158,f6097,f74])).

fof(f6632,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_71
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6588])).

fof(f6588,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_71
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f130,f116,f151,f5396,f6097,f75])).

fof(f6631,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | spl10_51
    | spl10_117 ),
    inference(avatar_contradiction_clause,[],[f6583])).

fof(f6583,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_51
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f130,f151,f2158,f6097,f1433])).

fof(f6579,plain,
    ( spl10_130
    | ~ spl10_0
    | ~ spl10_2
    | spl10_117 ),
    inference(avatar_split_clause,[],[f6096,f6082,f122,f115,f6577])).

fof(f6096,plain,
    ( k1_funct_1(sK1,sK3(sK2,sK0,sK1)) = k1_xboole_0
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_117 ),
    inference(unit_resulting_resolution,[],[f116,f123,f6083,f103])).

fof(f6465,plain,
    ( spl10_128
    | ~ spl10_4
    | ~ spl10_6
    | spl10_71 ),
    inference(avatar_split_clause,[],[f5395,f4483,f136,f129,f6463])).

fof(f5395,plain,
    ( k1_funct_1(sK2,sK3(sK2,sK0,sK1)) = k1_xboole_0
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_71 ),
    inference(unit_resulting_resolution,[],[f130,f137,f4484,f103])).

fof(f6228,plain,
    ( spl10_126
    | ~ spl10_114 ),
    inference(avatar_split_clause,[],[f5939,f5808,f6226])).

fof(f6226,plain,
    ( spl10_126
  <=> m1_subset_1(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_126])])).

fof(f5939,plain,
    ( m1_subset_1(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k1_relat_1(sK1))
    | ~ spl10_114 ),
    inference(unit_resulting_resolution,[],[f5809,f87])).

fof(f6221,plain,
    ( ~ spl10_125
    | ~ spl10_114 ),
    inference(avatar_split_clause,[],[f5938,f5808,f6219])).

fof(f6219,plain,
    ( spl10_125
  <=> ~ r2_hidden(k1_relat_1(sK1),sK9(sK0,k1_relat_1(sK2),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_125])])).

fof(f5938,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK9(sK0,k1_relat_1(sK2),k1_xboole_0))
    | ~ spl10_114 ),
    inference(unit_resulting_resolution,[],[f5809,f86])).

fof(f6214,plain,
    ( spl10_122
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f5850,f5765,f6212])).

fof(f6212,plain,
    ( spl10_122
  <=> m1_subset_1(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_122])])).

fof(f5850,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl10_108 ),
    inference(unit_resulting_resolution,[],[f5766,f87])).

fof(f6207,plain,
    ( ~ spl10_121
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f5849,f5765,f6205])).

fof(f6205,plain,
    ( spl10_121
  <=> ~ r2_hidden(k1_relat_1(sK1),sK9(k1_relat_1(sK2),sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_121])])).

fof(f5849,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK9(k1_relat_1(sK2),sK0,k1_xboole_0))
    | ~ spl10_108 ),
    inference(unit_resulting_resolution,[],[f5766,f86])).

fof(f6091,plain,
    ( ~ spl10_119
    | ~ spl10_18
    | spl10_47
    | spl10_51 ),
    inference(avatar_split_clause,[],[f6075,f2157,f2104,f204,f6089])).

fof(f2104,plain,
    ( spl10_47
  <=> k3_xboole_0(k1_relat_1(sK2),sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f6075,plain,
    ( ~ m1_subset_1(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_18
    | ~ spl10_47
    | ~ spl10_51 ),
    inference(forward_demodulation,[],[f6074,f205])).

fof(f6074,plain,
    ( ~ m1_subset_1(sK3(sK2,sK0,sK1),k3_xboole_0(sK0,k1_relat_1(sK2)))
    | ~ spl10_47
    | ~ spl10_51 ),
    inference(forward_demodulation,[],[f6048,f83])).

fof(f6048,plain,
    ( ~ m1_subset_1(sK3(sK2,sK0,sK1),k3_xboole_0(k1_relat_1(sK2),sK0))
    | ~ spl10_47
    | ~ spl10_51 ),
    inference(unit_resulting_resolution,[],[f2105,f4933,f209])).

fof(f4933,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(X0,sK0))
    | ~ spl10_51 ),
    inference(unit_resulting_resolution,[],[f2158,f109])).

fof(f2105,plain,
    ( k3_xboole_0(k1_relat_1(sK2),sK0) != k1_xboole_0
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f2104])).

fof(f6084,plain,
    ( ~ spl10_117
    | ~ spl10_16
    | spl10_51 ),
    inference(avatar_split_clause,[],[f6072,f2157,f183,f6082])).

fof(f6072,plain,
    ( ~ r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK1))
    | ~ spl10_16
    | ~ spl10_51 ),
    inference(superposition,[],[f4933,f184])).

fof(f5810,plain,
    ( spl10_114
    | ~ spl10_18
    | ~ spl10_86
    | ~ spl10_102 ),
    inference(avatar_split_clause,[],[f5582,f5522,f5225,f204,f5808])).

fof(f5582,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k1_relat_1(sK1))
    | ~ spl10_18
    | ~ spl10_86
    | ~ spl10_102 ),
    inference(forward_demodulation,[],[f5581,f205])).

fof(f5581,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k3_xboole_0(sK0,k1_relat_1(sK2)))
    | ~ spl10_86
    | ~ spl10_102 ),
    inference(forward_demodulation,[],[f5565,f83])).

fof(f5565,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k3_xboole_0(k1_relat_1(sK2),sK0))
    | ~ spl10_86
    | ~ spl10_102 ),
    inference(unit_resulting_resolution,[],[f5226,f5523,f108])).

fof(f5803,plain,
    ( spl10_112
    | ~ spl10_102 ),
    inference(avatar_split_clause,[],[f5561,f5522,f5801])).

fof(f5801,plain,
    ( spl10_112
  <=> m1_subset_1(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_112])])).

fof(f5561,plain,
    ( m1_subset_1(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k1_relat_1(sK2))
    | ~ spl10_102 ),
    inference(unit_resulting_resolution,[],[f5523,f87])).

fof(f5774,plain,
    ( ~ spl10_111
    | ~ spl10_102 ),
    inference(avatar_split_clause,[],[f5560,f5522,f5772])).

fof(f5772,plain,
    ( spl10_111
  <=> ~ r2_hidden(k1_relat_1(sK2),sK9(sK0,k1_relat_1(sK2),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_111])])).

fof(f5560,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK9(sK0,k1_relat_1(sK2),k1_xboole_0))
    | ~ spl10_102 ),
    inference(unit_resulting_resolution,[],[f5523,f86])).

fof(f5767,plain,
    ( spl10_108
    | ~ spl10_18
    | ~ spl10_84
    | ~ spl10_100 ),
    inference(avatar_split_clause,[],[f5552,f5515,f5218,f204,f5765])).

fof(f5552,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl10_18
    | ~ spl10_84
    | ~ spl10_100 ),
    inference(forward_demodulation,[],[f5551,f205])).

fof(f5551,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k3_xboole_0(sK0,k1_relat_1(sK2)))
    | ~ spl10_84
    | ~ spl10_100 ),
    inference(forward_demodulation,[],[f5535,f83])).

fof(f5535,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k3_xboole_0(k1_relat_1(sK2),sK0))
    | ~ spl10_84
    | ~ spl10_100 ),
    inference(unit_resulting_resolution,[],[f5219,f5516,f108])).

fof(f5760,plain,
    ( spl10_106
    | ~ spl10_100 ),
    inference(avatar_split_clause,[],[f5531,f5515,f5758])).

fof(f5758,plain,
    ( spl10_106
  <=> m1_subset_1(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f5531,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k1_relat_1(sK2))
    | ~ spl10_100 ),
    inference(unit_resulting_resolution,[],[f5516,f87])).

fof(f5753,plain,
    ( ~ spl10_105
    | ~ spl10_100 ),
    inference(avatar_split_clause,[],[f5530,f5515,f5751])).

fof(f5751,plain,
    ( spl10_105
  <=> ~ r2_hidden(k1_relat_1(sK2),sK9(k1_relat_1(sK2),sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_105])])).

fof(f5530,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK9(k1_relat_1(sK2),sK0,k1_xboole_0))
    | ~ spl10_100 ),
    inference(unit_resulting_resolution,[],[f5516,f86])).

fof(f5524,plain,
    ( spl10_102
    | ~ spl10_12
    | spl10_49 ),
    inference(avatar_split_clause,[],[f4770,f2143,f160,f5522])).

fof(f2143,plain,
    ( spl10_49
  <=> k3_xboole_0(sK0,k1_relat_1(sK2)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f4770,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),k1_relat_1(sK2))
    | ~ spl10_12
    | ~ spl10_49 ),
    inference(unit_resulting_resolution,[],[f161,f2144,f795])).

fof(f795,plain,(
    ! [X19,X20,X18] :
      ( ~ v1_xboole_0(X20)
      | k3_xboole_0(X18,X19) = X20
      | r2_hidden(sK9(X18,X19,X20),X19) ) ),
    inference(resolution,[],[f98,f93])).

fof(f2144,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK2)) != k1_xboole_0
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f2143])).

fof(f5517,plain,
    ( spl10_100
    | ~ spl10_12
    | spl10_47 ),
    inference(avatar_split_clause,[],[f4716,f2104,f160,f5515])).

fof(f4716,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),k1_relat_1(sK2))
    | ~ spl10_12
    | ~ spl10_47 ),
    inference(unit_resulting_resolution,[],[f161,f2105,f686])).

fof(f686,plain,(
    ! [X19,X20,X18] :
      ( ~ v1_xboole_0(X20)
      | k3_xboole_0(X18,X19) = X20
      | r2_hidden(sK9(X18,X19,X20),X18) ) ),
    inference(resolution,[],[f97,f93])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X2)
      | r2_hidden(sK9(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f5493,plain,
    ( ~ spl10_99
    | spl10_71
    | spl10_75 ),
    inference(avatar_split_clause,[],[f5397,f4754,f4483,f5491])).

fof(f4754,plain,
    ( spl10_75
  <=> ~ v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f5397,plain,
    ( ~ m1_subset_1(sK3(sK2,sK0,sK1),k1_relat_1(sK2))
    | ~ spl10_71
    | ~ spl10_75 ),
    inference(unit_resulting_resolution,[],[f4755,f4484,f85])).

fof(f4755,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl10_75 ),
    inference(avatar_component_clause,[],[f4754])).

fof(f5444,plain,
    ( ~ spl10_97
    | ~ spl10_12
    | spl10_59 ),
    inference(avatar_split_clause,[],[f5435,f2529,f160,f5442])).

fof(f5442,plain,
    ( spl10_97
  <=> ~ v1_xboole_0(k1_relat_1(k1_relat_1(k7_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).

fof(f5435,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))))
    | ~ spl10_12
    | ~ spl10_59 ),
    inference(unit_resulting_resolution,[],[f161,f2530,f92])).

fof(f5295,plain,
    ( spl10_94
    | ~ spl10_86 ),
    inference(avatar_split_clause,[],[f5249,f5225,f5293])).

fof(f5293,plain,
    ( spl10_94
  <=> m1_subset_1(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f5249,plain,
    ( m1_subset_1(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),sK0)
    | ~ spl10_86 ),
    inference(unit_resulting_resolution,[],[f5226,f87])).

fof(f5288,plain,
    ( ~ spl10_93
    | ~ spl10_86 ),
    inference(avatar_split_clause,[],[f5248,f5225,f5286])).

fof(f5248,plain,
    ( ~ r2_hidden(sK0,sK9(sK0,k1_relat_1(sK2),k1_xboole_0))
    | ~ spl10_86 ),
    inference(unit_resulting_resolution,[],[f5226,f86])).

fof(f5281,plain,
    ( spl10_90
    | ~ spl10_84 ),
    inference(avatar_split_clause,[],[f5230,f5218,f5279])).

fof(f5279,plain,
    ( spl10_90
  <=> m1_subset_1(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f5230,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),sK0)
    | ~ spl10_84 ),
    inference(unit_resulting_resolution,[],[f5219,f87])).

fof(f5272,plain,
    ( ~ spl10_89
    | ~ spl10_84 ),
    inference(avatar_split_clause,[],[f5229,f5218,f5270])).

fof(f5229,plain,
    ( ~ r2_hidden(sK0,sK9(k1_relat_1(sK2),sK0,k1_xboole_0))
    | ~ spl10_84 ),
    inference(unit_resulting_resolution,[],[f5219,f86])).

fof(f5227,plain,
    ( spl10_86
    | ~ spl10_12
    | spl10_49 ),
    inference(avatar_split_clause,[],[f4769,f2143,f160,f5225])).

fof(f4769,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2),k1_xboole_0),sK0)
    | ~ spl10_12
    | ~ spl10_49 ),
    inference(unit_resulting_resolution,[],[f161,f2144,f686])).

fof(f5220,plain,
    ( spl10_84
    | ~ spl10_12
    | spl10_47 ),
    inference(avatar_split_clause,[],[f4717,f2104,f160,f5218])).

fof(f4717,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),sK0,k1_xboole_0),sK0)
    | ~ spl10_12
    | ~ spl10_47 ),
    inference(unit_resulting_resolution,[],[f161,f2105,f795])).

fof(f5135,plain,
    ( ~ spl10_83
    | spl10_47 ),
    inference(avatar_split_clause,[],[f4712,f2104,f5133])).

fof(f4712,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK5(k1_relat_1(sK2)))
    | ~ spl10_47 ),
    inference(unit_resulting_resolution,[],[f2105,f1337])).

fof(f1337,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,sK5(X11))
      | k3_xboole_0(X11,X12) = k1_xboole_0 ) ),
    inference(resolution,[],[f1320,f86])).

fof(f1320,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK5(X11),X11)
      | k3_xboole_0(X11,X12) = k1_xboole_0 ) ),
    inference(resolution,[],[f398,f241])).

fof(f398,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X6,k3_xboole_0(X5,X4))
      | r2_hidden(sK5(X5),X5) ) ),
    inference(superposition,[],[f387,f83])).

fof(f5035,plain,
    ( spl10_80
    | spl10_47 ),
    inference(avatar_split_clause,[],[f4711,f2104,f5033])).

fof(f4711,plain,
    ( r2_hidden(sK5(k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl10_47 ),
    inference(unit_resulting_resolution,[],[f2105,f1320])).

fof(f5002,plain,
    ( ~ spl10_79
    | spl10_29 ),
    inference(avatar_split_clause,[],[f4553,f514,f5000])).

fof(f4553,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK5(k1_relat_1(sK1)))
    | ~ spl10_29 ),
    inference(unit_resulting_resolution,[],[f515,f246])).

fof(f246,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK5(X4))
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f241,f86])).

fof(f4961,plain,
    ( spl10_76
    | spl10_29 ),
    inference(avatar_split_clause,[],[f4550,f514,f4959])).

fof(f4550,plain,
    ( r2_hidden(sK5(k1_relat_1(sK1)),k1_relat_1(sK1))
    | ~ spl10_29 ),
    inference(unit_resulting_resolution,[],[f515,f241])).

fof(f4756,plain,
    ( ~ spl10_75
    | spl10_47 ),
    inference(avatar_split_clause,[],[f4713,f2104,f4754])).

fof(f4713,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl10_47 ),
    inference(unit_resulting_resolution,[],[f2105,f1338])).

fof(f1338,plain,(
    ! [X14,X13] :
      ( ~ v1_xboole_0(X13)
      | k3_xboole_0(X13,X14) = k1_xboole_0 ) ),
    inference(resolution,[],[f1320,f93])).

fof(f4684,plain,
    ( spl10_66
    | spl10_65 ),
    inference(avatar_split_clause,[],[f4363,f4353,f4369])).

fof(f4369,plain,
    ( spl10_66
  <=> r2_hidden(sK5(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f4363,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl10_65 ),
    inference(unit_resulting_resolution,[],[f81,f4354,f85])).

fof(f4562,plain,
    ( ~ spl10_73
    | ~ spl10_12
    | spl10_29 ),
    inference(avatar_split_clause,[],[f4555,f514,f160,f4560])).

fof(f4555,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl10_12
    | ~ spl10_29 ),
    inference(unit_resulting_resolution,[],[f161,f515,f92])).

fof(f4543,plain,
    ( spl10_43
    | spl10_51
    | ~ spl10_54 ),
    inference(avatar_contradiction_clause,[],[f4542])).

fof(f4542,plain,
    ( $false
    | ~ spl10_43
    | ~ spl10_51
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f2158,f2290])).

fof(f2290,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | ~ spl10_43
    | ~ spl10_54 ),
    inference(resolution,[],[f2044,f2193])).

fof(f2193,plain,
    ( m1_subset_1(sK3(sK2,sK0,sK1),sK0)
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f2192])).

fof(f2192,plain,
    ( spl10_54
  <=> m1_subset_1(sK3(sK2,sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f2044,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r2_hidden(X0,sK0) )
    | ~ spl10_43 ),
    inference(resolution,[],[f2041,f85])).

fof(f2041,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f2040])).

fof(f2040,plain,
    ( spl10_43
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f4541,plain,
    ( spl10_65
    | spl10_67 ),
    inference(avatar_contradiction_clause,[],[f4540])).

fof(f4540,plain,
    ( $false
    | ~ spl10_65
    | ~ spl10_67 ),
    inference(subsumption_resolution,[],[f4367,f4363])).

fof(f4367,plain,
    ( ~ r2_hidden(sK5(sK2),sK2)
    | ~ spl10_67 ),
    inference(avatar_component_clause,[],[f4366])).

fof(f4366,plain,
    ( spl10_67
  <=> ~ r2_hidden(sK5(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).

fof(f4523,plain,
    ( ~ spl10_12
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(avatar_contradiction_clause,[],[f4522])).

fof(f4522,plain,
    ( $false
    | ~ spl10_12
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(subsumption_resolution,[],[f4521,f172])).

fof(f4521,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_xboole_0)
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(forward_demodulation,[],[f4498,f2147])).

fof(f2147,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK2)) = k1_xboole_0
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f2146])).

fof(f2146,plain,
    ( spl10_48
  <=> k3_xboole_0(sK0,k1_relat_1(sK2)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f4498,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(sK0,k1_relat_1(sK2)))
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(unit_resulting_resolution,[],[f2161,f4487,f108])).

fof(f4519,plain,
    ( ~ spl10_12
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(avatar_contradiction_clause,[],[f4518])).

fof(f4518,plain,
    ( $false
    | ~ spl10_12
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(subsumption_resolution,[],[f4517,f172])).

fof(f4517,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_xboole_0)
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(forward_demodulation,[],[f4516,f2147])).

fof(f4516,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(sK0,k1_relat_1(sK2)))
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(forward_demodulation,[],[f4500,f83])).

fof(f4500,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k3_xboole_0(k1_relat_1(sK2),sK0))
    | ~ spl10_50
    | ~ spl10_70 ),
    inference(unit_resulting_resolution,[],[f2161,f4487,f108])).

fof(f4488,plain,
    ( spl10_70
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f4308,f4302,f4486])).

fof(f4308,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),k1_relat_1(sK2))
    | ~ spl10_62 ),
    inference(unit_resulting_resolution,[],[f4303,f106])).

fof(f4397,plain,
    ( ~ spl10_69
    | ~ spl10_66 ),
    inference(avatar_split_clause,[],[f4373,f4369,f4395])).

fof(f4373,plain,
    ( ~ r2_hidden(sK2,sK5(sK2))
    | ~ spl10_66 ),
    inference(unit_resulting_resolution,[],[f4370,f86])).

fof(f4370,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl10_66 ),
    inference(avatar_component_clause,[],[f4369])).

fof(f4371,plain,
    ( spl10_66
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f4333,f4302,f4369])).

fof(f4333,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl10_62 ),
    inference(unit_resulting_resolution,[],[f4303,f397])).

fof(f4355,plain,
    ( ~ spl10_65
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f4312,f4302,f4353])).

fof(f4312,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_62 ),
    inference(unit_resulting_resolution,[],[f4303,f93])).

fof(f4304,plain,
    ( spl10_62
    | ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | ~ spl10_12
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f2081,f1607,f160,f150,f129,f115,f4302])).

fof(f1607,plain,
    ( spl10_38
  <=> k7_relat_1(sK1,k1_xboole_0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f2081,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,sK0,sK1),sK4(sK2,sK0,sK1)),sK2)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_38 ),
    inference(unit_resulting_resolution,[],[f130,f116,f151,f1859,f75])).

fof(f1859,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),sK1)
    | ~ spl10_0
    | ~ spl10_12
    | ~ spl10_38 ),
    inference(backward_demodulation,[],[f1608,f598])).

fof(f1608,plain,
    ( k7_relat_1(sK1,k1_xboole_0) = sK1
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f1607])).

fof(f3262,plain,
    ( ~ spl10_61
    | ~ spl10_4
    | spl10_53 ),
    inference(avatar_split_clause,[],[f3219,f2185,f129,f3260])).

fof(f3260,plain,
    ( spl10_61
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK3(sK2,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f3219,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK3(sK2,sK0,sK1))))
    | ~ spl10_4
    | ~ spl10_53 ),
    inference(unit_resulting_resolution,[],[f2198,f107])).

fof(f2198,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK2,sK3(sK2,sK0,sK1)))
    | ~ spl10_4
    | ~ spl10_53 ),
    inference(unit_resulting_resolution,[],[f130,f174,f2186,f102])).

fof(f2534,plain,
    ( spl10_58
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f2511,f1607,f160,f129,f115,f2532])).

fof(f2532,plain,
    ( spl10_58
  <=> k1_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f2511,plain,
    ( k1_relat_1(k1_relat_1(k7_relat_1(sK2,sK1))) = k1_xboole_0
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12
    | ~ spl10_38 ),
    inference(unit_resulting_resolution,[],[f172,f2495,f90])).

fof(f2495,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12
    | ~ spl10_38 ),
    inference(unit_resulting_resolution,[],[f1861,f107])).

fof(f1861,plain,
    ( ! [X2,X0,X1] : ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k7_relat_1(sK2,sK1))
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12
    | ~ spl10_38 ),
    inference(backward_demodulation,[],[f1608,f612])).

fof(f2399,plain,
    ( ~ spl10_57
    | ~ spl10_4
    | spl10_45 ),
    inference(avatar_split_clause,[],[f2383,f2066,f129,f2397])).

fof(f2397,plain,
    ( spl10_57
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f2383,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK5(sK0))))
    | ~ spl10_4
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f2069,f107])).

fof(f2069,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK2,sK5(sK0)))
    | ~ spl10_4
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f130,f174,f2067,f102])).

fof(f2194,plain,
    ( spl10_54
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f2165,f2160,f2192])).

fof(f2165,plain,
    ( m1_subset_1(sK3(sK2,sK0,sK1),sK0)
    | ~ spl10_50 ),
    inference(unit_resulting_resolution,[],[f2161,f87])).

fof(f2187,plain,
    ( ~ spl10_53
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f2164,f2160,f2185])).

fof(f2164,plain,
    ( ~ r2_hidden(sK0,sK3(sK2,sK0,sK1))
    | ~ spl10_50 ),
    inference(unit_resulting_resolution,[],[f2161,f86])).

fof(f2162,plain,
    ( spl10_50
    | ~ spl10_0
    | ~ spl10_4
    | spl10_11
    | ~ spl10_12
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f2083,f1607,f160,f150,f129,f115,f2160])).

fof(f2083,plain,
    ( r2_hidden(sK3(sK2,sK0,sK1),sK0)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_38 ),
    inference(unit_resulting_resolution,[],[f130,f116,f151,f1859,f74])).

fof(f2148,plain,
    ( spl10_48
    | ~ spl10_18
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f1843,f517,f204,f2146])).

fof(f1843,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK2)) = k1_xboole_0
    | ~ spl10_18
    | ~ spl10_28 ),
    inference(forward_demodulation,[],[f205,f518])).

fof(f518,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f517])).

fof(f2113,plain,
    ( spl10_30
    | ~ spl10_36
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f1902,f1607,f1595,f592])).

fof(f592,plain,
    ( spl10_30
  <=> k7_relat_1(sK2,k1_xboole_0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f1595,plain,
    ( spl10_36
  <=> k7_relat_1(sK1,k1_xboole_0) = k7_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f1902,plain,
    ( k7_relat_1(sK2,k1_xboole_0) = sK1
    | ~ spl10_36
    | ~ spl10_38 ),
    inference(backward_demodulation,[],[f1608,f1596])).

fof(f1596,plain,
    ( k7_relat_1(sK1,k1_xboole_0) = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f1595])).

fof(f2109,plain,
    ( spl10_46
    | ~ spl10_16
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f1816,f517,f183,f2107])).

fof(f2107,plain,
    ( spl10_46
  <=> k3_xboole_0(k1_relat_1(sK2),sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f1816,plain,
    ( k3_xboole_0(k1_relat_1(sK2),sK0) = k1_xboole_0
    | ~ spl10_16
    | ~ spl10_28 ),
    inference(forward_demodulation,[],[f184,f518])).

fof(f2068,plain,
    ( ~ spl10_45
    | spl10_27 ),
    inference(avatar_split_clause,[],[f2031,f507,f2066])).

fof(f507,plain,
    ( spl10_27
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f2031,plain,
    ( ~ r2_hidden(sK0,sK5(sK0))
    | ~ spl10_27 ),
    inference(unit_resulting_resolution,[],[f508,f246])).

fof(f508,plain,
    ( k1_xboole_0 != sK0
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f507])).

fof(f2042,plain,
    ( ~ spl10_43
    | ~ spl10_12
    | spl10_27 ),
    inference(avatar_split_clause,[],[f2035,f507,f160,f2040])).

fof(f2035,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl10_12
    | ~ spl10_27 ),
    inference(unit_resulting_resolution,[],[f161,f508,f92])).

fof(f1810,plain,
    ( ~ spl10_12
    | ~ spl10_28
    | ~ spl10_40 ),
    inference(avatar_contradiction_clause,[],[f1809])).

fof(f1809,plain,
    ( $false
    | ~ spl10_12
    | ~ spl10_28
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f1808,f172])).

fof(f1808,plain,
    ( r2_hidden(sK3(sK2,k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl10_28
    | ~ spl10_40 ),
    inference(forward_demodulation,[],[f1788,f518])).

fof(f1788,plain,
    ( r2_hidden(sK3(sK2,k1_xboole_0,sK1),k1_relat_1(sK1))
    | ~ spl10_40 ),
    inference(resolution,[],[f1770,f106])).

fof(f1799,plain,
    ( ~ spl10_12
    | ~ spl10_28
    | ~ spl10_40 ),
    inference(avatar_contradiction_clause,[],[f1798])).

fof(f1798,plain,
    ( $false
    | ~ spl10_12
    | ~ spl10_28
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f1797,f172])).

fof(f1797,plain,
    ( r2_hidden(sK3(sK2,k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl10_28
    | ~ spl10_40 ),
    inference(forward_demodulation,[],[f1774,f518])).

fof(f1774,plain,
    ( r2_hidden(sK3(sK2,k1_xboole_0,sK1),k1_relat_1(sK1))
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f1770,f106])).

fof(f1771,plain,
    ( spl10_40
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12
    | spl10_31 ),
    inference(avatar_split_clause,[],[f1372,f595,f160,f129,f115,f1769])).

fof(f595,plain,
    ( spl10_31
  <=> k7_relat_1(sK2,k1_xboole_0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f1372,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k1_xboole_0,sK1),sK4(sK2,k1_xboole_0,sK1)),sK1)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12
    | ~ spl10_31 ),
    inference(unit_resulting_resolution,[],[f130,f116,f596,f172,f74])).

fof(f596,plain,
    ( k7_relat_1(sK2,k1_xboole_0) != sK1
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f595])).

fof(f1612,plain,
    ( ~ spl10_39
    | spl10_31
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f1598,f1595,f595,f1610])).

fof(f1610,plain,
    ( spl10_39
  <=> k7_relat_1(sK1,k1_xboole_0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f1598,plain,
    ( k7_relat_1(sK1,k1_xboole_0) != sK1
    | ~ spl10_31
    | ~ spl10_36 ),
    inference(superposition,[],[f596,f1596])).

fof(f1597,plain,
    ( spl10_36
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f1498,f160,f129,f115,f1595])).

fof(f1498,plain,
    ( k7_relat_1(sK1,k1_xboole_0) = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(backward_demodulation,[],[f1423,f1424])).

fof(f1424,plain,
    ( ! [X0] : k7_relat_1(sK2,k1_xboole_0) = k7_relat_1(k7_relat_1(sK2,k1_xboole_0),X0)
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f130,f176,f172,f1235,f74])).

fof(f1235,plain,
    ( ! [X2,X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(k7_relat_1(sK2,k1_xboole_0),X2))
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f174,f176,f599,f101])).

fof(f101,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f599,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(sK2,k1_xboole_0))
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f172,f130,f174,f102])).

fof(f176,plain,
    ( ! [X0,X1] : v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f174,f84])).

fof(f1423,plain,
    ( ! [X0] : k7_relat_1(sK1,k1_xboole_0) = k7_relat_1(k7_relat_1(sK2,k1_xboole_0),X0)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f116,f176,f172,f1235,f74])).

fof(f774,plain,
    ( spl10_34
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f737,f160,f129,f772])).

fof(f772,plain,
    ( spl10_34
  <=> k1_relat_1(k7_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f737,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(backward_demodulation,[],[f731,f732])).

fof(f732,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,k1_xboole_0)) = k3_xboole_0(k1_relat_1(k7_relat_1(sK2,k1_xboole_0)),X0)
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f695,f695,f97])).

fof(f695,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,k1_xboole_0)))
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f599,f107])).

fof(f731,plain,
    ( ! [X0] : k3_xboole_0(k1_relat_1(k7_relat_1(sK2,k1_xboole_0)),X0) = k1_xboole_0
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f172,f695,f97])).

fof(f678,plain,
    ( spl10_32
    | ~ spl10_0
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f642,f160,f115,f676])).

fof(f676,plain,
    ( spl10_32
  <=> k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f642,plain,
    ( k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) = k1_xboole_0
    | ~ spl10_0
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f610,f241])).

fof(f610,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,k1_xboole_0)))
    | ~ spl10_0
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f598,f107])).

fof(f597,plain,
    ( ~ spl10_31
    | spl10_11
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f581,f510,f150,f595])).

fof(f510,plain,
    ( spl10_26
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f581,plain,
    ( k7_relat_1(sK2,k1_xboole_0) != sK1
    | ~ spl10_11
    | ~ spl10_26 ),
    inference(forward_demodulation,[],[f151,f511])).

fof(f511,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f510])).

fof(f589,plain,
    ( spl10_28
    | ~ spl10_18
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f538,f510,f204,f517])).

fof(f538,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | ~ spl10_18
    | ~ spl10_26 ),
    inference(forward_demodulation,[],[f537,f186])).

fof(f186,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[],[f83,f69])).

fof(f537,plain,
    ( k1_relat_1(sK1) = k3_xboole_0(k1_xboole_0,k1_relat_1(sK2))
    | ~ spl10_18
    | ~ spl10_26 ),
    inference(forward_demodulation,[],[f205,f511])).

fof(f586,plain,
    ( ~ spl10_12
    | ~ spl10_22
    | ~ spl10_26 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | ~ spl10_12
    | ~ spl10_22
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f584,f172])).

fof(f584,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl10_22
    | ~ spl10_26 ),
    inference(forward_demodulation,[],[f413,f511])).

fof(f413,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl10_22
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f583,plain,
    ( ~ spl10_18
    | ~ spl10_26
    | spl10_29 ),
    inference(avatar_contradiction_clause,[],[f582])).

fof(f582,plain,
    ( $false
    | ~ spl10_18
    | ~ spl10_26
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f515,f538])).

fof(f519,plain,
    ( spl10_28
    | ~ spl10_16
    | spl10_23 ),
    inference(avatar_split_clause,[],[f448,f409,f183,f517])).

fof(f409,plain,
    ( spl10_23
  <=> ~ r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f448,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | ~ spl10_16
    | ~ spl10_23 ),
    inference(forward_demodulation,[],[f431,f69])).

fof(f431,plain,
    ( k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl10_16
    | ~ spl10_23 ),
    inference(backward_demodulation,[],[f423,f184])).

fof(f423,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_23 ),
    inference(unit_resulting_resolution,[],[f81,f410,f209])).

fof(f410,plain,
    ( ~ r2_hidden(sK5(sK0),sK0)
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f409])).

fof(f512,plain,
    ( spl10_26
    | spl10_23 ),
    inference(avatar_split_clause,[],[f423,f409,f510])).

fof(f417,plain,
    ( spl10_22
    | spl10_24
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f400,f183,f415,f412])).

fof(f400,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,k1_relat_1(sK1))
        | r2_hidden(sK5(sK0),sK0) )
    | ~ spl10_16 ),
    inference(superposition,[],[f387,f184])).

fof(f318,plain,
    ( spl10_20
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f295,f160,f316])).

fof(f316,plain,
    ( spl10_20
  <=> k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f295,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f286,f241])).

fof(f286,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f172,f107])).

fof(f206,plain,
    ( spl10_18
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f187,f183,f204])).

fof(f187,plain,
    ( k1_relat_1(sK1) = k3_xboole_0(sK0,k1_relat_1(sK2))
    | ~ spl10_16 ),
    inference(superposition,[],[f83,f184])).

fof(f185,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f65,f183])).

fof(f65,plain,(
    k1_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f171,plain,
    ( spl10_14
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f153,f143,f169])).

fof(f169,plain,
    ( spl10_14
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f143,plain,
    ( spl10_8
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f153,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f144,f70])).

fof(f144,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f162,plain,
    ( spl10_12
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f155,f143,f160])).

fof(f155,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_8 ),
    inference(backward_demodulation,[],[f153,f144])).

fof(f152,plain,(
    ~ spl10_11 ),
    inference(avatar_split_clause,[],[f67,f150])).

fof(f67,plain,(
    k7_relat_1(sK2,sK0) != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f145,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f68,f143])).

fof(f68,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t68_funct_1.p',dt_o_0_0_xboole_0)).

fof(f138,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f64,f136])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f131,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f63,f129])).

fof(f63,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f124,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f62,f122])).

fof(f62,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f117,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f61,f115])).

fof(f61,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
